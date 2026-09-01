unit RateLaw.Types;

{ Core types for the rate law checker: what a model looks like to the engine,
  and what the engine says about it.

  RTL-only, and deliberately so. Nothing in this library may reference FMX,
  libantimony or libRoadRunner -- that constraint is what lets the same engine
  be driven by Iridium, by this project's own console harness, and later by a
  bifurcation tool or a batch checker. The model arrives through IModelSource
  and nothing else.

  The naming here is defensive in one place. Diagnostics are TRateLawDiagnostic
  rather than the obvious TDiagnostic, because Iridium already uses a
  TDiagnosticList from Sim.Meta.Types in the same units that will use this one.
  Two same-named types in different units do not clash at compile time -- the
  later 'uses' entry silently wins -- so the bug would be a report quietly
  built from the wrong record. Distinct names cost a few characters and remove
  the possibility. }

interface

uses
  System.SysUtils, System.Classes, System.Generics.Collections;

type
  TSeverity = (sevInfo, sevWarn, sevError);

  { What a symbol is, as far as the checker cares. skUnknown covers both 'the
    model has never heard of this name' and 'the model source could not say',
    which the caller must not conflate: the first is defect S014, the second is
    a check that could not be performed. IModelSource.KnowsSymbolKinds
    distinguishes them once, rather than at every call site. }
  TSymbolKind = (skUnknown, skSpecies, skParameter, skCompartment);

  { Antimony states modifier roles explicitly through its interaction arrows:
    -o activates, -| inhibits, -( is generic. mrUnspecified means the species
    appears in the rate law but no interaction was declared for it -- a real
    and common case, and one worth reporting once inhibition laws are
    registered, since a role established by position alone is exactly what
    S007 exists to catch. }
  TModifierRole = (mrUnspecified, mrActivator, mrInhibitor, mrGeneric);

  { A reactant or product, with its stoichiometry.

    Stoichiometry is carried twice on purpose. A model may write it as a
    symbol ('S1 + n S2 => S3; n = 2*p1'), in which case there is no number to
    have -- Value is NaN and Text holds the symbol's name. Generative laws
    (mass action of arbitrary order) instantiate their exponents from this, so
    dropping the symbolic form would silently turn 'n' into 'not a number'. }
  TSpeciesRef = record
    Name:  string;
    Value: Double;   // NaN when the stoichiometry was written as a symbol
    Text:  string;   // as written: a number's text, or the symbol's name
    function IsSymbolic: Boolean;
    class function Make(const AName: string; AValue: Double;
                        const AText: string = ''): TSpeciesRef; static;
  end;

  TModifierRef = record
    Name: string;
    Role: TModifierRole;
    class function Make(const AName: string; ARole: TModifierRole): TModifierRef; static;
  end;

  TSpeciesRefs  = TArray<TSpeciesRef>;
  TModifierRefs = TArray<TModifierRef>;

  { ------------------------------------------------------------------------
    The model, as the engine sees it.

    Every method must be safe to call on a model that does not simulate and on
    one that is only half-sensible -- a malformed rate law is exactly the case
    the checker exists for, so refusing to describe a broken model defeats the
    purpose. Implementations report 'I cannot say' rather than raising:
    an out-of-range index returns empty, not an exception.
    ------------------------------------------------------------------------ }
  IModelSource = interface
    ['{9E2C1A44-5F3B-4E7A-9C21-6B8D0F4A7E11}']

    { Reactions. Indices are 0 .. ReactionCount-1. }
    function ReactionCount: Integer;
    function ReactionId   (AIndex: Integer): string;
    function RateLawText  (AIndex: Integer): string;
    function Reactants    (AIndex: Integer): TSpeciesRefs;
    function Products     (AIndex: Integer): TSpeciesRefs;
    function Modifiers    (AIndex: Integer): TModifierRefs;

    { Symbols. }
    function SymbolKind    (const AName: string): TSymbolKind;
    { False when the symbol was declared with no value at all. This is the
      only way to tell that case apart from a value of zero, since both leave
      the equation empty -- and it is the whole of defect S014. }
    function HasValue      (const AName: string): Boolean;
    function ValueOf       (const AName: string): Double;
    { '' when the symbol has no assignment rule. }
    function AssignmentRule(const AName: string): string;

    { True when the symbol's value is held fixed -- an SBML boundary species,
      an Antimony const species, a constant parameter or compartment.

      This exists for one check and earns its place there. S017 reports a
      reactant that does not appear in its own rate law, on the reasoning that
      a reaction consuming something ought to depend on how much of it there
      is. A species held constant is the standing exception: clamping it is
      precisely a statement that the kinetics do not vary with it, and leaving
      it out of the rate law is then correct. Over the BioModels corpus 78% of
      S017 findings were on boundary species -- all of them false.

      A source that cannot tell returns False, which keeps the old behaviour
      rather than silently exempting everything. }
    function IsConstant(const AName: string): Boolean;

    { User-defined functions. A rate law may be written as a call to one
      ('function MM(s,v,k) v*s/(k+s) end' then 'J1: S -> P; MM(S,Vm,Km)'), in
      which case comparing it structurally against a canonical form fails for
      a reason that has nothing to do with the model being wrong. The
      canonicaliser inlines through this. }
    function UserFunction  (const AName: string;
                            out AArgs: TArray<string>;
                            out ABody: string): Boolean;

    { True when SymbolKind's answers are trustworthy. A source that cannot
      classify symbols returns False here and skUnknown throughout, and the
      checks that depend on classification report themselves as not performed
      rather than as passed. }
    function KnowsSymbolKinds: Boolean;

    { The law id the modeller declared for this reaction, or '' if none.

      An annotation is the only evidence that can say "you meant Michaelis-
      Menten and wrote something else entirely". Inference can only ever say
      "this resembles nothing registered", which is a much weaker statement
      and is silent about the case that matters most. }
    function AnnotatedLaw(AIndex: Integer): string;

    { 1-based source line of a reaction, or -1 when unknown. For the UI only:
      nothing in the engine reads it, but it is what lets a report navigate to
      the offending reaction, so it belongs here from the start. }
    function SourceLineOf(AIndex: Integer): Integer;
  end;

  { ------------------------------------------------------------------------
    Diagnostics
    ------------------------------------------------------------------------ }

  TRateLawDiagnostic = record
    Code:       string;    // 'S004'
    Severity:   TSeverity;
    LawId:      string;    // '' when unassociated
    ReactionId: string;
    SourceLine: Integer;   // -1 when unknown
    Message:    string;
    Found:      string;    // the offending subexpression
    Expected:   string;    // the canonical subexpression
    Suggestion: string;    // '' when no unambiguous fix exists
    { The witness: the parameter and concentration values at which a dynamic
      property failed. Mandatory for every dynamic finding -- one without a
      reproducible witness cannot be told apart from a bug in the checker. }
    Evidence:   string;
    function ToString: string;
  end;

  TRateLawDiagnostics = class(TList<TRateLawDiagnostic>)
  public
    procedure Add(const ACode: string; ASeverity: TSeverity;
                  const AReactionId, AMessage: string); overload;
    function  CountOf(ASeverity: TSeverity): Integer;
    function  HasCode(const ACode: string): Boolean;
    { Codes present, sorted and de-duplicated. The corpus compares these
      rather than message text, so the tests stay stable while the wording is
      still being improved. }
    function  Codes: TArray<string>;
  end;

  { How a reaction was matched to a law, recorded per reaction so a report can
    say what was checked as well as what failed. 'Nothing was checked' and
    'nothing was wrong' must never look alike. }
  TAssociationKind = (akNone, akAnnotated, akInferred, akAmbiguous);

  TAssociation = record
    ReactionId: string;
    LawId:      string;
    Kind:       TAssociationKind;
    Detail:     string;   // why, for the report
  end;

  TCheckResult = class
  private
    FDiagnostics:  TRateLawDiagnostics;
    FAssociations: TList<TAssociation>;
    FLawsApplied:  TStringList;
    function GetErrorCount: Integer;
    function GetWarningCount: Integer;
  public
    constructor Create;
    destructor  Destroy; override;
    property Diagnostics:  TRateLawDiagnostics  read FDiagnostics;
    property Associations: TList<TAssociation>  read FAssociations;
    { Ids of the laws that actually participated. Empty with no diagnostics
      means the registry was empty or everything was disabled -- a very
      different report from a clean model. }
    property LawsApplied:  TStringList          read FLawsApplied;
    property ErrorCount:   Integer              read GetErrorCount;
    property WarningCount: Integer              read GetWarningCount;
  end;

function SeverityName(ASeverity: TSeverity): string;
function ModifierRoleName(ARole: TModifierRole): string;
{ True for a name the language defines rather than the model: SBML's time
  symbol and the mathematical constants.

  They are identifiers in the expression like any other, and nothing knew
  they were special. So a rate law that legitimately mentions "time" or "pi"
  was reported as referring to a symbol the model does not define -- 113 of
  the 147 S014 findings over the BioModels corpus, all wrong -- and both were
  offered to the binder as candidate parameters, where "pi" could be chosen
  to play a Km. }
{ Antimony writes a synthesis reaction as "-> P" and a degradation as
  "S ->", and names the absent side EmptySet. It is notation for NOTHING; it
  is not a species, it has no concentration, and no rate law mentions it.

  Nothing knew that. So mass action instantiated over a reactant list of
  [EmptySet] and produced "k*EmptySet", against which every real synthesis
  rate law looked like a substrate swap: "M appears where EmptySet was
  expected", 269 times over the BioModels corpus and the single largest
  source of errors left after the association work. }
function IsNullSpecies(const AName: string): Boolean;

function IsBuiltInSymbol(const AName: string): Boolean;

function SymbolKindName(AKind: TSymbolKind): string;

implementation

uses
  System.Math, System.Generics.Defaults;

{ ---------------------------------------------------------------- TSpeciesRef }

function TSpeciesRef.IsSymbolic: Boolean;
begin
  Result := IsNan(Value);
end;

class function TSpeciesRef.Make(const AName: string; AValue: Double;
  const AText: string): TSpeciesRef;
begin
  Result.Name  := AName;
  Result.Value := AValue;
  if AText <> '' then
    Result.Text := AText
  else if IsNan(AValue) then
    Result.Text := ''
  else
    Result.Text := FloatToStr(AValue);
end;

{ --------------------------------------------------------------- TModifierRef }

class function TModifierRef.Make(const AName: string;
  ARole: TModifierRole): TModifierRef;
begin
  Result.Name := AName;
  Result.Role := ARole;
end;

{ --------------------------------------------------------- TRateLawDiagnostic }

function TRateLawDiagnostic.ToString: string;
begin
  Result := Format('%-5s %-5s', [Code, SeverityName(Severity)]);
  if ReactionId <> '' then
    Result := Result + '  ' + ReactionId;
  if LawId <> '' then
    Result := Result + ' (' + LawId + ')';
  Result := Result + '  ' + Message;
  { The label column is 12 wide so the values line up. "try" and "at" were
    each short enough to fit and too short to be understood: "try" reads as an
    instruction, which is wrong for a suggestion phrased as a condition, and
    "at" said nothing at all about what the numbers after it were. }
  if Found <> '' then
    Result := Result + sLineBreak + '        found:      ' + Found;
  if Expected <> '' then
    Result := Result + sLineBreak + '        expected:   ' + Expected;
  if Suggestion <> '' then
    Result := Result + sLineBreak + '        suggestion: ' + Suggestion;
  if Evidence <> '' then
    Result := Result + sLineBreak + '        seen at:    ' + Evidence;
end;

{ -------------------------------------------------------- TRateLawDiagnostics }

procedure TRateLawDiagnostics.Add(const ACode: string; ASeverity: TSeverity;
  const AReactionId, AMessage: string);
var
  D: TRateLawDiagnostic;
begin
  D := Default(TRateLawDiagnostic);
  D.Code       := ACode;
  D.Severity   := ASeverity;
  D.ReactionId := AReactionId;
  D.Message    := AMessage;
  D.SourceLine := -1;
  inherited Add(D);
end;

function TRateLawDiagnostics.CountOf(ASeverity: TSeverity): Integer;
var
  D: TRateLawDiagnostic;
begin
  Result := 0;
  for D in Self do
    if D.Severity = ASeverity then
      Inc(Result);
end;

function TRateLawDiagnostics.HasCode(const ACode: string): Boolean;
var
  D: TRateLawDiagnostic;
begin
  for D in Self do
    if SameText(D.Code, ACode) then
      Exit(True);
  Result := False;
end;

function TRateLawDiagnostics.Codes: TArray<string>;
var
  L: TStringList;
  I: Integer;
  D: TRateLawDiagnostic;
begin
  L := TStringList.Create;
  try
    L.Sorted     := True;
    L.Duplicates := dupIgnore;
    for D in Self do
      L.Add(D.Code);
    SetLength(Result, L.Count);
    for I := 0 to L.Count - 1 do
      Result[I] := L[I];
  finally
    L.Free;
  end;
end;

{ -------------------------------------------------------------- TCheckResult }

constructor TCheckResult.Create;
begin
  inherited Create;
  FDiagnostics  := TRateLawDiagnostics.Create;
  FAssociations := TList<TAssociation>.Create;
  FLawsApplied  := TStringList.Create;
  FLawsApplied.Sorted     := True;
  FLawsApplied.Duplicates := dupIgnore;
end;

destructor TCheckResult.Destroy;
begin
  FLawsApplied.Free;
  FAssociations.Free;
  FDiagnostics.Free;
  inherited;
end;

function TCheckResult.GetErrorCount: Integer;
begin
  Result := FDiagnostics.CountOf(sevError);
end;

function TCheckResult.GetWarningCount: Integer;
begin
  Result := FDiagnostics.CountOf(sevWarn);
end;

{ ------------------------------------------------------------------- helpers }

function SeverityName(ASeverity: TSeverity): string;
begin
  case ASeverity of
    sevInfo:  Result := 'INFO';
    sevWarn:  Result := 'WARN';
  else        Result := 'ERROR';
  end;
end;

function ModifierRoleName(ARole: TModifierRole): string;
begin
  case ARole of
    mrActivator: Result := 'activator';
    mrInhibitor: Result := 'inhibitor';
    mrGeneric:   Result := 'interaction';
  else           Result := 'unspecified';
  end;
end;

function IsNullSpecies(const AName: string): Boolean;
begin
  Result := SameText(Trim(AName), 'EmptySet');
end;

function IsBuiltInSymbol(const AName: string): Boolean;
const
  { 'time' is SBML's; the rest are the constants Antimony and libSBML both
    accept. Case-insensitive, because SBML writes 'exponentiale' and a
    modeller writes 'e'. }
  BuiltIns: array [0 .. 8] of string = (
    'time', 'pi', 'avogadro', 'exponentiale', 'inf', 'infinity', 'nan',
    'true', 'false');
var
  I: Integer;
begin
  for I := Low(BuiltIns) to High(BuiltIns) do
    if SameText(AName, BuiltIns[I]) then Exit(True);
  Result := False;
end;

function SymbolKindName(AKind: TSymbolKind): string;
begin
  case AKind of
    skSpecies:     Result := 'species';
    skParameter:   Result := 'parameter';
    skCompartment: Result := 'compartment';
  else             Result := 'unknown';
  end;
end;

end.
