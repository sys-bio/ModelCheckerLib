unit RateLaw.TestCorpus;

{ A fixture model source, and the corpus that drives it.

  The fixture is the whole reason the engine is a separate project. It builds
  an IModelSource out of literal data, so a test case is a few lines of readable
  declaration rather than a model file that has to survive a round trip through
  libantimony -- and so the corpus runs with no DLL, no Iridium and no GUI.

  Cases compare diagnostic *codes*, not message text, so wording can keep
  improving without breaking tests. Extra codes not listed fail the case, so a
  rule cannot quietly gain a diagnostic without someone noticing.

  The founding case is Vm*S/(Km + Km): a rate law that parses, simulates, and is
  wrong. Everything here exists to catch that class of defect. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Types, RateLaw.Bind, RateLaw.Registry;

type
  { One reaction, as declared by a test case. }
  TFixtureReaction = record
    Id:        string;
    RateLaw:   string;
    Reactants: TSpeciesRefs;
    Products:  TSpeciesRefs;
    Modifiers: TModifierRefs;
    Annotation: string;
    Line:      Integer;
  end;

  TFixtureSymbol = record
    Name:      string;
    Kind:      TSymbolKind;
    Value:     Double;
    HasValue:  Boolean;
    Assignment: string;
    Constant:  Boolean;
  end;

  TFixtureFunction = record
    Name: string;
    Args: TArray<string>;
    Body: string;
  end;

  { A hand-built IModelSource.

    Deliberately permissive: an out-of-range reaction index returns empty
    rather than raising, matching the contract in RateLaw.Types. The engine
    will be pointed at broken models by design, and a fixture that is stricter
    than the real thing would hide that. }
  TFixtureModel = class(TInterfacedObject, IModelSource)
  private
    FReactions: TList<TFixtureReaction>;
    FSymbols:   TList<TFixtureSymbol>;
    FFunctions: TList<TFixtureFunction>;
    FKnowsKinds: Boolean;
    function IndexOfSymbol(const AName: string): Integer;
    function InRange(AIndex: Integer): Boolean;
  public
    constructor Create;
    destructor  Destroy; override;

    { Fluent builders -- each returns Self so a case reads as one statement. }
    function Reaction(const AId, ARateLaw: string): TFixtureModel;
    function Reactant(const AName: string; AStoich: Double = 1): TFixtureModel;
    function SymbolicReactant(const AName, AStoichSymbol: string): TFixtureModel;
    function Product (const AName: string; AStoich: Double = 1): TFixtureModel;
    function Modifier(const AName: string; ARole: TModifierRole): TFixtureModel;
    { Declares the law the modeller says this reaction follows. }
    function Annotate(const ALawId: string): TFixtureModel;
    function Param   (const AName: string; AValue: Double): TFixtureModel;
    { A parameter declared with no value at all -- the S014 case. Distinct
      from a value of zero, which is why HasValue exists. }
    function UnsetParam(const AName: string): TFixtureModel;
    function Species (const AName: string; AValue: Double): TFixtureModel;
    { A species whose value is held fixed -- SBML's boundaryCondition, and the
      exemption S017 has to honour. }
    function ConstSpecies(const AName: string; AValue: Double): TFixtureModel;
    function Compartment(const AName: string; AValue: Double): TFixtureModel;
    function Assigned_(const AName, AExpr: string): TFixtureModel;
    function Func(const AName: string; const AArgs: TArray<string>;
                  const ABody: string): TFixtureModel;
    { Turns off symbol classification, to exercise the 'could not say' path. }
    function WithoutSymbolKinds: TFixtureModel;

    { IModelSource }
    function ReactionCount: Integer;
    function ReactionId   (AIndex: Integer): string;
    function RateLawText  (AIndex: Integer): string;
    function Reactants    (AIndex: Integer): TSpeciesRefs;
    function Products     (AIndex: Integer): TSpeciesRefs;
    function Modifiers    (AIndex: Integer): TModifierRefs;
    function SymbolKind   (const AName: string): TSymbolKind;
    function HasValue     (const AName: string): Boolean;
    function ValueOf      (const AName: string): Double;
    function AssignmentRule(const AName: string): string;
    function IsConstant   (const AName: string): Boolean;
    function UserFunction (const AName: string; out AArgs: TArray<string>;
                           out ABody: string): Boolean;
    function KnowsSymbolKinds: Boolean;
    function AnnotatedLaw (AIndex: Integer): string;
    function SourceLineOf (AIndex: Integer): Integer;
  end;

  TRateLawTestCase = record
    Name:   string;
    Build:  TFunc<TFixtureModel>;
    /// Run the behavioural checks as well. Off by default: most cases are
    /// about structure, and probing every one of them would make the corpus
    /// slow for no gain.
    Dynamic: Boolean;
    /// Extra registry entries for this case only. Some behaviour depends on
    /// what else is registered -- ambiguity most of all -- and a single fixed
    /// registry cannot express that.
    ExtraLaws: TArray<string>;
    /// Codes that must appear. Order is not compared; extra codes fail.
    Expect: TArray<string>;
    /// Why this case is in the corpus. Printed on failure, so a broken test
    /// explains what it was protecting rather than only what it wanted.
    Why:    string;
  end;

  { A pair of expressions, with the reason the pair is in the corpus. }
  TExprPair = record
    A, B: string;
    Why:  string;
  end;

function Corpus: TArray<TRateLawTestCase>;

{ Pairs that MUST canonicalise to the same tree. These are the false-positive
  guard for the canonicaliser: every one is a stylistic variation a modeller
  might plausibly write, and any that fails to normalise becomes a spurious
  structural difference in every reaction written that way. }
function EquivalentPairs: TArray<TExprPair>;

{ Pairs that MUST NOT canonicalise to the same tree. These matter more than
  the equivalent ones: each is a near-miss that an over-aggressive
  canonicaliser would erase, taking a real defect with it. }
function DistinctPairs: TArray<TExprPair>;

{ Expressions that must be rejected by the parser rather than quietly
  producing some tree. }
function MalformedExpressions: TArray<string>;

  { A registry entry that must be rejected, and the code that must reject it.
    Every one is an authoring mistake someone will actually make -- which is
    the point of rejecting at load: a bad entry produces false positives on
    every model checked afterwards, and the user cannot tell it is the tool
    that is wrong rather than their model. }
type
  TBadLawCase = record
    Name: string;
    Json: string;
    Code: string;
    Why:  string;
  end;

function BadLawEntries: TArray<TBadLawCase>;

  { A role-binding case: one reaction, one law, and what the binder must make
    of it. Expect is written in the law's own role order, so a transposition
    shows up as a plainly different string rather than a subtle one. }
type
  TBindCase = record
    Name:       string;
    LawId:      string;
    Build:      TFunc<TFixtureModel>;
    Outcome:    TBindOutcome;
    Expect:     TArray<string>;   // 'S=A', 'Vm=k1', ...
    Suspicious: Boolean;          // the binder must smell a role swap
    Why:        string;
  end;

function BindCases: TArray<TBindCase>;

{ A correct irreversible Michaelis-Menten model -- the baseline every mutation
  case is derived from, and the false-positive corpus's first entry. }
function CorrectMM: TFixtureModel;

{ A model built FROM a law: one reaction whose structure is whatever the law's
  own roles say it should be, carrying ARateLaw as its kinetic law.

  This is what lets the mutation harness run over the whole registry instead
  of a hand-written list. A hand-written fixture per law is a fixture that has
  to be written before a law can be measured, which in practice means laws get
  added and never measured. Deriving the reaction from the roles means a new
  registry entry is covered the moment it exists.

  Pass '' for ARateLaw to use the law's own expression -- the correct form,
  which is the false-positive baseline every mutation is compared against. }
function ModelForLaw(ALaw: TRateLawDef;
                     const ARateLaw: string = ''): TFixtureModel;

/// Renders a model through IModelSource alone, which is how M1 proves the
/// interface carries everything the engine will need.
function DescribeModel(const AModel: IModelSource): string;

implementation

{ ------------------------------------------------------------- TFixtureModel }

constructor TFixtureModel.Create;
begin
  inherited Create;
  FReactions  := TList<TFixtureReaction>.Create;
  FSymbols    := TList<TFixtureSymbol>.Create;
  FFunctions  := TList<TFixtureFunction>.Create;
  FKnowsKinds := True;
end;

destructor TFixtureModel.Destroy;
begin
  FFunctions.Free;
  FSymbols.Free;
  FReactions.Free;
  inherited;
end;

function TFixtureModel.InRange(AIndex: Integer): Boolean;
begin
  Result := (AIndex >= 0) and (AIndex < FReactions.Count);
end;

function TFixtureModel.IndexOfSymbol(const AName: string): Integer;
var
  I: Integer;
begin
  for I := 0 to FSymbols.Count - 1 do
    if SameText(FSymbols[I].Name, AName) then
      Exit(I);
  Result := -1;
end;

function TFixtureModel.Reaction(const AId, ARateLaw: string): TFixtureModel;
var
  R: TFixtureReaction;
begin
  R := Default(TFixtureReaction);
  R.Id      := AId;
  R.RateLaw := ARateLaw;
  R.Line    := FReactions.Count + 1;
  FReactions.Add(R);
  Result := Self;
end;

function TFixtureModel.Reactant(const AName: string; AStoich: Double): TFixtureModel;
var
  R: TFixtureReaction;
begin
  Result := Self;
  if FReactions.Count = 0 then Exit;
  R := FReactions.Last;
  R.Reactants := R.Reactants + [TSpeciesRef.Make(AName, AStoich)];
  FReactions[FReactions.Count - 1] := R;
end;

function TFixtureModel.SymbolicReactant(const AName, AStoichSymbol: string): TFixtureModel;
var
  R: TFixtureReaction;
begin
  Result := Self;
  if FReactions.Count = 0 then Exit;
  R := FReactions.Last;
  R.Reactants := R.Reactants + [TSpeciesRef.Make(AName, NaN, AStoichSymbol)];
  FReactions[FReactions.Count - 1] := R;
end;

function TFixtureModel.Product(const AName: string; AStoich: Double): TFixtureModel;
var
  R: TFixtureReaction;
begin
  Result := Self;
  if FReactions.Count = 0 then Exit;
  R := FReactions.Last;
  R.Products := R.Products + [TSpeciesRef.Make(AName, AStoich)];
  FReactions[FReactions.Count - 1] := R;
end;

function TFixtureModel.Modifier(const AName: string; ARole: TModifierRole): TFixtureModel;
var
  R: TFixtureReaction;
begin
  Result := Self;
  if FReactions.Count = 0 then Exit;
  R := FReactions.Last;
  R.Modifiers := R.Modifiers + [TModifierRef.Make(AName, ARole)];
  FReactions[FReactions.Count - 1] := R;
end;

function TFixtureModel.Param(const AName: string; AValue: Double): TFixtureModel;
var
  S: TFixtureSymbol;
begin
  S := Default(TFixtureSymbol);
  S.Name := AName; S.Kind := skParameter; S.Value := AValue; S.HasValue := True;
  FSymbols.Add(S);
  Result := Self;
end;

function TFixtureModel.UnsetParam(const AName: string): TFixtureModel;
var
  S: TFixtureSymbol;
begin
  S := Default(TFixtureSymbol);
  S.Name := AName; S.Kind := skParameter; S.Value := NaN; S.HasValue := False;
  FSymbols.Add(S);
  Result := Self;
end;

function TFixtureModel.Species(const AName: string; AValue: Double): TFixtureModel;
var
  S: TFixtureSymbol;
begin
  S := Default(TFixtureSymbol);
  S.Name := AName; S.Kind := skSpecies; S.Value := AValue; S.HasValue := True;
  FSymbols.Add(S);
  Result := Self;
end;

function TFixtureModel.ConstSpecies(const AName: string;
  AValue: Double): TFixtureModel;
var
  S: TFixtureSymbol;
begin
  S := Default(TFixtureSymbol);
  S.Name := AName; S.Kind := skSpecies; S.Value := AValue; S.HasValue := True;
  S.Constant := True;
  FSymbols.Add(S);
  Result := Self;
end;

function TFixtureModel.Compartment(const AName: string; AValue: Double): TFixtureModel;
var
  S: TFixtureSymbol;
begin
  S := Default(TFixtureSymbol);
  S.Name := AName; S.Kind := skCompartment; S.Value := AValue; S.HasValue := True;
  FSymbols.Add(S);
  Result := Self;
end;

function TFixtureModel.Assigned_(const AName, AExpr: string): TFixtureModel;
var
  I: Integer;
  S: TFixtureSymbol;
begin
  Result := Self;
  I := IndexOfSymbol(AName);
  if I < 0 then Exit;
  S := FSymbols[I];
  S.Assignment := AExpr;
  FSymbols[I] := S;
end;

function TFixtureModel.Func(const AName: string; const AArgs: TArray<string>;
  const ABody: string): TFixtureModel;
var
  F: TFixtureFunction;
begin
  F.Name := AName; F.Args := AArgs; F.Body := ABody;
  FFunctions.Add(F);
  Result := Self;
end;

function TFixtureModel.WithoutSymbolKinds: TFixtureModel;
begin
  FKnowsKinds := False;
  Result := Self;
end;

function TFixtureModel.ReactionCount: Integer;
begin
  Result := FReactions.Count;
end;

function TFixtureModel.ReactionId(AIndex: Integer): string;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Id else Result := '';
end;

function TFixtureModel.RateLawText(AIndex: Integer): string;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].RateLaw else Result := '';
end;

function TFixtureModel.Reactants(AIndex: Integer): TSpeciesRefs;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Reactants else Result := nil;
end;

function TFixtureModel.Products(AIndex: Integer): TSpeciesRefs;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Products else Result := nil;
end;

function TFixtureModel.Modifiers(AIndex: Integer): TModifierRefs;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Modifiers else Result := nil;
end;

function TFixtureModel.SymbolKind(const AName: string): TSymbolKind;
var
  I: Integer;
begin
  if not FKnowsKinds then Exit(skUnknown);
  I := IndexOfSymbol(AName);
  if I < 0 then Result := skUnknown else Result := FSymbols[I].Kind;
end;

function TFixtureModel.HasValue(const AName: string): Boolean;
var
  I: Integer;
begin
  I := IndexOfSymbol(AName);
  Result := (I >= 0) and FSymbols[I].HasValue;
end;

function TFixtureModel.ValueOf(const AName: string): Double;
var
  I: Integer;
begin
  I := IndexOfSymbol(AName);
  if I < 0 then Result := NaN else Result := FSymbols[I].Value;
end;

function TFixtureModel.AssignmentRule(const AName: string): string;
var
  I: Integer;
begin
  I := IndexOfSymbol(AName);
  if I < 0 then Result := '' else Result := FSymbols[I].Assignment;
end;

function TFixtureModel.IsConstant(const AName: string): Boolean;
var
  I: Integer;
begin
  I := IndexOfSymbol(AName);
  Result := (I >= 0) and FSymbols[I].Constant;
end;

function TFixtureModel.UserFunction(const AName: string;
  out AArgs: TArray<string>; out ABody: string): Boolean;
var
  F: TFixtureFunction;
begin
  AArgs := nil;
  ABody := '';
  for F in FFunctions do
    if SameText(F.Name, AName) then
    begin
      AArgs := F.Args;
      ABody := F.Body;
      Exit(True);
    end;
  Result := False;
end;

function TFixtureModel.Annotate(const ALawId: string): TFixtureModel;
var
  R: TFixtureReaction;
begin
  Result := Self;
  if FReactions.Count = 0 then Exit;
  R := FReactions.Last;
  R.Annotation := ALawId;
  FReactions[FReactions.Count - 1] := R;
end;

function TFixtureModel.AnnotatedLaw(AIndex: Integer): string;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Annotation
  else Result := '';
end;

function TFixtureModel.KnowsSymbolKinds: Boolean;
begin
  Result := FKnowsKinds;
end;

function TFixtureModel.SourceLineOf(AIndex: Integer): Integer;
begin
  if InRange(AIndex) then Result := FReactions[AIndex].Line else Result := -1;
end;

{ ---------------------------------------------------------------- the corpus }

function CorrectMM: TFixtureModel;
begin
  Result := TFixtureModel.Create;
  Result.Species('S', 10).Species('P', 0)
        .Param('Vm', 5).Param('Km', 0.4)
        .Compartment('default_compartment', 1)
        .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
end;

function ModelForLaw(ALaw: TRateLawDef; const ARateLaw: string): TFixtureModel;
var
  I: Integer;
  R: TRole;
  Text: string;
  Products: Integer;
  V: Double;
begin
  Result := TFixtureModel.Create;

  { Symbols first, so the reaction can refer to them. Parameter values are
    distinct and positive: distinct because equal values would let a role swap
    go unnoticed by the dynamic checks, positive because nearly every law
    declares its parameters so. }
  V := 0.7;
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    R := ALaw.Roles[I];
    case R.Kind of
      rkSpecies:     Result.Species(R.Name, 1 + I);
      rkCompartment: Result.Compartment(R.Name, 1);
    else
      begin
        { A cooperativity exponent of 1 would make a Hill law degenerate into
          Michaelis-Menten and its sigmoidal invariant vacuous, so a role that
          says what it is for gets a value that suits it. }
        if SameText(R.Semantics, 'cooperativity') then
          Result.Param(R.Name, 2)
        else
        begin
          Result.Param(R.Name, V);
          V := V + 0.9;
        end;
      end;
    end;
  end;

  Text := ARateLaw;
  if Text = '' then Text := ALaw.Expression;
  Result.Reaction('J1', Text);

  Products := 0;
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    R := ALaw.Roles[I];
    if R.Kind <> rkSpecies then Continue;
    case R.Position of
      spSubstrate: Result.Reactant(R.Name);
      spProduct:   begin Result.Product(R.Name); Inc(Products); end;
      spInhibitor: Result.Modifier(R.Name, mrInhibitor);
      spActivator: Result.Modifier(R.Name, mrActivator);
      spModifier:  Result.Modifier(R.Name, mrUnspecified);
    else
      { A species role with no declared position is treated as a substrate:
        that is what an undeclared position means in every law that omits it. }
      Result.Reactant(R.Name);
    end;
  end;

  { Almost every law's applicability wants at least one product, and a law
    that names none of its own would otherwise fail to apply to the very
    reaction built for it. }
  if Products = 0 then
  begin
    Result.Species('__P', 0);
    Result.Product('__P');
  end;
end;

function Corpus: TArray<TRateLawTestCase>;

  function D(const AName, AWhy: string; ABuild: TFunc<TFixtureModel>;
             const AExpect: array of string;
             const AExtraLaws: array of string): TRateLawTestCase;
  var
    I: Integer;
  begin
    Result := Default(TRateLawTestCase);
    Result.Name    := AName;
    Result.Why     := AWhy;
    Result.Build   := ABuild;
    Result.Dynamic := True;
    SetLength(Result.Expect, Length(AExpect));
    for I := 0 to High(AExpect) do Result.Expect[I] := AExpect[I];
    SetLength(Result.ExtraLaws, Length(AExtraLaws));
    for I := 0 to High(AExtraLaws) do Result.ExtraLaws[I] := AExtraLaws[I];
  end;

  function C(const AName, AWhy: string; ABuild: TFunc<TFixtureModel>;
             const AExpect: array of string;
             const AExtraLaws: array of string): TRateLawTestCase; overload;
  var
    I: Integer;
  begin
    Result := Default(TRateLawTestCase);
    Result.Name  := AName;
    Result.Why   := AWhy;
    Result.Build := ABuild;
    SetLength(Result.Expect, Length(AExpect));
    for I := 0 to High(AExpect) do
      Result.Expect[I] := AExpect[I];
    SetLength(Result.ExtraLaws, Length(AExtraLaws));
    for I := 0 to High(AExtraLaws) do
      Result.ExtraLaws[I] := AExtraLaws[I];
  end;

  function C(const AName, AWhy: string; ABuild: TFunc<TFixtureModel>;
             const AExpect: array of string): TRateLawTestCase; overload;
  begin
    Result := C(AName, AWhy, ABuild, AExpect, []);
  end;

begin
  Result := [

    C('correct-mm',
      'The false-positive baseline. A correct law written plainly must produce '
      + 'nothing at all, or every other case is noise.',
      function: TFixtureModel begin Result := CorrectMM end,
      []),

    C('mm-duplicated-operand',
      'The founding case: Vm*S/(Km + Km) parses, simulates, and is wrong. '
      + 'Visible only after canonicalisation, where the denominator becomes '
      + 'a sum of two identical operands.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + Km)').Reactant('S').Product('P');
      end,
      ['S004']),

    C('mm-missing-parens',
      'Vm*S/Km + S has the same symbols as the correct form and a different '
      + 'tree. Visible only BEFORE canonicalisation, which is why both trees '
      + 'are retained.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/Km + S').Reactant('S').Product('P');
      end,
      ['S010']),

    C('mm-via-user-function',
      'A rate law factored into a user-defined function is good practice and '
      + 'common. Without inlining it looks like no law at all, so this must '
      + 'produce exactly what the inline form produces: nothing.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Func('MM', ['s', 'v', 'k'], 'v*s/(k+s)')
              .Reaction('J1', 'MM(S, Vm, Km)').Reactant('S').Product('P');
      end,
      []),

    C('uninitialised-parameter',
      'Km declared with no value at all. Distinct from a value of zero, which '
      + 'is the only reason HasValue exists separately from ValueOf.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).UnsetParam('Km')
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      ['S014']),

    C('hill-duplicated-operand',
      'The milestone test of genericity: the Hill equivalent of the founding '
      + 'defect must be caught with NO Hill-specific code anywhere in the '
      + 'engine. If this needs special handling, the design has failed.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('K', 0.4).Param('n', 2)
              .Reaction('J1', 'Vm*S^n/(K^n + K^n)').Reactant('S').Product('P');
      end,
      ['S004']),

    C('mm-operator-substitution',
      'A product where the law has a sum. It differs from mm-missing-parens '
      + 'in no symbol at all -- both use exactly the law''s symbols -- so the '
      + 'two are told apart by whether the differing node joins the same '
      + 'operands. Here it does, so the operator is wrong, not the grouping.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km*S)').Reactant('S').Product('P');
      end,
      ['S003']),

    C('mm-role-swap-model',
      'The parameters are transposed. The shape is perfect once the binder '
      + 'swaps them, so there is no structural difference left to see -- the '
      + 'naming is the only evidence, which is what S007 exists for.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Km*S/(Vm + S)').Reactant('S').Product('P');
      end,
      ['S007']),

    C('mass-action-first-order',
      'The milestone case, part one. One registry entry -- a family, not an '
      + 'expression -- instantiated from this reaction''s own stoichiometry.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1*A').Reactant('A').Product('B');
      end,
      []),

    C('mass-action-second-order',
      'Part two: two substrates, from the SAME entry. If this needed a second '
      + 'registry entry the generality claim would be false for the commonest '
      + 'law in biology.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 5).Species('C', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1*A*B')
              .Reactant('A').Reactant('B').Product('C');
      end,
      []),

    C('mass-action-third-order',
      'Part three.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 5).Species('C', 2).Species('D', 0)
              .Param('k1', 0.1)
              .Reaction('J1', 'k1*A*B*C')
              .Reactant('A').Reactant('B').Reactant('C').Product('D');
      end,
      []),

    C('mass-action-stoichiometric-power',
      '2 A -> B is second order in A, and the exponent comes from the '
      + 'stoichiometry rather than from the registry. A model writing k*A^2 '
      + 'must be clean.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1*A^2').Reactant('A', 2).Product('B');
      end,
      []),

    C('mass-action-symbolic-stoichiometry',
      'A stoichiometry written as a symbol gives NaN from the numeric '
      + 'accessor, so the exponent has to come from the symbol''s name. This '
      + 'is why TSpeciesRef has carried both a number and its source text '
      + 'since the interface was first written.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S1', 1).Species('S2', 1).Species('S3', 0)
              .Param('k', 0.1).Param('n', 2)
              .Reaction('J1', 'k*S1*S2^n')
              .Reactant('S1').SymbolicReactant('S2', 'n').Product('S3');
      end,
      []),

    C('mass-action-zero-order',
      'A source term has no substrates at all, so the product is empty and k '
      + 'alone is the whole law. Falls out of the same rule rather than '
      + 'needing a special case.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1').Product('A');
      end,
      []),

    C('mass-action-missing-substrate',
      'k1*A where the reaction consumes A and B. The rate law omits a '
      + 'substrate the stoichiometry declares, which is a real and easy '
      + 'mistake in a multi-substrate step.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 5).Species('C', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1*A')
              .Reactant('A').Reactant('B').Product('C');
      end,
      ['S005', 'S017']),

    C('mass-action-wrong-power',
      'k1*A^3 for a reaction that consumes 2 A. The exponent disagrees with '
      + 'the stoichiometry it is supposed to come from.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 0).Param('k1', 0.1)
              .Reaction('J1', 'k1*A^3').Reactant('A', 2).Product('B');
      end,
      ['S008']),

    C('ambiguous-two-laws-same-shape',
      'The milestone case: a registry holding two laws of the same shape. '
      + 'Not contrived -- a user who adds their own Michaelis-Menten variant '
      + 'alongside the built-in has exactly this. The reaction fits both '
      + 'perfectly and they are equally specific, so there is nothing to '
      + 'choose and S002 with NOTHING checked is the only honest answer.',
      function: TFixtureModel begin Result := CorrectMM end,
      ['S002'],
      ['{"id":"my_michaelis_menten","name":"My MM","version":1,'
       + '"enabled":true,"expression":"Vm * S / (Km + S)",'
       + '"roles":{"S":{"kind":"species","position":"substrate"},'
       + '"Vm":{"kind":"parameter"},"Km":{"kind":"parameter"}},'
       + '"applicability":{"reactants":"1","products":">=1"}}']),

    C('ambiguity-not-declared-away-by-specificity',
      'A near-tie between laws of DIFFERENT specificity is not ambiguous: '
      + 'the more specific law accounts for more of the expression and wins. '
      + 'Without this, mass action -- k*S for a single substrate, loose '
      + 'enough to sit near almost anything -- would draw with every tight '
      + 'law and suppress real findings across a whole class of models.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km*S)').Reactant('S').Product('P');
      end,
      ['S003']),

    C('hill-mutant-picks-the-right-hill',
      'Found by the stress harness, not invented. This expression sits close '
      + 'to both Hill forms, and before the margin existed it was silently '
      + 'assigned to repression, so every finding described a law the model '
      + 'never resembled. It now identifies activation and names the real '
      + 'defect.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('K', 0.4).Param('n', 2)
              .Reaction('J1', 'Vm*S^n/(K^n + K^n)').Reactant('S').Product('P');
      end,
      ['S004']),

    C('annotation-resolves-ambiguity',
      'The same expression, annotated. An annotation is the only evidence '
      + 'that can settle a genuine tie, which is most of why annotations '
      + 'exist -- and with the law now known, the duplicated operand it was '
      + 'hiding becomes reportable.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('K', 0.4).Param('n', 2)
              .Reaction('J1', 'Vm*S^n/(K^n + K^n)').Reactant('S').Product('P')
              .Annotate('hill_activation');
      end,
      ['S004']),

    C('annotation-catches-wrong-law',
      'The case inference can never produce. The reaction is annotated as '
      + 'Michaelis-Menten and is nothing of the sort; without the annotation '
      + 'it would simply report "matches nothing registered", which is silent '
      + 'about the modeller having asserted something false.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S*Km').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      ['S010']),

    C('annotation-applicability-violation',
      'Annotated as irreversible Michaelis-Menten, but the reaction consumes '
      + 'two substrates. Applicability normally just removes a law from '
      + 'consideration; where the modeller ASSERTED it, the mismatch is '
      + 'itself the finding.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 5).Species('C', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*A/(Km + A)')
              .Reactant('A').Reactant('B').Product('C')
              .Annotate('michaelis_menten_irrev');
      end,
      ['S013', 'S017']),

    C('annotation-names-unknown-law',
      'A misspelled or invented law id. Silently ignoring it would leave the '
      + 'modeller believing a check is running that never was.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P')
              .Annotate('michaelis_menton_irrev');
      end,
      ['S019']),

    D('dynamic-half-max-at-the-wrong-place',
      'The case for a dynamic engine. The static engine does notice something '
      + 'here -- Km/2 is not Km, so the shapes differ -- but all it can say '
      + 'is that the grouping is wrong. Only evaluation can say WHAT is '
      + 'wrong: the half-maximal rate no longer falls at the parameter named '
      + 'for it. A model whose structure matched exactly could not differ '
      + 'behaviourally at all, so on a model the dynamic engine explains '
      + 'rather than replaces; the case where it finds what structure cannot '
      + 'is a registry entry checked against itself (R015).',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km/2 + S)').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      ['D005', 'D006', 'S010'], []),

    D('dynamic-correct-mm-behaves',
      'The false-positive guard for the behavioural half. A correct law must '
      + 'satisfy every invariant its own registry entry declares, or the '
      + 'entry is wrong and every model checked against it suffers.',
      function: TFixtureModel begin Result := CorrectMM end,
      [], []),

    D('dynamic-sign-flipped',
      'A negated rate law. Structurally it is a product away from correct, '
      + 'but what makes it wrong is that the rate runs backwards -- which is '
      + 'a statement about values, not about shape.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', '-Vm*S/(Km + S)').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      { S009 -- a dedicated sign defect -- is specified but not implemented;
        the static engine reports the stray -1 as an extraneous term instead.
        Listed as it actually behaves rather than as it ought to. }
      ['D002', 'D003', 'D004', 'D005', 'D006', 'S006'], []),

    D('dynamic-mass-action-behaves',
      'Mass action declares that the rate vanishes when any substrate does. '
      + 'The invariant is checked against the INSTANTIATED law, so the same '
      + 'registry entry states it once for every order.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 5).Species('C', 0)
              .Param('k1', 0.1)
              .Reaction('J1', 'k1*A*B')
              .Reactant('A').Reactant('B').Product('C');
      end,
      [], []),

    D('dynamic-near-equal-in-regime',
      'THE case for a differential comparison, and the milestone''s own test. '
      + 'Vm*S/Km is the first-order approximation of Michaelis-Menten: below '
      + 'Km it agrees to within a percent or two, which is exactly the regime '
      + 'somebody tests in, and above Km it is wrong without limit. The '
      + 'structural engine says the shapes differ; only evaluating both says '
      + 'how much that costs and where it starts to.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/Km').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      ['D004', 'D005', 'D006', 'S010'], []),

    D('dynamic-same-rate-written-differently',
      'The other half, and the more useful one. This is Michaelis-Menten '
      + 'multiplied top and bottom by 2 -- a different tree, an identical '
      + 'rate. The structural engine reports a regrouping, which is true and '
      + 'reads like an error; D008 is what says the difference is one of form '
      + 'alone and the model computes the right thing.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', '2*Vm*S/(2*Km + 2*S)').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      ['S010'], []),

    C('declared-inhibitor',
      'Antimony states modifier roles through its interaction arrows, so an '
      + 'inhibitor is known rather than inferred from position.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0).Species('I', 1)
              .Param('Vm', 5).Param('Km', 0.4).Param('Ki', 2)
              .Reaction('J1', 'Vm*S/(Km*(1 + I/Ki) + S)')
              .Reactant('S').Product('P').Modifier('I', mrInhibitor);
      end,
      []),

    { ---- what the BioModels corpus sent back (M17) ---- }

    C('compartment-volume-factor-is-not-kinetics',
      'An SBML kinetic law is a rate, not a rate of change of concentration, '
      + 'so it is written as volume times kinetics. The volume belongs to the '
      + 'reaction and no law has a role for it. Left in, it was offered to '
      + 'every parameter role -- the corpus produced warnings saying "cyt" '
      + 'plays the Ks role -- and the shape then failed to match, which made '
      + 'this the largest single source of false positives over BioModels. '
      + 'Correct Michaelis-Menten times a volume must report nothing.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Compartment('cyt', 1)
              .Reaction('J1', 'cyt*Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      []),

    C('compartment-volume-factor-on-a-sum',
      'The same, in the form the corpus actually shows most often: a volume '
      + 'multiplying a parenthesised sum. Parses with the multiplication at '
      + 'the root rather than a division, which is a different path through '
      + 'the stripper and was worth a case of its own.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 1)
              .Param('kf', 2).Param('kr', 0.5)
              .Compartment('comp1', 1)
              .Reaction('J1', 'comp1*(kf*A - kr*B)').Reactant('A').Product('B');
      end,
      []),

    C('clamped-reactant-need-not-appear',
      'S017 says a reaction consuming something ought to depend on how much '
      + 'of it there is. A species held constant is the standing exception: '
      + 'clamping it IS the statement that the kinetics do not vary with it. '
      + 'Over BioModels 78%% of S017 findings were on boundary species and '
      + 'every one was wrong.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.ConstSpecies('CO2', 1).Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S)')
              .Reactant('S').Reactant('CO2').Product('P');
      end,
      []),

    C('unclamped-reactant-still-reported',
      'The other side of the same exemption: an ordinary species left out of '
      + 'its own rate law is still S017. Without this case the exemption '
      + 'could be widened to everything and the suite would not notice.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('X', 1).Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S)')
              .Reactant('S').Reactant('X').Product('P');
      end,
      ['S017']),

    C('missing-kinetics-among-kinetics-is-still-reported',
      'S015 is now said once for a model with no kinetics anywhere -- a '
      + 'genome-scale reconstruction is not a model with four thousand '
      + 'defects. One reaction missing its law among reactions that have '
      + 'theirs is a different statement, and this case is what stops the '
      + 'collapse being widened until it swallows that one too.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0).Species('Q', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P')
              .Reaction('J2', '').Reactant('P').Product('Q');
      end,
      ['S015']),

    C('dropped-term-still-caught-when-declared',
      'The other half of the association change. Inference no longer admits '
      + 'a law on the strength of sharing its vocabulary, so a rate law with '
      + 'a term left out no longer associates by shape -- five drop '
      + 'mutations went undetected when that admission was removed. This is '
      + 'the case that shows what was actually lost: nothing, where the '
      + 'modeller says which law they meant. Km is gone from the '
      + 'denominator, and the annotation is what carries the finding.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/S').Reactant('S').Product('P')
              .Annotate('michaelis_menten_irrev');
      end,
      ['S005', 'S010']),

    C('reversible-mass-action-uni',
      'The second generative family. It needs two scalar rate constants and '
      + 'a product over the PRODUCTS, and the instantiator refused both by '
      + 'construction until the corpus run made the omission impossible to '
      + 'ignore -- reversible mass action is everywhere in BioModels and was '
      + 'not merely unregistered but inexpressible.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 1)
              .Param('kf', 2).Param('kr', 0.5)
              .Reaction('J1', 'kf*A - kr*B').Reactant('A').Product('B');
      end,
      []),

    C('reversible-mass-action-takes-stoichiometry-from-both-sides',
      'One entry has to cover A <-> B, A + B <-> C and 2A <-> B alike, on '
      + 'both sides at once. If the product side were ignored -- which is '
      + 'what the old instantiator did -- this would report a defect against '
      + 'a correct model.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 2).Species('C', 1)
              .Param('kf', 2).Param('kr', 0.5)
              .Reaction('J1', 'kf*A^2 - kr*B*C')
              .Reactant('A', 2).Product('B').Product('C');
      end,
      []),

    C('a-rule-is-a-value',
      'S014 says a parameter with no value cannot be evaluated. One defined '
      + 'by an assignment rule has no literal value and needs none -- the '
      + 'rule is its value. Every S014 over the BioModels corpus that was '
      + 'not a genuinely undefined symbol was this: 147 findings over 18 '
      + 'models, all wrong.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Km', 0.4).Param('Vbase', 5)
              .UnsetParam('Vm').Assigned_('Vm', '2*Vbase')
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      []),

    C('no-value-and-no-rule-is-still-S014',
      'The other side of that exemption. A parameter with neither a value '
      + 'nor a rule genuinely cannot be evaluated, and without this case the '
      + 'exemption could be widened to every unset parameter unnoticed.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Km', 0.4).UnsetParam('Vm')
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      ['S014']),

    C('compartment-volume-distributed-over-a-sum',
      'libSBML renders a reversible reaction as "Cell*kf*A - Cell*kr*B" '
      + 'often enough to matter: the volume multiplies each term rather '
      + 'than the whole expression. The first version of the stripper '
      + 'walked only the multiplicative spine and stopped at the sum, so '
      + 'the volume survived inside both terms and BioModels came back with '
      + 'a page of S005/S006 pairs against correct reversible reactions.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 1)
              .Param('kf', 2).Param('kr', 0.5)
              .Compartment('Cell', 1)
              .Reaction('J1', 'Cell*kf*A - Cell*kr*B')
              .Reactant('A').Product('B');
      end,
      []),

    C('a-volume-on-only-one-term-is-not-a-volume-factor',
      'The guard on that. "Cell*a - b" is not a volume multiplying a rate, '
      + 'and cancelling it would change what the expression means rather '
      + 'than tidy it. Only a factor common to every term comes off.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 1)
              .Param('kf', 2).Param('kr', 0.5)
              .Compartment('Cell', 1)
              .Reaction('J1', 'Cell*kf*A - kr*B')
              .Reactant('A').Product('B');
      end,
      ['S006']),

    C('built-in-symbols-are-not-undefined',
      'time is SBML''s own symbol and pi is a constant of mathematics. '
      + 'Neither is defined by the model and nothing knew they were '
      + 'special, so a rate law mentioning either was reported as using an '
      + 'undefined symbol -- 113 of the 147 S014 findings over BioModels, '
      + 'all wrong -- and both were offered to the binder as parameters, '
      + 'where pi could be picked to play a Km.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0).Param('k', 2)
              .Reaction('J1', 'k*S*sin(2*pi*time)')
              .Reactant('S').Product('P');
      end,
      []),

    C('emptyset-is-not-a-species',
      'Antimony writes synthesis as "-> P" and names the absent side '
      + 'EmptySet. It is notation for nothing: no concentration, and no '
      + 'rate law mentions it. Nothing knew that, so mass action '
      + 'instantiated over [EmptySet] to give "k*EmptySet" and every real '
      + 'synthesis rate law then looked like a substrate swap -- 269 S007 '
      + 'findings over BioModels, the largest error class left after the '
      + 'association work, and every one of them wrong.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('EmptySet', 0).Species('P', 0).Param('k', 2)
              .Reaction('J1', 'k').Reactant('EmptySet').Product('P');
      end,
      []),

    C('emptyset-degradation-is-first-order',
      'The mirror image: "S ->" is degradation, first order in S, with '
      + 'EmptySet on the product side this time. The exclusion has to work '
      + 'from both directions or one of the two commonest reaction shapes '
      + 'in biology still reports against a correct model.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('EmptySet', 0).Species('S', 10).Param('k', 2)
              .Reaction('J1', 'k*S').Reactant('S').Product('EmptySet');
      end,
      []),

    C('catalytic-synthesis',
      'Transcription proportional to its gene, translation to its mRNA: a '
      + 'rate that depends on a species the reaction neither consumes nor '
      + 'produces. Mass action takes its species from stoichiometry alone, '
      + 'so it instantiated k*<substrate> and reported the modifier as a '
      + 'substrate swap. 416 of the 798 erroring reactions traced over '
      + 'BioModels were this, and 255 of them said S007.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('EmptySet', 0).Species('P', 0).Species('mRNA', 5)
              .Param('ks', 2)
              .Reaction('J1', 'ks*mRNA').Reactant('EmptySet').Product('P')
              .Modifier('mRNA', mrUnspecified);
      end,
      []),

    C('catalytic-conversion',
      'The other form: an enzyme-proportional conversion that does have a '
      + 'substrate, so the law is k*E*S. One entry has to cover both or the '
      + 'commoner half is still reported against the wrong law.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0).Species('E', 1)
              .Param('kcat', 2)
              .Reaction('J1', 'kcat*E*S').Reactant('S').Product('P')
              .Modifier('E', mrUnspecified);
      end,
      []),

    C('catalytic-mass-action-needs-a-modifier',
      'The load-bearing constraint. With no modifier this law instantiates '
      + 'to k*prod(Si), which IS mass action -- so the two would tie on '
      + 'every ordinary reaction and S002 would cancel both. It reported '
      + 'exactly that until the applicability constraint was honoured, which '
      + 'exposed a real bug: BindReaction swaps in the instantiated law '
      + 'BEFORE calling LawApplies, and InstantiateGenerative was not '
      + 'copying Applicability across, so every generative constraint was '
      + 'silently discarded.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 5).Species('B', 0).Param('k', 2)
              .Reaction('J1', 'k*A').Reactant('A').Product('B');
      end,
      []),

    C('substrate-absent-from-its-own-rate-law',
      'A reaction that consumes something at a rate independent of how much '
      + 'of it there is: saturated transport, a step limited entirely by its '
      + 'enzyme. Adding catalytic mass action ALONE moved the corpus errors '
      + 'the wrong way, 16.6%% to 21.3%%, because this shape then matched a '
      + 'law insisting on a substrate term it does not have. S017 still '
      + 'says the substrate is missing, which is the honest observation; '
      + 'what changes is that the reaction is no longer also accused of '
      + 'being a broken copy of a law it never followed.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('FH2f', 5).Species('FH4', 0).Species('FH2b', 2)
              .Param('kter', 2)
              .Reaction('J1', 'kter*FH2b').Reactant('FH2f').Product('FH4');
      end,
      ['S017']),

    C('zero-order-is-a-rate-law',
      'A -> B; k1 is a step running at a fixed rate, which is what a '
      + 'saturated enzyme looks like. Reporting "no registered rate law '
      + 'matches" told the reader the checker had nothing to say about a '
      + 'reaction that is textbook zero order.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 0).Param('k1', 0.3)
              .Reaction('J1', 'k1').Reactant('A').Product('B');
      end,
      ['S017']),

    C('a-source-term-is-still-mass-action',
      'The constraint that keeps zero order apart from mass action. With no '
      + 'reactants, mass action''s empty product already instantiates to '
      + 'exactly k, so without "reactants >= 1" the two tie on every source '
      + 'term and S002 cancels both.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('EmptySet', 0).Species('B', 0).Param('k', 0.3)
              .Reaction('J1', 'k').Reactant('EmptySet').Product('B');
      end,
      []),

    D('undefined-at-the-models-own-values',
      'A structurally perfect Michaelis-Menten that cannot be evaluated for '
      + 'the model it sits in: Km and S are both zero, so the denominator '
      + 'vanishes at time zero and the reaction cannot be integrated at all. '
      + 'Every other behavioural check tests the LAW over a grid of its own '
      + 'and never reads the model numbers, so all of them pass this and '
      + 'only D101 sees it.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 0).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0)
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      ['D101'], []),

    D('defined-at-the-models-own-values',
      'The guard on it. A species starting at zero is ordinary -- every '
      + 'intermediate in a chain does -- and says nothing on its own. Only a '
      + 'rate law that cannot be worked out from the starting values is a '
      + 'finding, so this one, with the same S=0 and a Km that is not zero, '
      + 'must stay silent.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 0).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S)').Reactant('S').Product('P');
      end,
      [], [])
  ];
end;

{ ------------------------------------------------------ canonicalisation pairs }

function P(const A, B, AWhy: string): TExprPair;
begin
  Result.A := A; Result.B := B; Result.Why := AWhy;
end;

function EquivalentPairs: TArray<TExprPair>;
begin
  Result := [
    P('Vm*S/(Km + S)', 'S*Vm/(S + Km)',
      'Commutativity of + and *, which is the commonest stylistic variation '
      + 'there is. If this fails nothing else matters.'),

    P('Vm*S/(Km + S)', '(Vm*S)/(Km + S)',
      'Redundant parentheses that change nothing.'),

    P('Vm*S/(Km + S)', 'Vm*S*(Km + S)^-1',
      'Division rewritten as a negative power -- rule 2. The two forms are '
      + 'the same expression and a registry entry may use either.'),

    P('a*b*c', 'c*(b*a)',
      'Associativity: flattening must make nesting irrelevant.'),

    P('a + b + c', '(c + a) + b',
      'The same for sums.'),

    P('S*S', 'S^2',
      'Rule 5. A modeller writing second-order mass action as S*S must not '
      + 'read as different from S^2.'),

    P('S*S*S', 'S^3',
      'The same collection, three deep.'),

    P('x^2*x^3', 'x^5',
      'Exponents of a collected base sum.'),

    P('(x^2)^3', 'x^6',
      'A power of a power. Needed for rule 5 to be self-consistent -- without '
      + 'it these two would be different factors of the same product.'),

    P('a - b', 'a + (-1)*b',
      'Rule 2 on subtraction.'),

    P('-x', '(-1)*x',
      'Unary minus is a product, so it collects with other coefficients.'),

    P('2*3*x', '6*x',
      'Rule 3: literals fold.'),

    P('x/x', '1',
      'Falls out of rules 2 and 5 together: x^1 * x^-1 is x^0 is 1.'),

    P('1*x', 'x',
      'A unit coefficient is dropped, so it cannot make two equal products '
      + 'differ.'),

    P('x + 0', 'x',
      'The same for a zero term.'),

    P('+x', 'x',
      'Unary plus is not represented at all.'),

    P('2^3^2', '512',
      'Right-associativity of ^: this is 2^(3^2), not (2^3)^2 = 64.'),

    P('Vm * S / (Km + S)', 'Vm*S/(Km+S)',
      'Whitespace.')
  ];
end;

function DistinctPairs: TArray<TExprPair>;
begin
  Result := [
    P('Vm*S/(Km + Km)', 'Vm*S/(Km + S)',
      'THE founding case. The defect must survive canonicalisation, or the '
      + 'static engine has nothing left to find.'),

    P('Vm*S/(Km + S)', 'Vm*S/Km + S',
      'A missing parenthesis. Same symbols, different tree -- and if these '
      + 'ever compare equal the canonicaliser has become an algebra system.'),

    P('Vm*S/(Km*S)', 'Vm*S/(Km + S)',
      'Operator substitution in the denominator: * where + was meant.'),

    P('Vm*S^2/(Km + S)', 'Vm*S/(Km + S)',
      'An exponent that should not be there.'),

    P('Km*S/(Vm + S)', 'Vm*S/(Km + S)',
      'Two identifiers swapped. Canonical sorting must not make a role swap '
      + 'invisible by reordering it away.'),

    P('x + x', '2*x',
      'Deliberately NOT equal. Collecting like terms in a sum would turn '
      + 'Km + Km into 2*Km and cost us the duplicated-operand signal. This '
      + 'pair documents the trade rather than hiding it.'),

    P('(x + y)*z', 'x*z + y*z',
      'Deliberately NOT equal. Distribution would let a real parenthesisation '
      + 'error normalise into the correct form and vanish.'),

    P('f(a, b)', 'f(b, a)',
      'Function arguments are not commutative, whatever the function is.'),

    P('a - b', 'b - a',
      'Subtraction is not commutative; the rewrite to a sum must not lose '
      + 'which operand carried the -1.')
  ];
end;

function MalformedExpressions: TArray<string>;
begin
  Result := [
    'Vm*S/(Km + S',      // unclosed parenthesis
    'Vm**S',             // doubled operator
    'Vm*S/',             // trailing operator
    '(',                 // nothing but an opening paren
    '',                  // empty
    '   ',               // whitespace only
    'Vm*S)',             // unbalanced close
    'Vm S',              // two atoms, no operator
    '2 +'                // ends mid-expression
  ];
end;

{ ------------------------------------------------------------ bad registry entries }

function BadLawEntries: TArray<TBadLawCase>;

  function B(const AName, ACode, AWhy, AJson: string): TBadLawCase;
  begin
    Result.Name := AName; Result.Code := ACode;
    Result.Why := AWhy;   Result.Json := AJson;
  end;

begin
  Result := [

    B('undeclared-symbol', 'R006',
      'The expression mentions Kx, which has no role. Role binding would have '
      + 'nothing to bind it to, so every reaction would mismatch on a symbol '
      + 'that only exists in the registry.',
      '{"id":"bad1","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Kx + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}}}'),

    B('expression-will-not-parse', 'R005',
      'An unbalanced parenthesis in the registry, not in the model. Without '
      + 'this check the law loads and silently matches nothing.',
      '{"id":"bad2","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}}}'),

    B('invariant-names-unknown-variable', 'R009',
      'The invariant asserts half-maximal rate at Kd, but the law has no Kd. '
      + 'The invariant refers to nothing and would never be evaluable.',
      '{"id":"bad3","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"invariants":[{"type":"value_at","point":{"Kd":"1"},"equals":"Vm/2"}]}'),

    B('unknown-invariant-type', 'R011',
      'A misspelled or invented invariant type. Accepting it would mean a '
      + 'declared property that is silently never checked -- the worst outcome, '
      + 'since the author believes it is being enforced.',
      '{"id":"bad4","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"invariants":[{"type":"monotonik","var":"S","direction":"increasing"}]}'),

    B('invariant-equals-will-not-parse', 'R010',
      'The equals expression is malformed. Same reasoning as R005, one level in.',
      '{"id":"bad5","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"invariants":[{"type":"limit","var":"S","to":"inf","equals":"Vm/"}]}'),

    B('duplicate-role', 'R004',
      'The same role declared twice. JSON itself permits duplicate keys, so '
      + 'this has to be caught here.',
      '{"id":"bad6","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"},"Km":{"kind":"parameter"}}}'),

    B('log-sampling-from-zero', 'R003',
      'A logarithmic grid cannot start at zero. Clamping it silently would '
      + 'move the sample points somewhere the law was never asked about, and '
      + 'a dynamic finding would then carry a witness the user cannot reproduce.',
      '{"id":"bad7","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"sampling":{"S":{"scale":"log","range":["0","1e3"],"n":64}}}'),

    B('bad-applicability', 'R013',
      'An applicability count that is not a count. It would silently never '
      + 'match, making the law look like it simply does not apply anywhere.',
      '{"id":"bad8","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"applicability":{"reactants":"one"}}'),

    B('limit-without-equals', 'R003',
      'A limit invariant with nothing to approach. Nothing to test against.',
      '{"id":"bad9","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (Km + S)",'
      + '"roles":{"S":{"kind":"species"},"Vm":{"kind":"parameter"},'
      + '"Km":{"kind":"parameter"}},'
      + '"invariants":[{"type":"limit","var":"S","to":"inf"}]}'),

    B('law-fails-its-own-invariant', 'R015',
      'Specification 7.3, and the case only evaluation can find: the entry is '
      + 'structurally impeccable and internally FALSE. It declares '
      + 'half-maximal rate at Km while putting it at 2*Km. Accepted, it would '
      + 'report that same defect against every correct model checked with it, '
      + 'and the user would have no way to tell the tool was wrong rather '
      + 'than their model.',
      '{"id":"bad10","name":"Bad","version":1,"enabled":true,'
      + '"expression":"Vm * S / (2*Km + S)",'
      + '"roles":{"S":{"kind":"species","position":"substrate"},'
      + '"Vm":{"kind":"parameter"},"Km":{"kind":"parameter"}},'
      + '"invariants":[{"type":"value_at","point":{"S":"Km"},'
      + '"equals":"Vm/2"}]}'),

    B('not-json', 'R001',
      'A file that is not JSON at all. Must name the file rather than throwing.',
      'this is not json')
  ];
end;

{ --------------------------------------------------------------- bind cases }

function BindCases: TArray<TBindCase>;

  function BC(const AName, ALawId, AWhy: string; ABuild: TFunc<TFixtureModel>;
              AOutcome: TBindOutcome; const AExpect: array of string;
              ASuspicious: Boolean = False): TBindCase;
  var
    I: Integer;
  begin
    Result.Name := AName; Result.LawId := ALawId; Result.Why := AWhy;
    Result.Build := ABuild; Result.Outcome := AOutcome;
    Result.Suspicious := ASuspicious;
    SetLength(Result.Expect, Length(AExpect));
    for I := 0 to High(AExpect) do Result.Expect[I] := AExpect[I];
  end;

begin
  Result := [

    BC('mm-own-names', 'michaelis_menten_irrev',
      'The milestone case: a correct MM model written in the law''s own '
      + 'vocabulary must bind S, Vm and Km to themselves.',
      function: TFixtureModel begin Result := CorrectMM end,
      boBound, ['S=S', 'Vm=Vm', 'Km=Km']),

    BC('mm-foreign-names', 'michaelis_menten_irrev',
      'The same law written with a modeller''s own names. S binds from '
      + 'stoichiometry; k1 and k2 carry no naming hint at all, so the only '
      + 'thing that can separate them is which one makes the expression fit.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 10).Species('B', 0)
              .Param('k1', 5).Param('k2', 0.4)
              .Reaction('J1', 'k1*A/(k2 + A)').Reactant('A').Product('B');
      end,
      boBound, ['S=A', 'Vm=k1', 'Km=k2']),

    BC('mm-conventional-aliases', 'michaelis_menten_irrev',
      'Vmax and KM are declared naming conventions, so they should bind '
      + 'without needing the shape to decide.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vmax', 5).Param('KM', 0.4)
              .Reaction('J1', 'Vmax*S/(KM + S)').Reactant('S').Product('P');
      end,
      boBound, ['S=S', 'Vm=Vmax', 'Km=KM']),

    BC('mm-role-swap', 'michaelis_menten_irrev',
      'The parameters are transposed: the thing called Km sits where Vm '
      + 'belongs. Shape must win over names -- binding Km to the Km role '
      + 'here would make the swap invisible, which is the exact failure the '
      + 'name-last ordering exists to prevent. The binding is flagged.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Km*S/(Vm + S)').Reactant('S').Product('P');
      end,
      boBound, ['S=S', 'Vm=Km', 'Km=Vm'], True),

    BC('hill-binds', 'hill_activation',
      'Three parameters, six permutations. Proves the binder is not '
      + 'Michaelis-Menten-shaped -- no law-specific code was added for this.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('K', 0.4).Param('n', 2)
              .Reaction('J1', 'Vm*S^n/(K^n + S^n)').Reactant('S').Product('P');
      end,
      boBound, ['S=S', 'Vm=Vm', 'K=K', 'n=n']),

    BC('mm-two-reactants-not-applicable', 'michaelis_menten_irrev',
      'Applicability rules the law out before any binding is attempted: a '
      + 'two-substrate reaction is not irreversible MM whatever its rate law '
      + 'looks like.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('A', 1).Species('B', 1).Species('C', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*A/(Km + A)')
              .Reactant('A').Reactant('B').Product('C');
      end,
      boNotApplicable, []),

    BC('mass-action-instantiates', 'mass_action_irrev',
      'The family is turned into a concrete law for this reaction before any '
      + 'binding happens, so the binder never learns that families exist. '
      + 'The substrate role is named after the model''s own species and binds '
      + 'to itself -- there is nothing to choose.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S1', 1).Species('S2', 0).Param('k', 0.1)
              .Reaction('J1', 'k*S1').Reactant('S1').Product('S2');
      end,
      boBound, ['k=k', 'S1=S1']),

    BC('unparsable-rate-law', 'michaelis_menten_irrev',
      'A model whose rate law will not parse is exactly the model a linter '
      + 'is most needed for, so this must be a reportable outcome rather '
      + 'than an exception.',
      function: TFixtureModel
      begin
        Result := TFixtureModel.Create;
        Result.Species('S', 10).Species('P', 0)
              .Param('Vm', 5).Param('Km', 0.4)
              .Reaction('J1', 'Vm*S/(Km + S').Reactant('S').Product('P');
      end,
      boUnparsable, [])
  ];
end;

{ ------------------------------------------------------------- DescribeModel }

function DescribeModel(const AModel: IModelSource): string;
var
  SB: TStringBuilder;
  I, J: Integer;
  Refs: TSpeciesRefs;
  Mods: TModifierRefs;

  function RefText(const R: TSpeciesRef): string;
  begin
    if R.IsSymbolic then
      Result := Format('%s x %s (symbolic)', [R.Name, R.Text])
    else if SameValue(R.Value, 1) then
      Result := R.Name
    else
      Result := Format('%s x %g', [R.Name, R.Value]);
  end;

  function Join(const ARefs: TSpeciesRefs): string;
  var
    K: Integer;
  begin
    Result := '';
    for K := 0 to High(ARefs) do
    begin
      if K > 0 then Result := Result + ' + ';
      Result := Result + RefText(ARefs[K]);
    end;
    if Result = '' then Result := '(none)';
  end;

begin
  SB := TStringBuilder.Create;
  try
    SB.AppendFormat('%d reaction(s); symbol kinds %s',
      [AModel.ReactionCount,
       BoolToStr(AModel.KnowsSymbolKinds, True).ToLower]).AppendLine;

    for I := 0 to AModel.ReactionCount - 1 do
    begin
      SB.AppendLine;
      SB.AppendFormat('  %s   (line %d)',
        [AModel.ReactionId(I), AModel.SourceLineOf(I)]).AppendLine;
      SB.AppendFormat('    rate law : %s', [AModel.RateLawText(I)]).AppendLine;

      Refs := AModel.Reactants(I);
      SB.AppendFormat('    reactants: %s', [Join(Refs)]).AppendLine;
      Refs := AModel.Products(I);
      SB.AppendFormat('    products : %s', [Join(Refs)]).AppendLine;

      Mods := AModel.Modifiers(I);
      if Length(Mods) > 0 then
        for J := 0 to High(Mods) do
          SB.AppendFormat('    modifier : %s (%s)',
            [Mods[J].Name, ModifierRoleName(Mods[J].Role)]).AppendLine;
    end;
    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

end.
