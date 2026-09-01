unit RateLaw.Registry;

{ The rate law registry: the data that makes this a generic checker rather
  than a pile of per-law code.

  Storage is JSON, not the YAML the original specification proposed. There is
  no YAML parser in the Delphi RTL and writing one is a project in itself,
  while System.JSON is already the house format. The field names are kept
  exactly as the YAML draft had them, so the two are mechanically
  interconvertible and a future standalone tool can read the same registry.

  Three layers, later overriding earlier BY ID:

    1. Built-in    compiled in (RateLaw.BuiltInLaws)
    2. User        a directory of .json files
    3. Project     a directory beside the model, so a model repository can
                   carry its own law set and have it travel in version control

  A built-in is never deleted, only disabled or shadowed. That is what makes a
  bad edit recoverable by deleting one file.

  SELF-VALIDATION (specification 7.3)
  -----------------------------------
  Every entry is validated as it loads, and an invalid entry does not
  participate in checking. This is not tidiness. A bad registry entry produces
  false positives on EVERY model checked afterwards, and the user has no way
  to tell that the tool is wrong rather than their model. Rejecting at load is
  the only point at which the blame is still legible.

  Both halves are done. Structural validation lives here; checking that a
  law's canonical expression actually SATISFIES its own declared invariants
  needs the numeric evaluator, so RateLaw.Dynamic installs itself through
  SetInvariantValidator and AddFromJsonText runs both. An entry that fails
  either does not participate in checking.

  A GENERATIVE entry is exempt from the second half: 'k * prod(Si^ai)' is a
  shape rather than an expression and cannot be evaluated until a reaction
  instantiates it, so its invariants are checked there instead. }

interface

uses
  System.SysUtils, System.Classes, System.JSON, System.IOUtils, System.Math,
  System.Generics.Collections,
  RateLaw.Types, RateLaw.Ast, RateLaw.Parser, RateLaw.Canonical;

type
  TRoleKind = (rkSpecies, rkParameter, rkCompartment);

  TSpeciesPosition = (spUnspecified, spSubstrate, spProduct, spModifier,
                      spInhibitor, spActivator);

  TRole = record
    Name:        string;
    Kind:        TRoleKind;
    Position:    TSpeciesPosition;   // species only
    Cardinality: string;             // '1', a number, or 'n' for generative
    Semantics:   string;             // 'max_rate', 'half_saturation', ...
    Positive:    Boolean;
    IsInteger:   Boolean;
    { Names a modeller might plausibly use for this role. Drives role binding
      and the S011 naming-convention warning. }
    Aliases:     TArray<string>;
    { For a cardinality-'n' role: the symbol standing for the per-instance
      exponent. Without it the validator cannot tell an index variable from
      an undeclared identifier. }
    Exponent:    string;
    { Set only on the roles of an instantiated generative law, where the role
      IS a particular model species and there is nothing to choose. A normal
      law's species roles are still bound by structure and then by shape --
      permuting them is how a genuine substrate swap is detected, and fixing
      them by name would hide it. }
    BindsToSelf: Boolean;
    function IsIndexed: Boolean;
  end;

  TInvariantKind = (ivUnknown, ivZeroAt, ivZeroAtAnyZero, ivNonNegative,
                    ivMonotonic, ivBoundedAbove, ivLimit, ivValueAt,
                    ivSigmoidal, ivHomogeneous, ivSymmetric);

  TPointEntry = record
    Name: string;
    Expr: string;
  end;

  { The union of the fields the ten invariant types use. A record with unused
    fields is easier to validate and to read than a bag of JSON, and the
    vocabulary is fixed by the specification rather than open-ended. }
  TInvariant = record
    Kind:      TInvariantKind;
    RawType:   string;
    Vars:      TArray<string>;      // 'var' or 'vars'
    Point:     TArray<TPointEntry>; // 'point'
    DomainVar: string;
    DomainLo:  string;
    DomainHi:  string;
    Direction: string;              // 'increasing' | 'decreasing'
    Toward:    string;              // '0' | 'inf'
    EqualsExpr: string;
    Degree:    string;
    WhenExpr:  string;
    function Describe: string;
  end;

  TSampling = record
    Name:  string;
    Scale: string;    // 'log' | 'linear'
    Lo:    string;
    Hi:    string;
    N:     Integer;
  end;

  TApplicability = record
    HasReactants:  Boolean;
    Reactants:     string;     // '1', '>=1', '2'...
    HasProducts:   Boolean;
    Products:      string;
    { Symmetric with the two above, and needed by any law whose rate depends
      on a species that is neither consumed nor produced. Catalytic mass
      action instantiates to k*prod(Si) when a reaction has no modifiers,
      which is mass action exactly -- so without this the two laws tie on
      every ordinary reaction and neither is applied. }
    HasModifiers:  Boolean;
    Modifiers:     string;
    ExponentsFrom: string;     // 'stoichiometry' or ''
  end;

  TRegistryLayer = (rlBuiltIn, rlUser, rlProject);

  TRateLawDef = class
  private
    FRoles: TList<TRole>;
    FInvariants: TList<TInvariant>;
    FSampling: TList<TSampling>;
    FTolerances: TDictionary<string, Double>;
    FExpr: TAstNode;
    FCanon: TAstNode;
    function GetRoleCount: Integer;
    function GetRole(AIndex: Integer): TRole;
  public
    Id:          string;
    LawName:     string;
    Version:     Integer;
    Enabled:     Boolean;
    Generative:  Boolean;
    Expression:  string;
    Notes:       string;
    { How far a reaction may sit from THIS law and still be associated with
      it. 0 means "use the registry-wide floor", which is what every law
      written before this field existed means by saying nothing.

      It exists because looseness is a property of the law, not of the
      registry. "k times some species" sits near a great deal: catalytic mass
      action, admitted on the ordinary floor, claimed 121 saturating rate
      laws and 57 that are sums rather than products, and reported defects
      against every one of them. A tight law like ordered bi-bi has no such
      problem and should not be penalised for its neighbour's appetite. }
    AssociationFloor: Double;
    Applicability: TApplicability;
    Layer:       TRegistryLayer;
    SourcePath:  string;
    { False when validation rejected it. Kept in the registry so 'list' can
      show it and say why, rather than an entry silently vanishing. }
    Valid:       Boolean;
    Problems:    TArray<string>;

    constructor Create;
    destructor  Destroy; override;

    function IndexOfRole(const AName: string): Integer;
    function FindRole(const AName: string; out ARole: TRole): Boolean;
    { True when AName is a role name or one of its declared aliases. }
    function RoleForAlias(const AName: string; out ARole: TRole): Boolean;
    { Every name the expression may legitimately mention: role names plus, for
      a generative law, the index and exponent symbols. }
    function LegalIdentifiers: TArray<string>;

    property Roles[AIndex: Integer]: TRole read GetRole;
    property RoleCount: Integer read GetRoleCount;
    property Invariants: TList<TInvariant> read FInvariants;
    property Sampling: TList<TSampling> read FSampling;
    property Tolerances: TDictionary<string, Double> read FTolerances;
    { Parsed as written, and canonicalised. Both are kept for the same reason
      the model's two trees are. nil when the expression would not parse. }
    property Expr: TAstNode read FExpr;
    property Canon: TAstNode read FCanon;

    function ToJson: TJSONObject;
    function ToJsonText: string;

    { Construction, for a law built in code rather than parsed from JSON --
      a generative law instantiated for one reaction, or a registry editor
      assembling an entry before saving it. }
    procedure AddRole(const ARole: TRole);
    procedure ClearRoles;
    { Parses AText and keeps both trees. False when it will not parse, in
      which case the law is left with no expression rather than a stale one. }
    function  SetExpression(const AText: string): Boolean;
  end;

  { Set by RateLaw.Dynamic at unit initialisation. The registry cannot call
    the dynamic engine directly -- the dynamic engine needs the registry's
    types -- and this is the seam that lets the dependency run one way while
    the behaviour runs the other. A registry loaded without the dynamic unit
    linked in still validates structurally. }
  TInvariantValidator = procedure (ALaw: TRateLawDef;
                                   ADiags: TRateLawDiagnostics);

  TRateLawRegistry = class
  private
    FLaws: TObjectList<TRateLawDef>;
    FLoadDiagnostics: TRateLawDiagnostics;
    function GetCount: Integer;
    function GetLaw(AIndex: Integer): TRateLawDef;
    procedure Upsert(ALaw: TRateLawDef);
  public
    constructor Create;
    destructor  Destroy; override;

    procedure Clear;
    procedure LoadBuiltIns;
    { Every *.json in the directory. A missing directory is not an error --
      the user layer and the project layer are both optional by design. }
    procedure LoadDirectory(const APath: string; ALayer: TRegistryLayer);
    { Built-ins, then user, then project. Either path may be ''. }
    procedure LoadDefaults(const AUserDir, AProjectDir: string);

    function  AddFromJsonText(const AJson: string; ALayer: TRegistryLayer;
                              const ASourcePath: string = ''): TRateLawDef;
    function  Find(const AId: string): TRateLawDef;
    function  Remove(const AId: string): Boolean;
    function  SetEnabled(const AId: string; AEnabled: Boolean): Boolean;
    function  Enable(const AId: string): Boolean;
    function  Disable(const AId: string): Boolean;

    { Ids of the laws that will actually participate: enabled and valid. }
    function  ActiveIds: TArray<string>;
    function  ActiveCount: Integer;

    procedure SaveToDirectory(const APath: string);
    function  ExportToText: string;

    { Diagnostics accumulated during loading -- R-codes, one set per load. }
    property  LoadDiagnostics: TRateLawDiagnostics read FLoadDiagnostics;
    property  Count: Integer read GetCount;
    property  Laws[AIndex: Integer]: TRateLawDef read GetLaw; default;
  end;

type
  { An applicability count, written as a bare number or a comparison:
    "1", "2", ">=1", "<=2", ">0". Used for reactant and product counts. }
  TCountConstraint = record
    Op:    string;      // '=', '>=', '<=', '>', '<'
    Value: Integer;
    function Matches(ACount: Integer): Boolean;
    function AsText: string;
  end;

function TryParseConstraint(const AText: string;
                            out AConstraint: TCountConstraint): Boolean; overload;
function TryParseConstraint(const AText: string): Boolean; overload;

{ Validates one definition, appending R-code diagnostics. Returns True when
  the entry may participate in checking. Public so a registry editor can check
  an entry before saving it. }
function ValidateLawDef(ALaw: TRateLawDef;
                        ADiags: TRateLawDiagnostics): Boolean;

function RoleKindName(AKind: TRoleKind): string;
function PositionName(APos: TSpeciesPosition): string;
function InvariantKindFromText(const AText: string): TInvariantKind;

{ Installed by RateLaw.Dynamic. }
procedure SetInvariantValidator(AValidator: TInvariantValidator);

implementation

uses
  RateLaw.BuiltInLaws, System.StrUtils;

var
  GInv: TFormatSettings;
  FInvariantValidator: TInvariantValidator = nil;

procedure SetInvariantValidator(AValidator: TInvariantValidator);
begin
  FInvariantValidator := AValidator;
end;

{ ------------------------------------------------------------------ helpers }

function RoleKindName(AKind: TRoleKind): string;
begin
  case AKind of
    rkSpecies:     Result := 'species';
    rkParameter:   Result := 'parameter';
  else             Result := 'compartment';
  end;
end;

function RoleKindFromText(const AText: string; out AKind: TRoleKind): Boolean;
begin
  Result := True;
  if SameText(AText, 'species') then AKind := rkSpecies
  else if SameText(AText, 'parameter') then AKind := rkParameter
  else if SameText(AText, 'compartment') then AKind := rkCompartment
  else begin AKind := rkParameter; Result := False; end;
end;

function PositionName(APos: TSpeciesPosition): string;
begin
  case APos of
    spSubstrate: Result := 'substrate';
    spProduct:   Result := 'product';
    spModifier:  Result := 'modifier';
    spInhibitor: Result := 'inhibitor';
    spActivator: Result := 'activator';
  else           Result := '';
  end;
end;

function PositionFromText(const AText: string; out APos: TSpeciesPosition): Boolean;
begin
  Result := True;
  if AText = '' then APos := spUnspecified
  else if SameText(AText, 'substrate') then APos := spSubstrate
  else if SameText(AText, 'product') then APos := spProduct
  else if SameText(AText, 'modifier') then APos := spModifier
  else if SameText(AText, 'inhibitor') then APos := spInhibitor
  else if SameText(AText, 'activator') then APos := spActivator
  else begin APos := spUnspecified; Result := False; end;
end;

function InvariantKindFromText(const AText: string): TInvariantKind;
begin
  if SameText(AText, 'zero_at') then Result := ivZeroAt
  else if SameText(AText, 'zero_at_any_zero') then Result := ivZeroAtAnyZero
  else if SameText(AText, 'nonnegative') then Result := ivNonNegative
  else if SameText(AText, 'monotonic') then Result := ivMonotonic
  else if SameText(AText, 'bounded_above') then Result := ivBoundedAbove
  else if SameText(AText, 'limit') then Result := ivLimit
  else if SameText(AText, 'value_at') then Result := ivValueAt
  else if SameText(AText, 'sigmoidal') then Result := ivSigmoidal
  else if SameText(AText, 'homogeneous') then Result := ivHomogeneous
  else if SameText(AText, 'symmetric') then Result := ivSymmetric
  else Result := ivUnknown;
end;

{ JSON readers that tolerate a number written as a string and vice versa.
  Hand-authored registry files will do both, and rejecting "n": "64" when
  "n": 64 was meant is a pointless obstacle to authoring a law. }
function JStr(AObj: TJSONObject; const AName: string;
              const ADefault: string = ''): string;
var
  V: TJSONValue;
begin
  Result := ADefault;
  if AObj = nil then Exit;
  V := AObj.Values[AName];
  if V = nil then Exit;
  if V is TJSONString then Result := TJSONString(V).Value
  else Result := V.ToString;
end;

function JBool(AObj: TJSONObject; const AName: string;
               ADefault: Boolean): Boolean;
var
  V: TJSONValue;
begin
  Result := ADefault;
  if AObj = nil then Exit;
  V := AObj.Values[AName];
  if V = nil then Exit;
  if V is TJSONBool then Result := TJSONBool(V).AsBoolean
  else Result := SameText(JStr(AObj, AName), 'true');
end;

function JInt(AObj: TJSONObject; const AName: string; ADefault: Integer): Integer;
var
  S: string;
begin
  S := JStr(AObj, AName);
  if (S = '') or not TryStrToInt(S, Result) then
    Result := ADefault;
end;

function JObj(AObj: TJSONObject; const AName: string): TJSONObject;
var
  V: TJSONValue;
begin
  Result := nil;
  if AObj = nil then Exit;
  V := AObj.Values[AName];
  if V is TJSONObject then Result := TJSONObject(V);
end;

function JArr(AObj: TJSONObject; const AName: string): TJSONArray;
var
  V: TJSONValue;
begin
  Result := nil;
  if AObj = nil then Exit;
  V := AObj.Values[AName];
  if V is TJSONArray then Result := TJSONArray(V);
end;

function JFloat(AObj: TJSONObject; const AName: string;
                ADefault: Double): Double;
var
  S: string;
begin
  S := JStr(AObj, AName);
  if (S = '') or not TryStrToFloat(S, Result, TFormatSettings.Invariant) then
    Result := ADefault;
end;

function JStrArray(AObj: TJSONObject; const AName: string): TArray<string>;
var
  A: TJSONArray;
  I: Integer;
  V: TJSONValue;
begin
  Result := nil;
  A := JArr(AObj, AName);
  if A = nil then
  begin
    { A single string where a list was expected is a common and harmless
      shorthand ("vars": "Si"), so accept it. }
    if (AObj <> nil) and (AObj.Values[AName] is TJSONString) then
      Result := [TJSONString(AObj.Values[AName]).Value];
    Exit;
  end;
  SetLength(Result, A.Count);
  for I := 0 to A.Count - 1 do
  begin
    V := A.Items[I];
    if V is TJSONString then Result[I] := TJSONString(V).Value
    else Result[I] := V.ToString;
  end;
end;

{ ------------------------------------------------------ TCountConstraint }

function TCountConstraint.Matches(ACount: Integer): Boolean;
begin
  if Op = '>=' then Result := ACount >= Value
  else if Op = '<=' then Result := ACount <= Value
  else if Op = '>'  then Result := ACount >  Value
  else if Op = '<'  then Result := ACount <  Value
  else Result := ACount = Value;
end;

function TCountConstraint.AsText: string;
begin
  if Op = '=' then Result := IntToStr(Value)
  else Result := Op + IntToStr(Value);
end;

function TryParseConstraint(const AText: string;
  out AConstraint: TCountConstraint): Boolean;
var
  S: string;
begin
  AConstraint := Default(TCountConstraint);
  S := Trim(AText);
  if S = '' then Exit(False);

  { Two-character operators first, or ">=1" would be read as ">" followed by
    "=1" and the "=" would fail to convert. }
  if S.StartsWith('>=') then begin AConstraint.Op := '>='; S := S.Substring(2); end
  else if S.StartsWith('<=') then begin AConstraint.Op := '<='; S := S.Substring(2); end
  else if S.StartsWith('>') then begin AConstraint.Op := '>'; S := S.Substring(1); end
  else if S.StartsWith('<') then begin AConstraint.Op := '<'; S := S.Substring(1); end
  else if S.StartsWith('=') then begin AConstraint.Op := '='; S := S.Substring(1); end
  else AConstraint.Op := '=';

  Result := TryStrToInt(Trim(S), AConstraint.Value) and (AConstraint.Value >= 0);
end;

function TryParseConstraint(const AText: string): Boolean;
var
  C: TCountConstraint;
begin
  Result := TryParseConstraint(AText, C);
end;

{ ----------------------------------------------------------------- TRole }

function TRole.IsIndexed: Boolean;
begin
  Result := SameText(Cardinality, 'n');
end;

{ ------------------------------------------------------------ TInvariant }

function TInvariant.Describe: string;
var
  I: Integer;
begin
  Result := RawType;
  if Length(Vars) > 0 then
    Result := Result + ' [' + string.Join(', ', Vars) + ']';
  if Length(Point) > 0 then
  begin
    Result := Result + ' at ';
    for I := 0 to High(Point) do
    begin
      if I > 0 then Result := Result + ', ';
      Result := Result + Point[I].Name + '=' + Point[I].Expr;
    end;
  end;
  if DomainVar <> '' then
    Result := Result + Format(' over %s in [%s, %s]', [DomainVar, DomainLo, DomainHi]);
  if Direction <> '' then Result := Result + ' ' + Direction;
  if Toward <> '' then Result := Result + ' as -> ' + Toward;
  if EqualsExpr <> '' then Result := Result + ' equals ' + EqualsExpr;
  if Degree <> '' then Result := Result + ' degree ' + Degree;
  if WhenExpr <> '' then Result := Result + ' when ' + WhenExpr;
end;

{ ---------------------------------------------------------- TRateLawDef }

constructor TRateLawDef.Create;
begin
  inherited Create;
  FRoles      := TList<TRole>.Create;
  FInvariants := TList<TInvariant>.Create;
  FSampling   := TList<TSampling>.Create;
  FTolerances := TDictionary<string, Double>.Create;
  Version     := 1;
  Enabled     := True;
  Valid       := True;
end;

destructor TRateLawDef.Destroy;
begin
  FCanon.Free;
  FExpr.Free;
  FTolerances.Free;
  FSampling.Free;
  FInvariants.Free;
  FRoles.Free;
  inherited;
end;

function TRateLawDef.GetRoleCount: Integer;
begin
  Result := FRoles.Count;
end;

function TRateLawDef.GetRole(AIndex: Integer): TRole;
begin
  Result := FRoles[AIndex];
end;

function TRateLawDef.IndexOfRole(const AName: string): Integer;
var
  I: Integer;
begin
  for I := 0 to FRoles.Count - 1 do
    if FRoles[I].Name = AName then     { case sensitive: model identifiers are }
      Exit(I);
  Result := -1;
end;

function TRateLawDef.FindRole(const AName: string; out ARole: TRole): Boolean;
var
  I: Integer;
begin
  I := IndexOfRole(AName);
  Result := I >= 0;
  if Result then ARole := FRoles[I] else ARole := Default(TRole);
end;

function TRateLawDef.RoleForAlias(const AName: string; out ARole: TRole): Boolean;
var
  R: TRole;
  A: string;
begin
  if FindRole(AName, ARole) then Exit(True);
  for R in FRoles do
    for A in R.Aliases do
      if SameText(A, AName) then
      begin
        ARole := R;
        Exit(True);
      end;
  ARole := Default(TRole);
  Result := False;
end;

function TRateLawDef.LegalIdentifiers: TArray<string>;
var
  L: TStringList;
  R: TRole;
  I: Integer;
begin
  L := TStringList.Create;
  try
    L.Sorted := True;
    L.Duplicates := dupIgnore;
    for R in FRoles do
    begin
      L.Add(R.Name);
      if R.IsIndexed and (R.Exponent <> '') then
        L.Add(R.Exponent);
    end;
    SetLength(Result, L.Count);
    for I := 0 to L.Count - 1 do Result[I] := L[I];
  finally
    L.Free;
  end;
end;

function TRateLawDef.ToJson: TJSONObject;
var
  RolesObj, NamesObj, SampObj, TolObj, AppObj, RObj, SObj, PtObj: TJSONObject;
  InvArr, RangeArr: TJSONArray;
  InvObj: TJSONObject;
  R: TRole;
  Inv: TInvariant;
  Smp: TSampling;
  Pair: TPair<string, Double>;
  A: string;
  Arr: TJSONArray;
  P: TPointEntry;
  HasNames: Boolean;
begin
  Result := TJSONObject.Create;
  Result.AddPair('id', Id);
  Result.AddPair('name', LawName);
  Result.AddPair('version', TJSONNumber.Create(Version));
  Result.AddPair('enabled', TJSONBool.Create(Enabled));
  if Generative then
    Result.AddPair('generative', TJSONBool.Create(True));
  Result.AddPair('expression', Expression);

  RolesObj := TJSONObject.Create;
  NamesObj := TJSONObject.Create;
  HasNames := False;
  for R in FRoles do
  begin
    RObj := TJSONObject.Create;
    RObj.AddPair('kind', RoleKindName(R.Kind));
    if PositionName(R.Position) <> '' then
      RObj.AddPair('position', PositionName(R.Position));
    if R.Cardinality <> '' then RObj.AddPair('cardinality', R.Cardinality);
    if R.Semantics <> '' then RObj.AddPair('semantics', R.Semantics);
    if R.Positive then RObj.AddPair('positive', TJSONBool.Create(True));
    if R.IsInteger then RObj.AddPair('integer', TJSONBool.Create(True));
    if R.Exponent <> '' then RObj.AddPair('exponent', R.Exponent);
    { BindsToSelf is deliberately not written: it belongs to an instantiated
      law, which is transient and never saved. }
    RolesObj.AddPair(R.Name, RObj);

    if Length(R.Aliases) > 0 then
    begin
      HasNames := True;
      Arr := TJSONArray.Create;
      for A in R.Aliases do Arr.Add(A);
      NamesObj.AddPair(R.Name, Arr);
    end;
  end;
  Result.AddPair('roles', RolesObj);
  if HasNames then Result.AddPair('naming_conventions', NamesObj)
  else NamesObj.Free;

  if Applicability.HasReactants or Applicability.HasProducts
     or (Applicability.ExponentsFrom <> '') then
  begin
    AppObj := TJSONObject.Create;
    if Applicability.HasReactants then
      AppObj.AddPair('reactants', Applicability.Reactants);
    if Applicability.HasProducts then
      AppObj.AddPair('products', Applicability.Products);
      if Applicability.HasModifiers then
        AppObj.AddPair('modifiers', Applicability.Modifiers);
    if Applicability.ExponentsFrom <> '' then
      AppObj.AddPair('exponents_from', Applicability.ExponentsFrom);
    Result.AddPair('applicability', AppObj);
  end;

  if FInvariants.Count > 0 then
  begin
    InvArr := TJSONArray.Create;
    for Inv in FInvariants do
    begin
      InvObj := TJSONObject.Create;
      InvObj.AddPair('type', Inv.RawType);
      if Length(Inv.Vars) = 1 then
        InvObj.AddPair('var', Inv.Vars[0])
      else if Length(Inv.Vars) > 1 then
      begin
        Arr := TJSONArray.Create;
        for A in Inv.Vars do Arr.Add(A);
        InvObj.AddPair('vars', Arr);
      end;
      if Length(Inv.Point) > 0 then
      begin
        PtObj := TJSONObject.Create;
        for P in Inv.Point do PtObj.AddPair(P.Name, P.Expr);
        InvObj.AddPair('point', PtObj);
      end;
      if Inv.DomainVar <> '' then
      begin
        SObj := TJSONObject.Create;
        RangeArr := TJSONArray.Create;
        RangeArr.Add(Inv.DomainLo);
        RangeArr.Add(Inv.DomainHi);
        SObj.AddPair(Inv.DomainVar, RangeArr);
        InvObj.AddPair('domain', SObj);
      end;
      if Inv.Direction <> '' then InvObj.AddPair('direction', Inv.Direction);
      if Inv.Toward <> '' then InvObj.AddPair('to', Inv.Toward);
      if Inv.EqualsExpr <> '' then InvObj.AddPair('equals', Inv.EqualsExpr);
      if Inv.Degree <> '' then InvObj.AddPair('degree', Inv.Degree);
      if Inv.WhenExpr <> '' then InvObj.AddPair('when', Inv.WhenExpr);
      InvArr.Add(InvObj);
    end;
    Result.AddPair('invariants', InvArr);
  end;

  if FSampling.Count > 0 then
  begin
    SampObj := TJSONObject.Create;
    for Smp in FSampling do
    begin
      SObj := TJSONObject.Create;
      SObj.AddPair('scale', Smp.Scale);
      RangeArr := TJSONArray.Create;
      RangeArr.Add(Smp.Lo);
      RangeArr.Add(Smp.Hi);
      SObj.AddPair('range', RangeArr);
      SObj.AddPair('n', TJSONNumber.Create(Smp.N));
      SampObj.AddPair(Smp.Name, SObj);
    end;
    Result.AddPair('sampling', SampObj);
  end;

  if FTolerances.Count > 0 then
  begin
    TolObj := TJSONObject.Create;
    for Pair in FTolerances do
      TolObj.AddPair(Pair.Key, TJSONNumber.Create(Pair.Value));
    Result.AddPair('tolerances', TolObj);
  end;

  if Notes <> '' then Result.AddPair('notes', Notes);
  if AssociationFloor > 0 then
    Result.AddPair('association_floor',
      TJSONNumber.Create(AssociationFloor));
end;

procedure TRateLawDef.AddRole(const ARole: TRole);
begin
  FRoles.Add(ARole);
end;

procedure TRateLawDef.ClearRoles;
begin
  FRoles.Clear;
end;

function TRateLawDef.SetExpression(const AText: string): Boolean;
var
  Err: string;
begin
  FreeAndNil(FCanon);
  FreeAndNil(FExpr);
  Expression := '';

  Result := TryParseRateLaw(AText, FExpr, Err);
  if Result then
  begin
    Expression := AText;
    FCanon := Canonicalise(FExpr);
  end;
end;

function TRateLawDef.ToJsonText: string;
var
  O: TJSONObject;
begin
  O := ToJson;
  try
    Result := O.Format(2);
  finally
    O.Free;
  end;
end;

{ ------------------------------------------------------------- parse a law }

function ParseLawDef(const AJson: string; out ALaw: TRateLawDef;
                     out AError: string): Boolean;
var
  Root, RolesObj, NamesObj, SampObj, TolObj, AppObj, RObj, SObj, PtObj,
  DomObj, InvObj: TJSONObject;
  V: TJSONValue;
  InvArr, RangeArr: TJSONArray;
  Pair: TJSONPair;
  R: TRole;
  Inv: TInvariant;
  Smp: TSampling;
  P: TPointEntry;
  I, J: Integer;
  D: Double;
  RK: TRoleKind;
  Pos: TSpeciesPosition;
begin
  ALaw   := nil;
  AError := '';

  V := TJSONObject.ParseJSONValue(AJson);
  if not (V is TJSONObject) then
  begin
    V.Free;
    AError := 'not a JSON object';
    Exit(False);
  end;

  Root := TJSONObject(V);
  ALaw := TRateLawDef.Create;
  try
    ALaw.Id         := JStr(Root, 'id');
    ALaw.LawName    := JStr(Root, 'name');
    ALaw.Version    := JInt(Root, 'version', 1);
    ALaw.Enabled    := JBool(Root, 'enabled', True);
    ALaw.Generative := JBool(Root, 'generative', False);
    ALaw.Expression := JStr(Root, 'expression');
    ALaw.Notes      := JStr(Root, 'notes');
    ALaw.AssociationFloor := JFloat(Root, 'association_floor', 0);

    { roles }
    RolesObj := JObj(Root, 'roles');
    NamesObj := JObj(Root, 'naming_conventions');
    if RolesObj <> nil then
      for I := 0 to RolesObj.Count - 1 do
      begin
        Pair := RolesObj.Pairs[I];
        RObj := nil;
        if Pair.JsonValue is TJSONObject then RObj := TJSONObject(Pair.JsonValue);

        R := Default(TRole);
        R.Name := Pair.JsonString.Value;
        if not RoleKindFromText(JStr(RObj, 'kind', 'parameter'), RK) then
          RK := rkParameter;
        R.Kind := RK;
        if not PositionFromText(JStr(RObj, 'position'), Pos) then
          Pos := spUnspecified;
        R.Position    := Pos;
        R.Cardinality := JStr(RObj, 'cardinality', '1');
        R.Semantics   := JStr(RObj, 'semantics');
        R.Positive    := JBool(RObj, 'positive', False);
        R.IsInteger   := JBool(RObj, 'integer', False);
        R.Exponent    := JStr(RObj, 'exponent');
        if NamesObj <> nil then
          R.Aliases := JStrArray(NamesObj, R.Name);
        ALaw.FRoles.Add(R);
      end;

    { applicability }
    AppObj := JObj(Root, 'applicability');
    if AppObj <> nil then
    begin
      ALaw.Applicability.HasReactants := AppObj.Values['reactants'] <> nil;
      ALaw.Applicability.Reactants    := JStr(AppObj, 'reactants');
      ALaw.Applicability.HasProducts  := AppObj.Values['products'] <> nil;
      ALaw.Applicability.Products     := JStr(AppObj, 'products');
      ALaw.Applicability.HasModifiers := AppObj.Values['modifiers'] <> nil;
      ALaw.Applicability.Modifiers    := JStr(AppObj, 'modifiers');
      ALaw.Applicability.ExponentsFrom := JStr(AppObj, 'exponents_from');
    end;

    { invariants }
    InvArr := JArr(Root, 'invariants');
    if InvArr <> nil then
      for I := 0 to InvArr.Count - 1 do
      begin
        if not (InvArr.Items[I] is TJSONObject) then Continue;
        InvObj := TJSONObject(InvArr.Items[I]);

        Inv := Default(TInvariant);
        Inv.RawType := JStr(InvObj, 'type');
        Inv.Kind    := InvariantKindFromText(Inv.RawType);

        if InvObj.Values['var'] <> nil then
          Inv.Vars := [JStr(InvObj, 'var')]
        else
          Inv.Vars := JStrArray(InvObj, 'vars');

        PtObj := JObj(InvObj, 'point');
        if PtObj <> nil then
          for J := 0 to PtObj.Count - 1 do
          begin
            P.Name := PtObj.Pairs[J].JsonString.Value;
            if PtObj.Pairs[J].JsonValue is TJSONString then
              P.Expr := TJSONString(PtObj.Pairs[J].JsonValue).Value
            else
              P.Expr := PtObj.Pairs[J].JsonValue.ToString;
            Inv.Point := Inv.Point + [P];
          end;

        DomObj := JObj(InvObj, 'domain');
        if (DomObj <> nil) and (DomObj.Count > 0) then
        begin
          Inv.DomainVar := DomObj.Pairs[0].JsonString.Value;
          if DomObj.Pairs[0].JsonValue is TJSONArray then
          begin
            RangeArr := TJSONArray(DomObj.Pairs[0].JsonValue);
            if RangeArr.Count > 0 then
              if RangeArr.Items[0] is TJSONString then
                Inv.DomainLo := TJSONString(RangeArr.Items[0]).Value
              else Inv.DomainLo := RangeArr.Items[0].ToString;
            if RangeArr.Count > 1 then
              if RangeArr.Items[1] is TJSONString then
                Inv.DomainHi := TJSONString(RangeArr.Items[1]).Value
              else Inv.DomainHi := RangeArr.Items[1].ToString;
          end;
        end;

        Inv.Direction  := JStr(InvObj, 'direction');
        Inv.Toward     := JStr(InvObj, 'to');
        Inv.EqualsExpr := JStr(InvObj, 'equals');
        Inv.Degree     := JStr(InvObj, 'degree');
        Inv.WhenExpr   := JStr(InvObj, 'when');
        ALaw.FInvariants.Add(Inv);
      end;

    { sampling }
    SampObj := JObj(Root, 'sampling');
    if SampObj <> nil then
      for I := 0 to SampObj.Count - 1 do
      begin
        if not (SampObj.Pairs[I].JsonValue is TJSONObject) then Continue;
        SObj := TJSONObject(SampObj.Pairs[I].JsonValue);
        Smp := Default(TSampling);
        Smp.Name  := SampObj.Pairs[I].JsonString.Value;
        Smp.Scale := JStr(SObj, 'scale', 'linear');
        Smp.N     := JInt(SObj, 'n', 32);
        RangeArr  := JArr(SObj, 'range');
        if (RangeArr <> nil) and (RangeArr.Count > 1) then
        begin
          if RangeArr.Items[0] is TJSONString then
            Smp.Lo := TJSONString(RangeArr.Items[0]).Value
          else Smp.Lo := RangeArr.Items[0].ToString;
          if RangeArr.Items[1] is TJSONString then
            Smp.Hi := TJSONString(RangeArr.Items[1]).Value
          else Smp.Hi := RangeArr.Items[1].ToString;
        end;
        ALaw.FSampling.Add(Smp);
      end;

    { tolerances }
    TolObj := JObj(Root, 'tolerances');
    if TolObj <> nil then
      for I := 0 to TolObj.Count - 1 do
        if TryStrToFloat(TolObj.Pairs[I].JsonValue.Value, D, GInv) then
          ALaw.FTolerances.AddOrSetValue(TolObj.Pairs[I].JsonString.Value, D);

    { The expression is parsed once, here, and both trees kept. A law whose
      expression will not parse is still returned -- validation reports it as
      R005 rather than the loader failing with no explanation. }
    if ALaw.Expression <> '' then
      if TryParseRateLaw(ALaw.Expression, ALaw.FExpr, AError) then
      begin
        ALaw.FCanon := Canonicalise(ALaw.FExpr);
        AError := '';
      end;

    Result := True;
  finally
    Root.Free;
  end;
end;

{ -------------------------------------------------------------- validation }

function ValidateLawDef(ALaw: TRateLawDef;
                        ADiags: TRateLawDiagnostics): Boolean;
var
  Idents, Legal: TArray<string>;
  Ident, A: string;
  R: TRole;
  Inv: TInvariant;
  Smp: TSampling;
  I: Integer;
  Node: TAstNode;
  Err: string;
  Fatal: Boolean;
  Seen: TStringList;

  procedure Problem(const ACode: string; ASeverity: TSeverity;
                    const AMessage: string);
  var
    D: TRateLawDiagnostic;
  begin
    D := Default(TRateLawDiagnostic);
    D.Code       := ACode;
    D.Severity   := ASeverity;
    D.LawId      := ALaw.Id;
    D.SourceLine := -1;
    D.Message    := AMessage;
    if ADiags <> nil then ADiags.Add(D);
    ALaw.Problems := ALaw.Problems + [ACode + ' ' + AMessage];
    if ASeverity = sevError then Fatal := True;
  end;

  function Known(const AName: string): Boolean;
  var
    K: string;
  begin
    for K in Legal do
      if K = AName then Exit(True);
    Result := False;
  end;

  { An expression appearing inside an invariant ('equals', a point value, a
    domain bound). It must parse, and it may mention only role names --
    otherwise the invariant silently refers to nothing. }
  procedure CheckExpr(const AWhat, AText: string);
  var
    N: TAstNode;
    E: string;
    Id: string;
  begin
    if Trim(AText) = '' then Exit;
    if SameText(AText, 'inf') or SameText(AText, '-inf') then Exit;
    if not TryParseRateLaw(AText, N, E) then
    begin
      Problem('R010', sevError,
        Format('%s: "%s" will not parse -- %s', [AWhat, AText, E]));
      Exit;
    end;
    try
      for Id in IdentifiersIn(N) do
        if not Known(Id) then
          Problem('R009', sevError,
            Format('%s: "%s" mentions "%s", which is not a role of this law',
                   [AWhat, AText, Id]));
    finally
      N.Free;
    end;
  end;

begin
  Fatal := False;
  ALaw.Problems := nil;

  { --- required fields --- }
  if Trim(ALaw.Id) = '' then
    Problem('R002', sevError, 'no "id"');
  if Trim(ALaw.LawName) = '' then
    Problem('R002', sevWarn, 'no "name"; reports will show the id instead');
  if Trim(ALaw.Expression) = '' then
    Problem('R002', sevError, 'no "expression"');
  if ALaw.RoleCount = 0 then
    Problem('R002', sevError, 'no "roles"');
  if ALaw.Version < 1 then
    Problem('R003', sevWarn, '"version" should be a positive integer');

  { --- the expression --- }
  if (ALaw.Expression <> '') and (ALaw.Expr = nil) then
  begin
    Node := nil;
    TryParseRateLaw(ALaw.Expression, Node, Err);
    Node.Free;   { nil on the failure path, but not worth assuming }
    Problem('R005', sevError,
      Format('"expression" will not parse -- %s', [Err]));
  end;

  Legal := ALaw.LegalIdentifiers;

  { --- duplicate role names --- }
  Seen := TStringList.Create;
  try
    Seen.Sorted := True;
    for I := 0 to ALaw.RoleCount - 1 do
    begin
      R := ALaw.Roles[I];
      if Seen.IndexOf(R.Name) >= 0 then
        Problem('R004', sevError, Format('role "%s" is declared twice', [R.Name]))
      else
        Seen.Add(R.Name);

      { A modifier is exempt: it has no stoichiometry, so there is no
        per-instance exponent to name. Requiring one made catalytic mass
        action and modifier-proportional kinetics warn at every load, and
        contradicted the authoring manual, which tells an author to omit the
        field exactly here. }
      if R.IsIndexed and (R.Exponent = '') and ALaw.Generative and
         not (R.Position in [spModifier, spActivator, spInhibitor]) then
        Problem('R003', sevWarn,
          Format('role "%s" has cardinality "n" but no "exponent" symbol, so '
               + 'its per-instance exponent cannot be named', [R.Name]));

      if (R.Kind <> rkSpecies) and (R.Position <> spUnspecified) then
        Problem('R003', sevWarn,
          Format('role "%s" is a %s but declares a species position "%s"',
                 [R.Name, RoleKindName(R.Kind), PositionName(R.Position)]));
    end;
  finally
    Seen.Free;
  end;

  { --- every identifier in the expression has a role, and vice versa --- }
  if ALaw.Expr <> nil then
  begin
    Idents := IdentifiersIn(ALaw.Expr);

    for Ident in Idents do
      if not Known(Ident) then
        Problem('R006', sevError,
          Format('the expression mentions "%s", which has no role. Every '
               + 'symbol in the expression must be declared, or role binding '
               + 'has nothing to bind it to', [Ident]));

    for I := 0 to ALaw.RoleCount - 1 do
    begin
      R := ALaw.Roles[I];
      if not MatchStr(R.Name, Idents) then
        Problem('R007', sevWarn,
          Format('role "%s" never appears in the expression', [R.Name]));
    end;
  end;

  { --- naming conventions --- }
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    R := ALaw.Roles[I];
    for A in R.Aliases do
      if Trim(A) = '' then
        Problem('R003', sevWarn,
          Format('role "%s" has an empty naming convention', [R.Name]));
  end;

  { --- invariants --- }
  for Inv in ALaw.Invariants do
  begin
    if Inv.Kind = ivUnknown then
      Problem('R011', sevError,
        Format('unknown invariant type "%s"', [Inv.RawType]));

    for A in Inv.Vars do
      if not Known(A) then
        Problem('R009', sevError,
          Format('invariant "%s" names variable "%s", which is not a role',
                 [Inv.RawType, A]));

    for I := 0 to High(Inv.Point) do
    begin
      if not Known(Inv.Point[I].Name) then
        Problem('R009', sevError,
          Format('invariant "%s" gives a point for "%s", which is not a role',
                 [Inv.RawType, Inv.Point[I].Name]));
      CheckExpr(Format('invariant "%s" point %s', [Inv.RawType, Inv.Point[I].Name]),
                Inv.Point[I].Expr);
    end;

    if Inv.DomainVar <> '' then
    begin
      if not Known(Inv.DomainVar) then
        Problem('R009', sevError,
          Format('invariant "%s" has a domain for "%s", which is not a role',
                 [Inv.RawType, Inv.DomainVar]));
      CheckExpr('domain lower bound', Inv.DomainLo);
      CheckExpr('domain upper bound', Inv.DomainHi);
    end;

    CheckExpr(Format('invariant "%s" equals', [Inv.RawType]), Inv.EqualsExpr);
    CheckExpr(Format('invariant "%s" degree', [Inv.RawType]), Inv.Degree);

    if (Inv.Direction <> '') and
       not (SameText(Inv.Direction, 'increasing') or
            SameText(Inv.Direction, 'decreasing')) then
      Problem('R003', sevError,
        Format('invariant "%s" direction must be increasing or decreasing, not "%s"',
               [Inv.RawType, Inv.Direction]));

    if (Inv.Toward <> '') and
       not (SameText(Inv.Toward, 'inf') or SameText(Inv.Toward, '0')) then
      Problem('R003', sevError,
        Format('invariant "%s" "to" must be 0 or inf, not "%s"',
               [Inv.RawType, Inv.Toward]));

    { Types that cannot mean anything without a variable. }
    if (Inv.Kind in [ivMonotonic, ivLimit, ivSigmoidal]) and
       (Length(Inv.Vars) = 0) then
      Problem('R003', sevError,
        Format('invariant "%s" needs a "var"', [Inv.RawType]));

    if (Inv.Kind in [ivLimit, ivValueAt, ivBoundedAbove]) and
       (Trim(Inv.EqualsExpr) = '') then
      Problem('R003', sevError,
        Format('invariant "%s" needs an "equals" expression', [Inv.RawType]));
  end;

  { --- sampling --- }
  for Smp in ALaw.Sampling do
  begin
    if not Known(Smp.Name) then
      Problem('R012', sevWarn,
        Format('sampling is given for "%s", which is not a role', [Smp.Name]));
    if not (SameText(Smp.Scale, 'log') or SameText(Smp.Scale, 'linear')) then
      Problem('R003', sevWarn,
        Format('sampling scale for "%s" should be log or linear, not "%s"',
               [Smp.Name, Smp.Scale]));
    if Smp.N < 2 then
      Problem('R003', sevWarn,
        Format('sampling for "%s" has n = %d; at least 2 points are needed',
               [Smp.Name, Smp.N]));
    { A log grid cannot start at zero, and silently clamping it would move the
      sample points somewhere the law was never asked about. }
    if SameText(Smp.Scale, 'log') and (Smp.Lo = '0') then
      Problem('R003', sevError,
        Format('sampling for "%s" is logarithmic but starts at 0', [Smp.Name]));
  end;

  { --- applicability --- }
  if ALaw.Applicability.HasReactants then
    if not TryParseConstraint(ALaw.Applicability.Reactants) then
      Problem('R013', sevError,
        Format('applicability reactants "%s" is not a count or a comparison',
               [ALaw.Applicability.Reactants]));
  if ALaw.Applicability.HasProducts then
    if not TryParseConstraint(ALaw.Applicability.Products) then
      Problem('R013', sevError,
        Format('applicability products "%s" is not a count or a comparison',
               [ALaw.Applicability.Products]));

  { --- specification 7.3: does the law satisfy its OWN invariants? ---

    Structural validation above says the entry is well formed. This says it is
    self-consistent, and it is the half that catches an author who declares a
    property their expression does not have -- which would then be reported as
    a defect in every model checked against it.

    Performed by the caller, after this returns, because it needs the numeric
    evaluator and this unit must stay free of it: the registry is loaded in
    places where nothing is being evaluated. TRateLawRegistry.AddFromJsonText
    wires the two together. }

  ALaw.Valid := not Fatal;
  Result := ALaw.Valid;
end;

{ ---------------------------------------------------------- TRateLawRegistry }

constructor TRateLawRegistry.Create;
begin
  inherited Create;
  FLaws := TObjectList<TRateLawDef>.Create(True);
  FLoadDiagnostics := TRateLawDiagnostics.Create;
end;

destructor TRateLawRegistry.Destroy;
begin
  FLoadDiagnostics.Free;
  FLaws.Free;
  inherited;
end;

procedure TRateLawRegistry.Clear;
begin
  FLaws.Clear;
  FLoadDiagnostics.Clear;
end;

function TRateLawRegistry.GetCount: Integer;
begin
  Result := FLaws.Count;
end;

function TRateLawRegistry.GetLaw(AIndex: Integer): TRateLawDef;
begin
  Result := FLaws[AIndex];
end;

function TRateLawRegistry.Find(const AId: string): TRateLawDef;
var
  L: TRateLawDef;
begin
  for L in FLaws do
    if SameText(L.Id, AId) then Exit(L);
  Result := nil;
end;

{ Later layers override earlier ones by id -- that is the whole point of the
  layering, so a user entry replaces a built-in rather than colliding with it. }
procedure TRateLawRegistry.Upsert(ALaw: TRateLawDef);
var
  Existing: TRateLawDef;
begin
  Existing := Find(ALaw.Id);
  if Existing <> nil then
    FLaws.Remove(Existing);
  FLaws.Add(ALaw);
end;

function TRateLawRegistry.AddFromJsonText(const AJson: string;
  ALayer: TRegistryLayer; const ASourcePath: string): TRateLawDef;
var
  Law: TRateLawDef;
  Err: string;
  Where: string;
  D: TRateLawDiagnostic;
begin
  Result := nil;
  if not ParseLawDef(AJson, Law, Err) then
  begin
    D := Default(TRateLawDiagnostic);
    D.Code       := 'R001';
    D.Severity   := sevError;
    D.SourceLine := -1;
    Where := ASourcePath;
    if Where = '' then Where := '<text>';
    D.Message    := Format('%s: %s', [Where, Err]);
    FLoadDiagnostics.Add(D);
    Exit;
  end;

  Law.Layer      := ALayer;
  Law.SourcePath := ASourcePath;

  { Structure first, then behaviour. A law whose expression will not even
    parse cannot be probed numerically, so the second check is skipped rather
    than made to fail twice for one cause. }
  if ValidateLawDef(Law, FLoadDiagnostics) and Assigned(FInvariantValidator) then
    FInvariantValidator(Law, FLoadDiagnostics);

  Upsert(Law);
  Result := Law;
end;

procedure TRateLawRegistry.LoadBuiltIns;
var
  B: TBuiltInLaw;
begin
  for B in BuiltInLaws do
    AddFromJsonText(B.Json, rlBuiltIn, '<built-in>');
end;

procedure TRateLawRegistry.LoadDirectory(const APath: string;
  ALayer: TRegistryLayer);
var
  F: string;
begin
  { A missing directory is not an error: both the user layer and the project
    layer are optional, and a checker that refuses to run because the user has
    never added a law of their own would be useless out of the box. }
  if (APath = '') or not TDirectory.Exists(APath) then Exit;

  for F in TDirectory.GetFiles(APath, '*.json') do
    try
      AddFromJsonText(TFile.ReadAllText(F, TEncoding.UTF8), ALayer, F);
    except
      on E: Exception do
        FLoadDiagnostics.Add('R001', sevError, '',
          Format('%s could not be read: %s', [F, E.Message]));
    end;
end;

procedure TRateLawRegistry.LoadDefaults(const AUserDir, AProjectDir: string);
begin
  Clear;
  LoadBuiltIns;
  LoadDirectory(AUserDir, rlUser);
  LoadDirectory(AProjectDir, rlProject);
end;

function TRateLawRegistry.Remove(const AId: string): Boolean;
var
  L: TRateLawDef;
begin
  L := Find(AId);
  Result := L <> nil;
  if Result then FLaws.Remove(L);
end;

function TRateLawRegistry.SetEnabled(const AId: string;
  AEnabled: Boolean): Boolean;
var
  L: TRateLawDef;
begin
  L := Find(AId);
  Result := L <> nil;
  if Result then L.Enabled := AEnabled;
end;

function TRateLawRegistry.Enable(const AId: string): Boolean;
begin
  Result := SetEnabled(AId, True);
end;

function TRateLawRegistry.Disable(const AId: string): Boolean;
begin
  Result := SetEnabled(AId, False);
end;

function TRateLawRegistry.ActiveIds: TArray<string>;
var
  L: TRateLawDef;
begin
  Result := nil;
  for L in FLaws do
    if L.Enabled and L.Valid then
      Result := Result + [L.Id];
end;

function TRateLawRegistry.ActiveCount: Integer;
begin
  Result := Length(ActiveIds);
end;

procedure TRateLawRegistry.SaveToDirectory(const APath: string);
var
  L: TRateLawDef;
begin
  if not TDirectory.Exists(APath) then
    TDirectory.CreateDirectory(APath);
  for L in FLaws do
    TFile.WriteAllText(TPath.Combine(APath, L.Id + '.json'),
                       L.ToJsonText, TEncoding.UTF8);
end;

function TRateLawRegistry.ExportToText: string;
var
  Arr: TJSONArray;
  L: TRateLawDef;
begin
  Arr := TJSONArray.Create;
  try
    for L in FLaws do
      Arr.Add(L.ToJson);
    Result := Arr.Format(2);
  finally
    Arr.Free;
  end;
end;

initialization
  GInv := TFormatSettings.Invariant;
  GInv.DecimalSeparator := '.';

end.
