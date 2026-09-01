unit RateLaw.Bind;

{ Role binding: deciding which model identifier plays which role in a law.

  This is the step that makes a generic checker possible. The law says
  "Vm * S / (Km + S)" in terms of roles; the model says "k1 * A / (k2 + A)" in
  terms of its own names. Nothing can be compared until the two vocabularies
  are lined up, and lining them up wrongly produces a confident, detailed,
  entirely spurious report.

  Two sources of evidence, and they are not equally trustworthy:

    Species roles bind from REACTION STRUCTURE. A substrate role binds to a
    reactant, a product role to a product, an inhibitor role to a species the
    model declared as an inhibitor. This is hard evidence -- the modeller
    stated it -- and it is not negotiable.

    Parameter roles bind from NAMES and then from SHAPE. Naming conventions
    are a hint, never a decision: a parameter called Km is probably the
    half-saturation constant, but a model that swapped two parameters would
    then bind by the wrong name and the swap would become invisible. So every
    permutation is scored by how well the resulting expression matches the
    law, and the name only breaks ties.

  That ordering is the whole design. Binding by name first and checking
  afterwards cannot detect a role swap, because the swap is exactly what the
  name-first binding undoes.

  A binding whose best fit required an unnatural name assignment -- putting
  the identifier literally called "Km" into the Vm role -- is recorded rather
  than silently accepted. It is a stronger signal of a role swap than the
  structural difference it produces, and more useful to report. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  System.Generics.Defaults, System.StrUtils,
  RateLaw.Types, RateLaw.Ast, RateLaw.Parser, RateLaw.Canonical,
  RateLaw.Registry, RateLaw.Generative, RateLaw.Diff;

type
  { How a role came to be bound, which is what a report needs in order to say
    why it believes what it believes. }
  TBindVia = (bvExactName,     // the model uses the role's own name
              bvAlias,         // a declared naming convention
              bvStructure,     // reaction stoichiometry or a declared modifier
              bvShape,         // chosen because it fit the expression best
              bvUnbound);

  TBindingEntry = record
    Role:      string;
    ModelName: string;
    Via:       TBindVia;
    function Describe: string;
  end;

  TBinding = class
  private
    FEntries: TList<TBindingEntry>;
    function GetEntry(AIndex: Integer): TBindingEntry;
    function GetCount: Integer;
  public
    { Structural distance after applying this binding, in [0, 1]. }
    Distance: Double;
    { Penalty for names that sit oddly in their slots. Breaks ties only. }
    NamePenalty: Double;
    { Roles bound to an identifier that is a declared alias of a DIFFERENT
      role. The strongest available signal of a role swap. }
    Suspicious: TArray<string>;
    { Roles the law declares that nothing in the model could fill. }
    Unbound: TArray<string>;
    { The expression uses exactly the law's symbols, the same number of times.
      Strong evidence that this IS the law, however far apart the two trees
      have ended up -- a misplaced parenthesis rearranges everything while
      changing no ingredient. }
    SameSymbols: Boolean;
    { Every symbol the expression uses is one of this law's. Weaker than
      SameSymbols and admits a candidate the distance alone rejects: a term
      left out removes symbols, so a defective copy no longer matches
      exactly, but it is still built from nothing but this law's vocabulary. }
    SymbolsSubset: Boolean;

    constructor Create;
    destructor  Destroy; override;
    procedure Add(const ARole, AModelName: string; AVia: TBindVia);
    function  ModelNameFor(const ARole: string): string;
    function  RoleFor(const AModelName: string): string;
    function  IsComplete: Boolean;
    function  Score: Double;
    function  AsMap: TDictionary<string, string>;   // model name -> role name
    function  Describe: string;
    property  Entries[AIndex: Integer]: TBindingEntry read GetEntry; default;
    property  Count: Integer read GetCount;
  end;

  TBindOutcome = (boBound,          // one clear best binding
                  boAmbiguous,      // two or more equally good
                  boIncomplete,     // a role nothing can fill
                  boNotApplicable,  // applicability rules this law out
                  boUnparsable,     // the reaction's rate law will not parse
                  boGenerative);    // a family law; instantiation is M11

  TBindResult = class
  private
    FCandidates: TObjectList<TBinding>;
    function GetBest: TBinding;
  public
    Outcome:    TBindOutcome;
    Reason:     string;
    LawId:      string;
    ReactionId: string;
    { The reaction's rate law, parsed and canonicalised, and the same tree
      with model names replaced by role names. Owned here, because the static
      engine will want all three and re-deriving them would risk deriving them
      differently. }
    RawTree:    TAstNode;
    CanonTree:  TAstNode;
    BoundTree:  TAstNode;
    { A generative law instantiated for this reaction, owned here. nil for an
      ordinary law. Everything downstream must compare against EffectiveLaw
      rather than the registry entry, or mass action would be diffed against
      "k * prod(Si^ai)" -- a shape, not an expression. }
    Instantiated: TRateLawDef;
    { True when a compartment volume was taken off the rate law's spine before
      anything compared it. Worth carrying because the trees above no longer
      match the text the modeller wrote, and a report that quotes them without
      saying so invites "that is not what my model says". }
    VolumeStripped: Boolean;
    constructor Create;
    destructor  Destroy; override;
    { The instantiated law where there is one, otherwise ADefault. }
    function EffectiveLaw(ADefault: TRateLawDef): TRateLawDef;
    property Candidates: TObjectList<TBinding> read FCandidates;
    property Best: TBinding read GetBest;
  end;

{ Binds one reaction against one law. Never raises: a model that cannot be
  bound is the normal case, not an error. }
function BindReaction(ALaw: TRateLawDef; const AModel: IModelSource;
                      AReactionIndex: Integer): TBindResult;

{ Applicability only -- cheap, and used to narrow the candidate laws before
  the expensive part. }
function LawApplies(ALaw: TRateLawDef; const AModel: IModelSource;
                    AReactionIndex: Integer; out AReason: string): Boolean;

function BindViaName(AVia: TBindVia): string;
function OutcomeName(AOutcome: TBindOutcome): string;

const
  { Above this, two bindings are treated as equally good and the result is
    ambiguous rather than a guess. Deliberately small: bindings of the same
    law differ only by which name is in which slot, so a real winner wins by
    a lot. }
  BindingTieMargin = 0.02;

  { Permutations are enumerated exhaustively up to this many. Beyond it the
    binder falls back to a name-led assignment and says so, rather than
    quietly taking minutes over a reaction with a dozen parameters. }
  MaxPermutations = 5040;   // 7!

  { An absolute ceiling on how far a binding may sit from the law and still
    be called a match.

    PROVISIONAL, and M7's to replace. Until now nothing needed it: with only
    hand-shaped laws registered, a reaction either fitted one or fitted
    nothing. Mass action changes that -- k times a product of substrates
    resembles a great deal at a distance -- and without a ceiling it would
    claim every reaction no other law wanted and then report a page of
    defects against it.

    Chosen above the worst genuine defect measured so far (the founding
    duplicated-operand case sits at 0.500), because a defective reaction must
    still associate or there is nothing to report it against. That is the
    tension M7 has to resolve properly, with a margin between candidates as
    well as this floor. }
  MaxAssociationDistance = 0.62;

implementation

{ ------------------------------------------------------------ small helpers }

function BindViaName(AVia: TBindVia): string;
begin
  case AVia of
    bvExactName: Result := 'name';
    bvAlias:     Result := 'convention';
    bvStructure: Result := 'stoichiometry';
    bvShape:     Result := 'shape';
  else           Result := 'unbound';
  end;
end;

function OutcomeName(AOutcome: TBindOutcome): string;
begin
  case AOutcome of
    boBound:         Result := 'bound';
    boAmbiguous:     Result := 'ambiguous';
    boIncomplete:    Result := 'incomplete';
    boNotApplicable: Result := 'n/a';
    boUnparsable:    Result := 'unparsable';
  else               Result := 'generative';
  end;
end;

function TBindingEntry.Describe: string;
begin
  Result := Format('%s = %s (%s)', [Role, ModelName, BindViaName(Via)]);
end;

{ ------------------------------------------------------------------ TBinding }

constructor TBinding.Create;
begin
  inherited Create;
  FEntries := TList<TBindingEntry>.Create;
  Distance := 1;
end;

destructor TBinding.Destroy;
begin
  FEntries.Free;
  inherited;
end;

procedure TBinding.Add(const ARole, AModelName: string; AVia: TBindVia);
var
  E: TBindingEntry;
begin
  E.Role := ARole; E.ModelName := AModelName; E.Via := AVia;
  FEntries.Add(E);
end;

function TBinding.GetEntry(AIndex: Integer): TBindingEntry;
begin
  Result := FEntries[AIndex];
end;

function TBinding.GetCount: Integer;
begin
  Result := FEntries.Count;
end;

function TBinding.ModelNameFor(const ARole: string): string;
var
  E: TBindingEntry;
begin
  for E in FEntries do
    if E.Role = ARole then Exit(E.ModelName);
  Result := '';
end;

function TBinding.RoleFor(const AModelName: string): string;
var
  E: TBindingEntry;
begin
  for E in FEntries do
    if E.ModelName = AModelName then Exit(E.Role);
  Result := '';
end;

function TBinding.IsComplete: Boolean;
begin
  Result := Length(Unbound) = 0;
end;

function TBinding.Score: Double;
begin
  { Distance dominates; the name penalty only separates bindings that fit the
    expression equally well. Weighted so that no accumulation of naming
    oddities can outvote a genuine structural improvement.

    An unfilled role costs more than any distance can, so a binding that
    accounts for every role always beats one that gives up on a role. Without
    that the incomplete binding could WIN: it has one fewer entry to accrue
    name penalty from, so leaving a role empty scored better than filling it,
    and a correct reaction was reported as missing a term it plainly had. }
  Result := Distance + 0.001 * NamePenalty + 10 * Length(Unbound);
end;

function TBinding.AsMap: TDictionary<string, string>;
var
  E: TBindingEntry;
begin
  Result := TDictionary<string, string>.Create;
  for E in FEntries do
    if (E.ModelName <> '') and not Result.ContainsKey(E.ModelName) then
      Result.Add(E.ModelName, E.Role);
end;

function TBinding.Describe: string;
var
  I: Integer;
begin
  Result := '';
  for I := 0 to FEntries.Count - 1 do
  begin
    if I > 0 then Result := Result + ', ';
    Result := Result + FEntries[I].Describe;
  end;
  if Length(Unbound) > 0 then
    Result := Result + '   unbound: ' + string.Join(', ', Unbound);
end;

{ -------------------------------------------------------------- TBindResult }

constructor TBindResult.Create;
begin
  inherited Create;
  FCandidates := TObjectList<TBinding>.Create(True);
  Outcome := boIncomplete;
end;

function TBindResult.EffectiveLaw(ADefault: TRateLawDef): TRateLawDef;
begin
  if Instantiated <> nil then Result := Instantiated else Result := ADefault;
end;

destructor TBindResult.Destroy;
begin
  Instantiated.Free;
  BoundTree.Free;
  CanonTree.Free;
  RawTree.Free;
  FCandidates.Free;
  inherited;
end;

function TBindResult.GetBest: TBinding;
begin
  if FCandidates.Count = 0 then Result := nil else Result := FCandidates[0];
end;

{ ------------------------------------------------------------ applicability }

{ Species on one side of a reaction, not counting EmptySet -- "-> P" has no
  reactants, and counting the notation for their absence as one made a
  synthesis reaction satisfy a "reactants >= 1" constraint. }
function SideCount(const ARefs: TSpeciesRefs): Integer;
var
  I: Integer;
begin
  Result := 0;
  for I := 0 to High(ARefs) do
    if not IsNullSpecies(ARefs[I].Name) then Inc(Result);
end;

function LawApplies(ALaw: TRateLawDef; const AModel: IModelSource;
  AReactionIndex: Integer; out AReason: string): Boolean;
var
  C: TCountConstraint;
  N: Integer;
begin
  AReason := '';
  Result  := True;

  if ALaw.Applicability.HasReactants then
  begin
    N := SideCount(AModel.Reactants(AReactionIndex));
    if TryParseConstraint(ALaw.Applicability.Reactants, C) and not C.Matches(N) then
    begin
      AReason := Format('needs %s reactant(s), the reaction has %d',
                        [C.AsText, N]);
      Exit(False);
    end;
  end;

  if ALaw.Applicability.HasProducts then
  begin
    N := SideCount(AModel.Products(AReactionIndex));
    if TryParseConstraint(ALaw.Applicability.Products, C) and not C.Matches(N) then
    begin
      AReason := Format('needs %s product(s), the reaction has %d',
                        [C.AsText, N]);
      Exit(False);
    end;
  end;

  if ALaw.Applicability.HasModifiers then
  begin
    N := Length(EffectiveModifiers(AModel, AReactionIndex));
    if TryParseConstraint(ALaw.Applicability.Modifiers, C) and not C.Matches(N) then
    begin
      AReason := Format('needs %s modifier(s), the reaction has %d',
                        [C.AsText, N]);
      Exit(False);
    end;
  end;
end;

{ ------------------------------------------------------- function inlining }

{ A rate law may be written as a call to a function the model defines:

      function MM(s, v, k)  v*s/(k+s)  end
      J1: S -> P; MM(S, Vm, Km);

  Factoring a repeated law into a function is good modelling practice and
  common. Left alone it looks like no registered law at all, so a correctly
  written model would be reported as unassociated -- or worse, as an operator
  substitution, since a call node is not a division node. That is a false
  positive on a correct model, which is the failure that gets a linter turned
  off, so the call is substituted away before anything compares trees.

  ADepth guards against a function defined in terms of itself. Antimony should
  not permit it, but a checker that hangs on a malformed model is worse than
  one that gives up on it. }
{ ------------------------------------------- the compartment volume factor }

{ An SBML kinetic law is a RATE, not a rate of change of concentration, so it
  is written as volume times kinetics: "cyt*(kf*A - kr*B)". The volume belongs
  to the reaction, not to the rate law, and no registered law has a role for
  it.

  Left in place it is not merely noise. It is an identifier like any other, so
  the binder offers it to every parameter role and the shape then fails to
  match: the BioModels corpus produced warnings saying, in as many words, that
  "cyt" plays the Ks role, followed by a page of defects arising from that.
  It was the single largest source of false positives in the M17 run.

  Only MULTIPLICATIVE factors on the spine are removed, and only in a
  numerator. A compartment dividing an expression is doing something else --
  converting an amount to a concentration, most often -- and that is part of
  the kinetics.

  Returns nil when the subtree was nothing but compartments, which is what
  lets a caller collapse "cyt*k" to "k" without a special case. }
function StripCompartmentFactors(ANode: TAstNode;
  const AModel: IModelSource; var AStripped: Boolean): TAstNode;
var
  L, R: TAstNode;
  Both, LGone, RGone: Boolean;
begin
  if (ANode.Kind = nkIdent) and AModel.KnowsSymbolKinds and
     (AModel.SymbolKind(ANode.Name) = skCompartment) then
  begin
    AStripped := True;
    Exit(nil);
  end;

  if ANode.Kind = nkMul then
  begin
    L := StripCompartmentFactors(ANode[0], AModel, AStripped);
    R := StripCompartmentFactors(ANode[1], AModel, AStripped);
    if L = nil then Exit(R);
    if R = nil then Exit(L);
    Exit(TAstNode.Op(nkMul, [L, R]));
  end;

  { "cyt*Vm*S/(Km + S)" parses with a division at the root, so the numerator
    has to be descended into or the commonest form of all is missed. }
  if ANode.Kind = nkDiv then
  begin
    L := StripCompartmentFactors(ANode[0], AModel, AStripped);
    if L = nil then L := TAstNode.Num(1);
    Exit(TAstNode.Op(nkDiv, [L, ANode[1].Clone]));
  end;

  { A volume DISTRIBUTED over a sum -- "Cell*k3*P2*T2 - Cell*k4*CC", which is
    how libSBML renders a reversible reaction often enough to matter. It is
    the same volume and it comes off the same way, but only when it is common
    to EVERY term: taking it off "Cell*a - b" would change what the
    expression means rather than tidy it.

    Missed on the first pass, because the spine walk stopped at the sum. It
    cost nothing on the synthetic corpus, where no case writes a rate law
    that way, and showed up on BioModels as a page of S005/S006 pairs against
    correct reversible reactions. }
  if ANode.Kind in [nkAdd, nkSub] then
  begin
    L := nil;
    R := nil;
    try
      LGone := False;
      RGone := False;
      L := StripCompartmentFactors(ANode[0], AModel, LGone);
      R := StripCompartmentFactors(ANode[1], AModel, RGone);
      Both := LGone and RGone;
      if Both then
      begin
        if L = nil then L := TAstNode.Num(1);
        if R = nil then R := TAstNode.Num(1);
        AStripped := True;
        Result := TAstNode.Op(ANode.Kind, [L, R]);
        L := nil;
        R := nil;
        Exit;
      end;
    finally
      L.Free;
      R.Free;
    end;
    Exit(ANode.Clone);
  end;

  Result := ANode.Clone;
end;

function InlineUserFunctions(ANode: TAstNode; const AModel: IModelSource;
  ADepth: Integer): TAstNode;
const
  MaxInlineDepth = 8;
var
  Args: TArray<string>;
  Body: string;
  BodyTree, Inlined, Arg: TAstNode;
  Map: TDictionary<string, TAstNode>;
  Err: string;
  I: Integer;
  Actuals: TObjectList<TAstNode>;
begin
  if ANode = nil then Exit(nil);

  if (ANode.Kind <> nkFunc) or (ADepth >= MaxInlineDepth) or
     not AModel.UserFunction(ANode.Name, Args, Body) then
  begin
    { Not a user function -- a built-in like exp, or too deep. Copy it, but
      keep descending: a user function may sit inside one. }
    if ANode.Kind = nkIdent then Exit(TAstNode.Ident(ANode.Name));
    if ANode.Kind = nkNumber then Exit(TAstNode.Num(ANode.Value));
    Result := TAstNode.Create(ANode.Kind);
    Result.Name := ANode.Name;
    for I := 0 to ANode.Count - 1 do
      Result.AddChild(InlineUserFunctions(ANode[I], AModel, ADepth));
    Exit;
  end;

  { Arity mismatch: leave the call alone rather than substituting nonsense.
    The model is wrong, but saying so is not this function's job. }
  if Length(Args) <> ANode.Count then
  begin
    Result := ANode.Clone;
    Exit;
  end;

  if not TryParseRateLaw(Body, BodyTree, Err) then
  begin
    Result := ANode.Clone;
    Exit;
  end;

  Actuals := TObjectList<TAstNode>.Create(True);
  Map     := TDictionary<string, TAstNode>.Create;
  try
    { Arguments are themselves inlined first, so a call passed as an argument
      is resolved too. }
    for I := 0 to ANode.Count - 1 do
    begin
      Arg := InlineUserFunctions(ANode[I], AModel, ADepth + 1);
      Actuals.Add(Arg);
      Map.AddOrSetValue(Args[I], Arg);
    end;

    Inlined := CloneSubstituted(BodyTree, Map);
    try
      { The body may itself call another user function. }
      Result := InlineUserFunctions(Inlined, AModel, ADepth + 1);
    finally
      Inlined.Free;
    end;
  finally
    Map.Free;
    Actuals.Free;
    BodyTree.Free;
  end;
end;

{ ------------------------------------------------------- candidate gathering }

{ The model names that could fill a species role, taken from the reaction's
  structure rather than from its rate law. A substrate that does not appear in
  the rate law is a defect, not a reason to bind something else to the role. }
function SpeciesCandidates(const ARole: TRole; const AModel: IModelSource;
  AIdx: Integer): TArray<string>;
var
  Refs: TSpeciesRefs;
  Mods: TModifierRefs;
  I: Integer;
begin
  Result := nil;

  case ARole.Position of
    { EmptySet is skipped on both sides: it is the absence of a reactant,
      so it can fill no role. }
    spSubstrate:
      begin
        Refs := AModel.Reactants(AIdx);
        for I := 0 to High(Refs) do
          if not IsNullSpecies(Refs[I].Name) then
            Result := Result + [Refs[I].Name];
      end;

    spProduct:
      begin
        Refs := AModel.Products(AIdx);
        for I := 0 to High(Refs) do
          if not IsNullSpecies(Refs[I].Name) then
            Result := Result + [Refs[I].Name];
      end;

    spInhibitor, spActivator, spModifier:
      begin
        Mods := EffectiveModifiers(AModel, AIdx);
        for I := 0 to High(Mods) do
        begin
          { A declared role must match. An UNSPECIFIED modifier is allowed to
            fill any modifier role: Antimony only records a role when the
            modeller used an interaction arrow, and most do not. }
          if (ARole.Position = spModifier) or
             (Mods[I].Role = mrUnspecified) or
             ((ARole.Position = spInhibitor) and (Mods[I].Role = mrInhibitor)) or
             ((ARole.Position = spActivator) and (Mods[I].Role = mrActivator)) then
            Result := Result + [Mods[I].Name];
        end;
      end;

  else
    { A species role with no declared position: anything the model calls a
      species and the rate law mentions. }
    Result := nil;
  end;
end;

{ ------------------------------------------------------------------ scoring }

{ How odd it is for AModelName to sit in ARole. Zero when the model uses the
  role's own name or one of its declared conventions. }
function NameOddity(ALaw: TRateLawDef; const ARole: TRole;
  const AModelName: string; out ASuspicious: Boolean): Double;
var
  A: string;
  Other: TRole;
  I: Integer;
begin
  ASuspicious := False;

  if ARole.Name = AModelName then Exit(0);

  for A in ARole.Aliases do
    if SameText(A, AModelName) then Exit(0);

  { Bound to a name that is another role's declared convention. This is the
    role-swap signal, and it is worth far more than the structural difference
    it produces: 'you put the thing called Km where Vm belongs' is a sentence
    the user can act on. }
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    Other := ALaw.Roles[I];
    if Other.Name = ARole.Name then Continue;
    if Other.Name = AModelName then
    begin
      ASuspicious := True;
      Exit(10);
    end;
    for A in Other.Aliases do
      if SameText(A, AModelName) then
      begin
        ASuspicious := True;
        Exit(10);
      end;
  end;

  { An unremarkable name nobody has an opinion about. }
  Result := 1;
end;

{ ---------------------------------------------------------------- the binder }

type
  { One role awaiting assignment, with the model names it could take. }
  TSlot = record
    Role:       TRole;
    Candidates: TArray<string>;
    Fixed:      string;      // already decided (species from structure)
    Via:        TBindVia;
  end;

function BindReaction(ALaw: TRateLawDef; const AModel: IModelSource;
  AReactionIndex: Integer): TBindResult;
var
  Slots: TArray<TSlot>;
  ParamSlots: TArray<Integer>;
  RateText, Err, Reason: string;
  Parsed, Inlined: TAstNode;
  Stripped: Boolean;
  I, J: Integer;
  R: TRole;
  Cands: TArray<string>;
  Idents: TArray<string>;
  ParamNames: TArray<string>;
  Used: TDictionary<string, Boolean>;
  Perms: Integer;
  Assignment: TArray<string>;

  function IsBoundSpecies(const AName: string): Boolean;
  var
    K: Integer;
  begin
    for K := 0 to High(Slots) do
      if (Slots[K].Fixed <> '') and (Slots[K].Fixed = AName) then Exit(True);
    Result := False;
  end;

  { Builds a TBinding from the current Assignment and scores it by renaming
    the reaction's tree into role vocabulary and comparing with the law's
    canonical form. }
  { Which position in Assignment holds the value for slot ASlot, or -1. }
  function AssignmentIndexOf(ASlot: Integer): Integer;
  var
    M: Integer;
  begin
    for M := 0 to High(ParamSlots) do
      if ParamSlots[M] = ASlot then Exit(M);
    Result := -1;
  end;

  procedure Evaluate;
  var
    B: TBinding;
    Map: TDictionary<string, string>;
    Renamed, RenamedCanon: TAstNode;
    K, Ai: Integer;
    Susp: Boolean;
    Odd: Double;
    Nm: string;
    Via: TBindVia;
  begin
    B := TBinding.Create;

    { Built in one pass rather than added and then patched: an entry is a
      record in a TList, so a later edit means writing a modified copy back,
      and that is a trap waiting for someone to forget. }
    for K := 0 to High(Slots) do
    begin
      if Slots[K].Fixed <> '' then
      begin
        B.Add(Slots[K].Role.Name, Slots[K].Fixed, Slots[K].Via);
        Continue;
      end;

      Ai := AssignmentIndexOf(K);
      if Ai < 0 then Nm := '' else Nm := Assignment[Ai];

      if Nm = '' then
      begin
        B.Add(Slots[K].Role.Name, '', bvUnbound);
        B.Unbound := B.Unbound + [Slots[K].Role.Name];
        Continue;
      end;

      Odd := NameOddity(ALaw, Slots[K].Role, Nm, Susp);
      if Odd = 0 then
        if Slots[K].Role.Name = Nm then Via := bvExactName else Via := bvAlias
      else
        Via := bvShape;

      B.Add(Slots[K].Role.Name, Nm, Via);
      B.NamePenalty := B.NamePenalty + Odd;
      if Susp then
        B.Suspicious := B.Suspicious
          + [Format('%s = %s', [Slots[K].Role.Name, Nm])];
    end;

    Map := B.AsMap;
    try
      Renamed := CloneRenamed(Result.RawTree, Map);
      try
        RenamedCanon := Canonicalise(Renamed);
        try
          { The cost of the very diff the static engine will perform if this
            binding wins. Association and classification therefore agree by
            construction: the law chosen is the law with least to explain. }
          B.Distance    := DiffCost(RenamedCanon, ALaw.Canon);
          { Compared on the trees AS WRITTEN, not the canonical ones.
            Canonicalisation can cancel symbols away -- Vm*K^n/K^n + S^n
            collapses to Vm + S^n -- and then a defective copy of a law no
            longer appears to share its ingredients at all, so the very
            evidence that admits it is destroyed by the same rewriting that
            created the defect. }
          B.SameSymbols   := SameIdentifierMultiset(Renamed, ALaw.Expr);
          B.SymbolsSubset := IdentifiersSubsetOf(Renamed, ALaw.Expr);
        finally
          RenamedCanon.Free;
        end;
      finally
        Renamed.Free;
      end;
    finally
      Map.Free;
    end;

    Result.Candidates.Add(B);
  end;

  procedure Permute(ADepth: Integer);
  var
    K: Integer;
    Name: string;
    Any: Boolean;
    Local: TArray<string>;   { not the outer Cands, which slot building uses }
  begin
    if Result.Candidates.Count > MaxPermutations then Exit;
    if ADepth > High(ParamSlots) then
    begin
      Evaluate;
      Exit;
    end;

    Local := Slots[ParamSlots[ADepth]].Candidates;
    if Length(Local) = 0 then
    begin
      Assignment[ADepth] := '';
      Permute(ADepth + 1);
      Exit;
    end;

    Any := False;
    for K := 0 to High(Local) do
    begin
      Name := Local[K];
      if Used.ContainsKey(Name) then Continue;   { injective: one name, one role }
      Any := True;
      Used.Add(Name, True);
      Assignment[ADepth] := Name;
      Permute(ADepth + 1);
      Used.Remove(Name);
    end;

    { Every candidate is already spoken for. The recursion has to continue
      with this role UNFILLED rather than stopping: abandoning the branch
      produced no binding at all, so a law with one more parameter than the
      expression supplies simply vanished from consideration -- and with it
      every diagnostic about the term that was left out. }
    if not Any then
    begin
      Assignment[ADepth] := '';
      Permute(ADepth + 1);
    end;
  end;

begin
  Result := TBindResult.Create;
  Result.LawId      := ALaw.Id;
  Result.ReactionId := AModel.ReactionId(AReactionIndex);

  { A family law is turned into a concrete one for THIS reaction before
    anything else happens, so everything below works on an ordinary law and
    needs no idea that families exist. }
  if ALaw.Generative then
  begin
    if not InstantiateGenerative(ALaw, AModel, AReactionIndex,
                                 Result.Instantiated, Reason) then
    begin
      Result.Outcome := boGenerative;
      Result.Reason  := 'cannot be instantiated here: ' + Reason;
      Exit;
    end;
    ALaw := Result.Instantiated;
  end;

  if not LawApplies(ALaw, AModel, AReactionIndex, Reason) then
  begin
    Result.Outcome := boNotApplicable;
    Result.Reason  := Reason;
    Exit;
  end;

  RateText := AModel.RateLawText(AReactionIndex);
  if not TryParseRateLaw(RateText, Parsed, Err) then
  begin
    Result.Outcome := boUnparsable;
    Result.Reason  := Err;
    Exit;
  end;

  { Calls to model-defined functions are substituted away here, so everything
    downstream sees one vocabulary of operators rather than two. }
  try
    Inlined := InlineUserFunctions(Parsed, AModel, 0);
  finally
    Parsed.Free;
  end;

  { A rate law that is nothing BUT a compartment is left alone: there is no
    kinetics underneath to reveal, and "1" would be a worse thing to report
    against than the expression the modeller wrote. }
  Stripped := False;
  try
    Result.RawTree := StripCompartmentFactors(Inlined, AModel, Stripped);
    if Result.RawTree = nil then
    begin
      Result.RawTree := Inlined.Clone;
      Stripped := False;
    end;
  finally
    Inlined.Free;
  end;
  Result.VolumeStripped := Stripped;

  Result.CanonTree := Canonicalise(Result.RawTree);
  Idents := IdentifiersIn(Result.RawTree);

  { --- slots --- }
  SetLength(Slots, ALaw.RoleCount);
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    R := ALaw.Roles[I];
    Slots[I] := Default(TSlot);
    Slots[I].Role := R;

    { An instantiated generative law names its roles after the model's own
      symbols, and there is nothing to choose: this role IS that species. }
    if R.BindsToSelf then
    begin
      Slots[I].Fixed := R.Name;
      Slots[I].Via   := bvStructure;
      Continue;
    end;

    if R.Kind = rkSpecies then
    begin
      Cands := SpeciesCandidates(R, AModel, AReactionIndex);
      { Cardinality 1 and exactly one candidate: structure decides, and no
        permutation is needed or wanted. }
      if Length(Cands) = 1 then
      begin
        Slots[I].Fixed := Cands[0];
        Slots[I].Via   := bvStructure;
      end
      else
        Slots[I].Candidates := Cands;
    end;
  end;

  { Parameter candidates are the rate law's identifiers that are not bound
    species. Names the model classifies as species are excluded -- unless the
    source cannot classify, in which case everything unbound is fair game. }
  ParamNames := nil;
  for I := 0 to High(Idents) do
  begin
    if IsBoundSpecies(Idents[I]) then Continue;
    if AModel.KnowsSymbolKinds and
       (AModel.SymbolKind(Idents[I]) = skSpecies) then Continue;
    { Nor a built-in. "pi" is a constant of mathematics, not a half-saturation
      the modeller happened to name oddly, and offering it as a candidate
      lets it be chosen to play one. }
    if IsBuiltInSymbol(Idents[I]) then Continue;
    { Nor a compartment. Most are gone by now -- StripCompartmentFactors took
      the volume off the spine -- but one reached in some other way is still a
      volume, and no registered law has a kinetic role a volume can fill.
      Offering it as a candidate is how "cyt" came to play the Ks role. }
    if AModel.KnowsSymbolKinds and
       (AModel.SymbolKind(Idents[I]) = skCompartment) then Continue;
    ParamNames := ParamNames + [Idents[I]];
  end;

  ParamSlots := nil;
  for I := 0 to High(Slots) do
    if Slots[I].Fixed = '' then
    begin
      if Slots[I].Role.Kind <> rkSpecies then
        Slots[I].Candidates := ParamNames;
      ParamSlots := ParamSlots + [I];
    end;

  { --- enumerate --- }
  Perms := 1;
  for I := 0 to High(ParamSlots) do
    Perms := Perms * Max(1, Length(Slots[ParamSlots[I]].Candidates));

  SetLength(Assignment, Length(ParamSlots));
  Used := TDictionary<string, Boolean>.Create;
  try
    if Perms > MaxPermutations then
    begin
      { Too many to enumerate. Take the name-led assignment and say so; a
        silent truncation would read as 'this is the best binding' when it is
        only the first one tried. }
      for I := 0 to High(ParamSlots) do
      begin
        Assignment[I] := '';
        for J := 0 to High(Slots[ParamSlots[I]].Candidates) do
        begin
          var Nm := Slots[ParamSlots[I]].Candidates[J];
          var Susp: Boolean;
          if not Used.ContainsKey(Nm) and
             (NameOddity(ALaw, Slots[ParamSlots[I]].Role, Nm, Susp) = 0) then
          begin
            Assignment[I] := Nm;
            Used.Add(Nm, True);
            Break;
          end;
        end;
      end;
      Evaluate;
      Result.Reason := Format('%d permutations exceeded the enumeration limit; '
        + 'bound by naming convention alone', [Perms]);
    end
    else
      Permute(0);
  finally
    Used.Free;
  end;

  if Result.Candidates.Count = 0 then
  begin
    Result.Outcome := boIncomplete;
    Result.Reason  := 'no candidate binding could be formed';
    Exit;
  end;

  Result.Candidates.Sort(TComparer<TBinding>.Construct(
    function(const A, B: TBinding): Integer
    begin
      Result := CompareValue(A.Score, B.Score);
    end));

  if not Result.Best.IsComplete then
  begin
    { ONE unfilled role, in an expression built from nothing but this law's
      symbols, is a usable binding rather than a failed one -- and the thing
      it usually means is that a term was left out.

      Refusing it made a whole defect class invisible. Dropping Km from
      Vm*S/(Km + S) removes the only occurrence of Km, so the law has a role
      nothing can fill and stopped being a candidate at all; the reaction then
      associated with nothing and the omission went unreported. Reported as
      the missing term it is, by the ordinary diff, once the binding is
      allowed to stand.

      Held to one role, and to a subset of the law's own vocabulary, so that a
      short expression cannot be claimed by every law that happens to contain
      its symbols. }
    if (Length(Result.Best.Unbound) = 1) and Result.Best.SymbolsSubset then
    begin
      Result.Outcome := boBound;
      Result.Reason  := Format('nothing fills the %s role, which the law '
        + 'requires', [Result.Best.Unbound[0]]);
    end
    else
    begin
      Result.Outcome := boIncomplete;
      Result.Reason  := 'no model symbol could fill: '
                        + string.Join(', ', Result.Best.Unbound);
    end;
  end
  else if (Result.Candidates.Count > 1) and
          (Result.Candidates[1].Score - Result.Best.Score < BindingTieMargin) then
  begin
    { Two bindings fit equally well. Guessing here is how a role swap gets
      reported against the wrong parameter. }
    Result.Outcome := boAmbiguous;
    Result.Reason  := Format('two bindings fit equally well: [%s] and [%s]',
      [Result.Best.Describe, Result.Candidates[1].Describe]);
  end
  else
    Result.Outcome := boBound;

  { The reaction's tree in role vocabulary, kept for the static engine. }
  if Result.Best <> nil then
  begin
    var Map := Result.Best.AsMap;
    try
      Result.BoundTree := CloneRenamed(Result.RawTree, Map);
    finally
      Map.Free;
    end;
  end;
end;

end.
