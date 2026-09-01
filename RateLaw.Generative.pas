unit RateLaw.Generative;

{ Instantiating a family law for one reaction.

  Mass action is not an expression, it is a shape: k times the product of the
  substrates, each raised to its own stoichiometry. First order is k*A, second
  order k*A*B or k*A^2, third order k*A*B*C. Written out as fixed expressions
  that is one registry entry per order, for the commonest law in biology --
  which would make "coverage grows by adding registry entries" false exactly
  where it matters most.

  So the registry holds the family:

      expression : "k * prod(Si^ai)"
      roles      : k  parameter
                   Si species, cardinality n, exponent ai

  and this unit turns it into a concrete expression for a concrete reaction,
  taken from that reaction's own stoichiometry, before anything tries to bind
  or compare it.

  THE TEMPLATE DRIVES THE EXPANSION. Every prod(...) in the family's
  expression is replaced by the product over the species of that role's
  position -- substrates for a substrate role, products for a product role --
  and the rest of the template is carried through untouched. Nothing in this
  unit knows what mass action looks like.

  It did until the BioModels corpus was run. The instantiator built
  "<the one scalar parameter> * <the product of the reactants>" directly, and
  refused outright any family declaring a second scalar. That made reversible
  mass action -- kf*prod(Si^ai) - kr*prod(Pj^bj), one of the commonest rate
  laws there is and everywhere in the corpus -- not merely unregistered but
  INEXPRESSIBLE. Per the falsification test in section 2 of the
  specification, a law that cannot be added without changing the engine is a
  defect in the engine, so it is recorded as one rather than quietly fixed.

  The instantiated law names its species roles after the model's actual
  species, and marks them BindsToSelf. There is nothing to choose: the
  substrates of the reaction ARE the substrates of the law, in the order the
  reaction gives them. Permuting them would be meaningless here (the product
  is commutative) and would cost a round of ambiguity for nothing. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Types, RateLaw.Ast, RateLaw.Parser, RateLaw.Canonical,
  RateLaw.Registry;

{ Builds a concrete law for this reaction. The caller owns AInst.

  False when the family cannot be instantiated here -- which is a normal
  outcome, not a failure, and AReason says why so the report can be honest
  about what was not checked. }
function InstantiateGenerative(ALaw: TRateLawDef; const AModel: IModelSource;
                               AIndex: Integer; out AInst: TRateLawDef;
                               out AReason: string): Boolean;

{ The reaction's modifiers, declared and inferred.

  A modifier is a species the rate depends on that the reaction neither
  consumes nor produces. SBML states them in listOfModifiers; Antimony states
  them only where the modeller drew an interaction arrow (-o, -|, -(), and
  sbmlToAntimony does not turn the former into the latter -- an SBML modifier
  survives the conversion only by still appearing in the rate law.

  So asking IModelSource.Modifiers alone answers "which interaction arrows
  were drawn", which over BioModels is almost none: catalytic mass action
  matched 43 reactions when the true figure was in the hundreds. A species in
  the rate law that is on neither side of the reaction IS a modifier, by the
  definition, whatever notation the file arrived in.

  Inferred ones are mrUnspecified -- true, and weaker than a declared role,
  which is exactly the distinction that record exists to carry. }
function EffectiveModifiers(const AModel: IModelSource;
                            AIndex: Integer): TModifierRefs;

implementation

function EffectiveModifiers(const AModel: IModelSource;
  AIndex: Integer): TModifierRefs;
var
  Refs: TSpeciesRefs;
  Tree: TAstNode;
  Err, Name: string;
  I: Integer;
  Known: TStringList;
begin
  Result := AModel.Modifiers(AIndex);
  if not AModel.KnowsSymbolKinds then Exit;

  Known := TStringList.Create;
  try
    Known.CaseSensitive := True;
    for I := 0 to High(Result) do Known.Add(Result[I].Name);
    Refs := AModel.Reactants(AIndex);
    for I := 0 to High(Refs) do Known.Add(Refs[I].Name);
    Refs := AModel.Products(AIndex);
    for I := 0 to High(Refs) do Known.Add(Refs[I].Name);

    { A rate law that will not parse is the checker's normal business, not an
      error: it simply contributes no inferred modifiers. }
    if not TryParseRateLaw(AModel.RateLawText(AIndex), Tree, Err) then Exit;
    try
      for Name in IdentifiersIn(Tree) do
      begin
        if Known.IndexOf(Name) >= 0 then Continue;
        if IsNullSpecies(Name) or IsBuiltInSymbol(Name) then Continue;
        if AModel.SymbolKind(Name) <> skSpecies then Continue;
        Known.Add(Name);
        Result := Result + [TModifierRef.Make(Name, mrUnspecified)];
      end;
    finally
      Tree.Free;
    end;
  finally
    Known.Free;
  end;
end;

{ The exponent for one substrate, as source text.

  Three cases, and the third is the reason TSpeciesRef has carried both a
  number and its source text since the interface was first written:

    1     the species appears bare -- A, not A^1, because A^1 would be a
          structural difference from every model that writes A
    n     an ordinary integer or fractional stoichiometry
    'n'   a stoichiometry written as a SYMBOL ('S1 + n S2 => S3'). The
          numeric accessor gives NaN for these; the symbol's name is what
          the expression needs, and it is compared as a symbol. }
function ExponentTextFor(const ARef: TSpeciesRef): string;
begin
  if ARef.IsSymbolic then
  begin
    if Trim(ARef.Text) = '' then Exit('');   // unusable; caller rejects
    Exit(ARef.Text);
  end;

  if SameValue(ARef.Value, 1) then Exit('');
  Result := ARef.Text;
  if Trim(Result) = '' then
    Result := FloatToStr(ARef.Value, TFormatSettings.Invariant);
end;

function InstantiateGenerative(ALaw: TRateLawDef; const AModel: IModelSource;
  AIndex: Integer; out AInst: TRateLawDef; out AReason: string): Boolean;
var
  I, Indexed: Integer;
  NewRole: TRole;
  Expr, Failure: string;
  Seen: TStringList;

  { The species an indexed role stands for. A role with no position declared
    is taken as a substrate, which is what every family written before the
    product side existed meant by saying nothing. }
  function RefsForRole(const ARole: TRole): TSpeciesRefs;
  var
    Mods: TModifierRefs;
    J: Integer;
  begin
    if ARole.Position = spProduct then
      Exit(AModel.Products(AIndex));

    { A modifier has no stoichiometry -- it is neither consumed nor produced
      -- so it enters the product to the first power. Converting here rather
      than teaching the expansion about two reference types keeps the rest of
      this unit reading in one vocabulary. }
    if ARole.Position in [spModifier, spActivator, spInhibitor] then
    begin
      Mods := EffectiveModifiers(AModel, AIndex);
      SetLength(Result, 0);
      for J := 0 to High(Mods) do
      begin
        { A declared role must match. An UNSPECIFIED modifier fills any
          modifier role, exactly as SpeciesCandidates treats it: Antimony
          records a role only where the modeller drew an interaction arrow,
          and most do not. }
        if (ARole.Position = spModifier) or
           (Mods[J].Role = mrUnspecified) or
           ((ARole.Position = spActivator) and (Mods[J].Role = mrActivator)) or
           ((ARole.Position = spInhibitor) and (Mods[J].Role = mrInhibitor)) then
          Result := Result + [TSpeciesRef.Make(Mods[J].Name, 1)];
      end;
      Exit;
    end;

    Result := AModel.Reactants(AIndex);
  end;

  { "A^2*B", or "1" for an empty product. A reaction with no reactants is
    zero order and k alone is right for it -- not a special case, just the
    empty product. }
  function ExpandProduct(const ARole: TRole; out AFailure: string): string;
  var
    Refs: TSpeciesRefs;
    J: Integer;
    Exp, Term: string;
  begin
    AFailure := '';
    Result   := '';
    Refs := RefsForRole(ARole);
    for J := 0 to High(Refs) do
    begin
      if Trim(Refs[J].Name) = '' then Continue;
      { "-> P" is zero order in its absent substrate, not first order in a
        species called EmptySet. }
      if IsNullSpecies(Refs[J].Name) then Continue;

      Exp := ExponentTextFor(Refs[J]);
      if Refs[J].IsSymbolic and (Exp = '') then
      begin
        AFailure := Format('the stoichiometry of "%s" is a symbol the model '
                         + 'did not name', [Refs[J].Name]);
        Exit('');
      end;

      if Exp = '' then Term := Refs[J].Name
      else Term := Refs[J].Name + '^' + Exp;

      { The same species twice on one side ('A + A -> B') is a legitimate way
        of writing second order. The expression carries it twice and
        canonicalisation collects A*A into A^2, so it compares equal to a
        model that wrote A^2 directly. }
      if Result = '' then Result := Term
      else Result := Result + '*' + Term;
    end;
    if Result = '' then Result := '1';
  end;

  { Rewrites every prod(...) in the template. The argument's leading
    identifier names the indexed role, so prod(Si^ai) and prod(Si) both
    resolve to Si. }
  function ExpandTemplate(const ATemplate: string; out AFailure: string): string;
  var
    P, Depth, ArgStart, K, Idx: Integer;
    Arg, Base, Repl, Fail: string;
  begin
    AFailure := '';
    Result   := ATemplate;
    P := Pos('prod(', Result);
    while P > 0 do
    begin
      ArgStart := P + Length('prod(');
      Depth    := 1;
      K        := ArgStart;
      while (K <= Length(Result)) and (Depth > 0) do
      begin
        if Result[K] = '(' then Inc(Depth)
        else if Result[K] = ')' then Dec(Depth);
        if Depth > 0 then Inc(K);
      end;
      if Depth <> 0 then
      begin
        AFailure := 'the family expression has an unclosed prod(';
        Exit('');
      end;

      Arg  := Copy(Result, ArgStart, K - ArgStart);
      Base := Trim(Arg);
      Idx  := Pos('^', Base);
      if Idx > 0 then Base := Trim(Copy(Base, 1, Idx - 1));

      Idx := ALaw.IndexOfRole(Base);
      if Idx < 0 then
      begin
        AFailure := Format('prod(%s) names "%s", which the family does not '
                         + 'declare as a role', [Arg, Base]);
        Exit('');
      end;
      if not ALaw.Roles[Idx].IsIndexed then
      begin
        AFailure := Format('prod(%s) names "%s", which is not a '
                         + 'cardinality-n role', [Arg, Base]);
        Exit('');
      end;

      Repl := ExpandProduct(ALaw.Roles[Idx], Fail);
      if Fail <> '' then
      begin
        AFailure := Fail;
        Exit('');
      end;

      { Parenthesised. The expansion is a product being dropped into an
        arbitrary template, and in "kf*prod(..) - kr*prod(..)" an unbracketed
        one would rebind across the minus sign. }
      Result := Copy(Result, 1, P - 1) + '(' + Repl + ')'
              + Copy(Result, K + 1, MaxInt);
      P := Pos('prod(', Result);
    end;
  end;

  { Every species and symbolic stoichiometry the expansion introduced has to
    be a legal identifier of the instantiated law too, or the model's own
    symbol reads as an undeclared extra. }
  procedure AddRolesFor(const ARole: TRole);
  var
    Refs: TSpeciesRefs;
    J: Integer;
  begin
    Refs := RefsForRole(ARole);
    for J := 0 to High(Refs) do
    begin
      if Trim(Refs[J].Name) = '' then Continue;
      if IsNullSpecies(Refs[J].Name) then Continue;

      if Seen.IndexOf(Refs[J].Name) < 0 then
      begin
        Seen.Add(Refs[J].Name);
        NewRole             := Default(TRole);
        NewRole.Name        := Refs[J].Name;
        NewRole.Kind        := rkSpecies;
        NewRole.Position    := ARole.Position;
        NewRole.Cardinality := '1';
        NewRole.BindsToSelf := True;
        AInst.AddRole(NewRole);
      end;

      if Refs[J].IsSymbolic and (Trim(Refs[J].Text) <> '') then
        if AInst.IndexOfRole(Refs[J].Text) < 0 then
        begin
          NewRole             := Default(TRole);
          NewRole.Name        := Refs[J].Text;
          NewRole.Kind        := rkParameter;
          NewRole.Semantics   := 'stoichiometry';
          NewRole.Cardinality := '1';
          NewRole.BindsToSelf := True;
          AInst.AddRole(NewRole);
        end;
    end;
  end;

begin
  AInst   := nil;
  AReason := '';
  Result  := False;

  if not ALaw.Generative then
  begin
    AReason := 'not a generative law';
    Exit;
  end;

  Indexed := 0;
  for I := 0 to ALaw.RoleCount - 1 do
    if ALaw.Roles[I].IsIndexed then Inc(Indexed);
  if Indexed = 0 then
  begin
    AReason := 'the family declares no cardinality-n role, so there is '
             + 'nothing to instantiate';
    Exit;
  end;

  AInst := TRateLawDef.Create;
  try
    AInst.Id         := ALaw.Id;
    AInst.LawName    := ALaw.LawName;
    AInst.Version    := ALaw.Version;
    AInst.Enabled    := True;
    AInst.Generative := False;          { it is concrete now }
    AInst.Notes      := ALaw.Notes;
    AInst.Layer      := ALaw.Layer;

    { Applicability carries over, and the omission was a real bug: BindReaction
      replaces the family with the instantiated law BEFORE calling LawApplies,
      so a constraint left behind here is a constraint that never runs. It
      went unnoticed while mass action was the only family and declared none.
      It surfaced when catalytic mass action -- which is plain mass action
      when a reaction has no modifiers, and so MUST be refused on one -- tied
      with mass action on every ordinary reaction in the suite. }
    AInst.Applicability := ALaw.Applicability;

    { Scalar roles carry over untouched -- their naming conventions are what
      let k1, kf and so on bind without the shape having to decide. There may
      be any number of them; a reversible family needs two, and refusing that
      is what made reversible mass action inexpressible. }
    for I := 0 to ALaw.RoleCount - 1 do
      if not ALaw.Roles[I].IsIndexed then
        AInst.AddRole(ALaw.Roles[I]);

    { Expression, not Expr: the template is expanded as SOURCE TEXT and
      reparsed. Expr is the parsed tree, and rebuilding one tree into another
      would mean a second printer to keep in step with the parser. }
    Expr := ExpandTemplate(ALaw.Expression, Failure);
    if Failure <> '' then
    begin
      AReason := Failure;
      FreeAndNil(AInst);
      Exit;
    end;

    Seen := TStringList.Create;
    try
      for I := 0 to ALaw.RoleCount - 1 do
        if ALaw.Roles[I].IsIndexed then AddRolesFor(ALaw.Roles[I]);
    finally
      Seen.Free;
    end;

    if not AInst.SetExpression(Expr) then
    begin
      AReason := Format('the instantiated expression "%s" will not parse',
                        [Expr]);
      FreeAndNil(AInst);
      Exit;
    end;

    AInst.Valid := True;
    Result := True;
  except
    on E: Exception do
    begin
      FreeAndNil(AInst);
      AReason := E.Message;
      Result := False;
    end;
  end;
end;

end.
