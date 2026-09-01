unit RateLaw.Static;

{ The static engine: structural comparison of a reaction against the law it is
  supposed to follow, and classification of what differs.

  ONE diff, many laws. Nothing here knows what Michaelis-Menten is. The law
  arrives as a canonical tree and a role binding; every defect class is stated
  in terms of tree shape, so a new law is a registry entry and not a new walk.
  If a defect class ever needs to ask which law it is looking at, that is a
  failure of this design and should be recorded as one.

  The canonical pair carries almost everything. Duplicated operands, missing
  and extra symbols, substituted operators and misplaced parentheses are all
  decided there, because the diff already walks to the node that differs and
  the classification is a local question about that node:

    same operands, different operator   -> a substitution      (S003)
    different operands                  -> a regrouping        (S010)
    an operand repeated among siblings  -> a duplication       (S004)

  The pre-canonical pair is the fallback, and it runs only when the canonical
  pass finds nothing to say. Canonicalisation can cancel a defect out of
  existence -- terms that divide away leave a tree differing from the law only
  by absence -- and that is the case where the operators as written are the
  only evidence left.

  It must not run otherwise. Every commutative reordering -- S*Vm where the
  law says Vm*S -- is a pre-canonical difference and no defect at all, and a
  checker that reports those is unusable on correct models, which is the
  failure mode that gets a linter switched off. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Types, RateLaw.Ast, RateLaw.Parser, RateLaw.Canonical,
  RateLaw.Registry, RateLaw.Bind, RateLaw.Associate, RateLaw.Diff,
  RateLaw.Dynamic;

{ Checks one reaction against one law, given a completed binding. }
procedure CheckAgainstLaw(ALaw: TRateLawDef; const AModel: IModelSource;
                          AIndex: Integer; ABind: TBindResult;
                          ADiags: TRateLawDiagnostics);

{ The law-independent checks: they need no association and no registry, so a
  model using laws nobody has registered still gets a useful report. }
{ AReportMissing is False when EVERY reaction in the model lacks a kinetic
  law, in which case CheckModel has already said so once for the model as a
  whole. See the S015 note there. }
procedure ModelLevelChecks(const AModel: IModelSource; AIndex: Integer;
                           ADiags: TRateLawDiagnostics;
                           AReportMissing: Boolean = True);

{ The whole model. The caller owns the result.

  ADynamic runs the behavioural checks as well as the structural ones. It is
  off by default because it is orders of magnitude more work -- thousands of
  evaluations per reaction against per law -- and because a caller doing a
  quick check while the user types wants neither the cost nor the extra
  findings. }
function CheckModel(ARegistry: TRateLawRegistry;
                    const AModel: IModelSource;
                    ADynamic: Boolean = False): TCheckResult;

implementation

{ ------------------------------------------------------------- classification }

procedure Emit(ADiags: TRateLawDiagnostics; const ACode: string;
  ASeverity: TSeverity; ALaw: TRateLawDef; const AReactionId: string;
  ALine: Integer; const AMessage, AFound, AExpected, ASuggestion: string);
var
  D: TRateLawDiagnostic;
begin
  D := Default(TRateLawDiagnostic);
  D.Code       := ACode;
  D.Severity   := ASeverity;
  D.ReactionId := AReactionId;
  D.SourceLine := ALine;
  D.Message    := AMessage;
  D.Found      := AFound;
  D.Expected   := AExpected;
  D.Suggestion := ASuggestion;
  if ALaw <> nil then D.LawId := ALaw.Id;
  ADiags.Add(D);
end;

procedure CheckAgainstLaw(ALaw: TRateLawDef; const AModel: IModelSource;
  AIndex: Integer; ABind: TBindResult; ADiags: TRateLawDiagnostics);
var
  Diffs: TList<TTreeDiff>;
  PreDiffs: TList<TTreeDiff>;
  BoundCanon, PreBound: TAstNode;
  Map: TDictionary<string, string>;
  D: TTreeDiff;
  RxId: string;
  Line: Integer;
  Equivalent: Boolean;
  Before: Integer;
  J: Integer;
  PreSubstitution: Boolean;
  Rearranged: Boolean;
  I: Integer;
  DupHandled: TStringList;
  MissingHandled: TStringList;
  ModelText, ExpectText: string;
  Role: TRole;
  S: string;
begin
  if (ABind = nil) or (ABind.Best = nil) or (ABind.BoundTree = nil) then Exit;
  if ALaw.Canon = nil then Exit;

  RxId := AModel.ReactionId(AIndex);
  Line := AModel.SourceLineOf(AIndex);

  { --- S007: the names say the roles are transposed --------------------- }
  { Reported before anything structural, because when it fires the structure
    is usually PERFECT: the binder found the shape by swapping the names, so
    there is no tree difference left to see. The naming is the only evidence
    there is. }
  if Length(ABind.Best.Suspicious) > 0 then
  begin
    ModelText := '';
    for S in ABind.Best.Suspicious do
    begin
      if ModelText <> '' then ModelText := ModelText + ', ';
      ModelText := ModelText + S;
    end;
    Emit(ADiags, 'S007', sevError, ALaw, RxId, Line,
      'the rate law has the right shape only if these names are read '
      + 'against their names; they look transposed',
      ModelText, ALaw.Expression,
      'check that each parameter is playing the role its name suggests');
  end;

  BoundCanon := Canonicalise(ABind.BoundTree);
  PreBound   := nil;
  Diffs      := TList<TTreeDiff>.Create;
  PreDiffs   := TList<TTreeDiff>.Create;
  DupHandled := TStringList.Create;
  MissingHandled := TStringList.Create;
  try
    Equivalent := Signature(BoundCanon) = Signature(ALaw.Canon);

    { An expression that canonicalises to the law is the law, however it was
      written. Nothing structural to say. }
    if Equivalent then Exit;

    Map := ABind.Best.AsMap;
    try
      PreBound := CloneRenamed(ABind.RawTree, Map);
    finally
      Map.Free;
    end;

    { The pre-canonical diff is computed up front now, because the canonical
      classification consults it. }
    DiffTrees(PreBound, ALaw.Expr, PreDiffs);
    PreSubstitution := False;
    for I := 0 to PreDiffs.Count - 1 do
      if (PreDiffs[I].Kind in [dfOperator, dfArity]) and
         SameChildMultiset(PreDiffs[I].ModelNode, PreDiffs[I].ExpectNode) then
      begin
        PreSubstitution := True;
        Break;
      end;

    Before := ADiags.Count;
    DiffTrees(BoundCanon, ALaw.Canon, Diffs);

    { Both sides unmatched, with the same ingredients on each: nothing lines
      up, so the parts were put together differently rather than changed. }
    Rearranged := ABind.Best.SameSymbols;
    if Rearranged then
    begin
      Rearranged := False;
      for I := 0 to Diffs.Count - 1 do
        if Diffs[I].Kind = dfExtra then
        begin
          for J := 0 to Diffs.Count - 1 do
            if Diffs[J].Kind = dfMissing then
            begin
              Rearranged := True;
              Break;
            end;
          Break;
        end;
    end;

    { --- canonical-tree findings ------------------------------------- }
    for D in Diffs do
      case D.Kind of

        dfDuplicate:
          begin
            { THE founding defect -- Vm*S/(Km + Km), and its Hill equivalent
              K^n + K^n. Named at the parent that holds both copies, so it
              reads the same whether the repeated operand is a leaf or a whole
              subtree. No law-specific code is involved in either. }
            ModelText := ToInfix(D.ModelNode);
            ExpectText := ToInfix(D.ExpectNode);
            Emit(ADiags, 'S004', sevError, ALaw, RxId, Line,
              Format('"%s" appears twice where "%s" and "%s" were expected',
                [ModelText, ModelText, ExpectText]),
              ToInfix(D.ModelParent), ToInfix(D.ExpectParent),
              Format('one of the two "%s" should be "%s"',
                [ModelText, ExpectText]));
            MissingHandled.Add(ExpectText);
          end;

        dfIdent:
          begin
            { Both are role names, in the same slot: the model put one role
              where another belongs. }
            Emit(ADiags, 'S007', sevError, ALaw, RxId, Line,
              Format('"%s" appears where "%s" was expected',
                [D.ModelNode.Name, D.ExpectNode.Name]),
              ToInfix(D.ModelParent), ToInfix(D.ExpectParent),
              Format('use "%s" here', [D.ExpectNode.Name]));
            MissingHandled.Add(D.ExpectNode.Name);
          end;

        dfExponent:
          Emit(ADiags, 'S008', sevError, ALaw, RxId, Line,
            'the exponent is not the one this law calls for',
            ToInfix(D.ModelNode), ToInfix(D.ExpectNode),
            Format('expected %s', [ToInfix(D.ExpectNode)]));

        dfLiteral:
          Emit(ADiags, 'S012', sevWarn, ALaw, RxId, Line,
            'a number appears here where this law expects a different value',
            ToInfix(D.ModelNode), ToInfix(D.ExpectNode), '');

        dfExtra:
          if Rearranged then
            { Reported once, below, as a regrouping. }
          else
            Emit(ADiags, 'S006', sevWarn, ALaw, RxId, Line,
              'this term is not part of the law',
              ToInfix(D.ModelNode), ToInfix(D.ExpectParent), '');

        dfMissing:
          if Rearranged then
            { Reported once, below, as a regrouping. }
          else
          begin
            ExpectText := ToInfix(D.ExpectNode);
            if MissingHandled.IndexOf(ExpectText) < 0 then
              Emit(ADiags, 'S005', sevError, ALaw, RxId, Line,
                'this part of the law is missing from the rate law',
                ToInfix(D.ModelParent), ExpectText,
                Format('add %s', [ExpectText]));
          end;

        dfOperator, dfArity:
          begin
            { Substitution when the differing node joins the same operands;
              regrouping when it does not.

              The question is asked of PreSubstitution, which was decided on
              the trees as written, not of the canonical nodes in hand.
              Canonicalisation flattens nested products, so a model's
              Mul(Mul(Km,X), S) becomes a three-operand product while the law
              still has a two-operand sum -- the operands then differ by
              arity alone and a genuine substitution reads as a regrouping.
              Before normalisation both nodes still hold exactly two
              operands and the comparison means what it says. }
            if PreSubstitution then
              Emit(ADiags, 'S003', sevError, ALaw, RxId, Line,
                'the right quantities, combined the wrong way',
                ToInfix(D.ModelNode), ToInfix(D.ExpectNode),
                Format('expected %s here', [ToInfix(D.ExpectNode)]))
            else
              Emit(ADiags, 'S010', sevError, ALaw, RxId, Line,
                'the right quantities, but bracketed differently from this law',
                AModel.RateLawText(AIndex), ALaw.Expression,
                Format('the law reads %s', [ALaw.Expression]));
          end;
      end;

    { A role nothing could fill is a term of the law with no counterpart in
      the expression at all -- which is what S005 says. Reported from the
      binding rather than the diff, because the diff can only compare what is
      there. }
    for S in ABind.Best.Unbound do
      Emit(ADiags, 'S005', sevError, ALaw, RxId, Line,
        Format('this law needs a %s, and the rate law has nothing that '
             + 'could be one', [S]),
        AModel.RateLawText(AIndex), S, '');

    { An expression built from exactly the law's symbols, whose parts no
      longer correspond to the law's at all, has been RE-ASSEMBLED rather than
      had pieces added and removed. Turning a fraction upside down is the
      clearest case: every ingredient is still there and nothing about
      "this term is not part of the law" describes what happened. }
    if Rearranged then
      Emit(ADiags, 'S010', sevError, ALaw, RxId, Line,
        'the law''s own quantities, but put together a different way',
        AModel.RateLawText(AIndex), ALaw.Expression,
        Format('the law reads %s', [ALaw.Expression]));

    { --- pre-canonical findings ---------------------------------------- }
    { Only when the canonical pass found nothing to say. Canonicalisation can
      cancel a defect out of existence, leaving a tree that differs from the
      law only by absence, and this is the pass that still has the operators
      to point at. When the canonical pass DID produce findings, running this
      one as well only says the same thing twice in different words. }
    if ADiags.Count = Before then
    begin
      for I := 0 to PreDiffs.Count - 1 do
        if PreDiffs[I].Kind in [dfOperator, dfArity] then
        begin
          Emit(ADiags, 'S003', sevError, ALaw, RxId, Line,
            'a different arithmetic sign from the one this law uses',
            ToInfix(PreDiffs[I].ModelNode), ToInfix(PreDiffs[I].ExpectNode),
            Format('expected %s here', [ToInfix(PreDiffs[I].ExpectNode)]));
          Break;
        end;
    end;

    { --- S011: an identifier whose name argues against its role --------- }
    { Only when the law actually publishes conventions for that role: a law
      with no opinion about names cannot have its conventions violated. }
    for I := 0 to ABind.Best.Count - 1 do
      if ABind.Best[I].Via = bvShape then
      begin
        if not ALaw.FindRole(ABind.Best[I].Role, Role) then Continue;
        if Length(Role.Aliases) = 0 then Continue;
        if Length(ABind.Best.Suspicious) > 0 then Continue;   { S007 said it }
        Emit(ADiags, 'S011', sevWarn, ALaw, RxId, Line,
          Format('"%s" plays the %s role, which is conventionally called %s',
            [ABind.Best[I].ModelName, ABind.Best[I].Role,
             string.Join(' or ', Role.Aliases)]),
          ABind.Best[I].ModelName, Role.Name, '');
      end;

  finally
    MissingHandled.Free;
    DupHandled.Free;
    PreDiffs.Free;
    Diffs.Free;
    PreBound.Free;
    BoundCanon.Free;
  end;
end;

{ ------------------------------------------------------- model-level checks }

procedure ModelLevelChecks(const AModel: IModelSource; AIndex: Integer;
  ADiags: TRateLawDiagnostics; AReportMissing: Boolean);
var
  Tree: TAstNode;
  Err, RxId: string;
  Line: Integer;
  Ident: string;
  Refs: TSpeciesRefs;
  I: Integer;
  Present: TArray<string>;
  Found: Boolean;
  J: Integer;
begin
  RxId := AModel.ReactionId(AIndex);
  Line := AModel.SourceLineOf(AIndex);

  if Trim(AModel.RateLawText(AIndex)) = '' then
  begin
    { Not when the whole model is like this -- CheckModel says so once instead.
      See AReportMissing at the call site. }
    if AReportMissing then
      Emit(ADiags, 'S015', sevError, nil, RxId, Line,
        'the reaction has no kinetic law', '', '', '');
    Exit;
  end;

  if not TryParseRateLaw(AModel.RateLawText(AIndex), Tree, Err) then
  begin
    Emit(ADiags, 'S016', sevError, nil, RxId, Line,
      'the kinetic law will not parse: ' + Err,
      AModel.RateLawText(AIndex), '', '');
    Exit;
  end;

  try
    Present := IdentifiersIn(Tree);

    { S014 -- referenced but undefined or uninitialised. Only asked when the
      model source can actually classify symbols; a source that cannot would
      otherwise report every name in every rate law as undefined. }
    if AModel.KnowsSymbolKinds then
      for Ident in Present do
      begin
        { time and pi are defined by the language, not by the model. }
        if IsBuiltInSymbol(Ident) then Continue;

        if AModel.SymbolKind(Ident) = skUnknown then
          Emit(ADiags, 'S014', sevError, nil, RxId, Line,
            Format('"%s" is used in the rate law but the model does not '
                 + 'define it', [Ident]), Ident, '', '')
        else if not AModel.HasValue(Ident) and
                (Trim(AModel.AssignmentRule(Ident)) = '') then
        begin
          { A SPECIES with no initial value is ordinary Antimony: it defaults
            to zero, which is a perfectly good initial condition and is what
            every intermediate in a chain is written as. Reporting it as an
            error made every one of Iridium's own example models fail, which
            is the exact false positive that gets a checker switched off.

            A PARAMETER or COMPARTMENT with no value is a different matter --
            there is no sensible default and the rate law genuinely cannot be
            evaluated.

            Unless a rule computes it, which is the condition on the test
            above. A parameter defined by an assignment rule HAS no literal
            value and does not need one: the rule is its value. Over the
            BioModels corpus this was every S014 that was not a genuinely
            undefined symbol -- 147 findings across 18 models, all wrong.
            This is the narrow half of M8; resolving such a symbol THROUGH
            its rule, so the expression can be compared as the modeller meant
            it, is still not built, and a rate law that refers to one is
            still compared as written. }
          if AModel.SymbolKind(Ident) = skSpecies then
            Emit(ADiags, 'S018', sevInfo, nil, RxId, Line,
              Format('"%s" has no initial value, so it starts at zero',
                [Ident]), Ident, '', '')
          else
            Emit(ADiags, 'S014', sevError, nil, RxId, Line,
              Format('"%s" is declared with no value at all, so the rate law '
                   + 'cannot be evaluated', [Ident]), Ident, '',
              Format('give %s a value', [Ident]));
        end;
      end;

    { A reactant that the rate law never mentions. Legitimate occasionally --
      a zero-order step -- so a warning, not an error.

      A species held constant is exempt, and not as a concession: clamping a
      species IS the statement that the kinetics do not vary with it, so its
      absence from the rate law is the correct way to write it, not an
      omission. Over the BioModels corpus this was 78% of every S017 -- 313 of
      400 sampled were SBML boundary species, and every one of those findings
      was wrong. }
    Refs := AModel.Reactants(AIndex);
    for I := 0 to High(Refs) do
    begin
      if AModel.IsConstant(Refs[I].Name) then Continue;
      { Nor EmptySet, which is not consumed because it is not there. }
      if IsNullSpecies(Refs[I].Name) then Continue;
      Found := False;
      for J := 0 to High(Present) do
        if Present[J] = Refs[I].Name then
        begin
          Found := True;
          Break;
        end;
      if not Found then
        Emit(ADiags, 'S017', sevWarn, nil, RxId, Line,
          Format('"%s" is consumed by this reaction but does not appear in '
               + 'its rate law', [Refs[I].Name]),
          AModel.RateLawText(AIndex), Refs[I].Name,
          Format('add "%s" to the rate law, if the rate should depend on it',
                 [Refs[I].Name]));
    end;
  finally
    Tree.Free;
  end;
end;

{ ---------------------------------------------------------------- CheckModel }

function CheckModel(ARegistry: TRateLawRegistry;
  const AModel: IModelSource; ADynamic: Boolean): TCheckResult;
var
  I, J: Integer;
  Law: TRateLawDef;
  Res: TBindResult;
  Assoc: TAssociation;
  Held: TObjectList<TBindResult>;
  Cands: TArray<TAssocCandidate>;
  C: TAssocCandidate;
  Decision: TAssocDecision;
  RxId, Annotated: string;
  Line: Integer;
  WithLaws: Integer;
  ReportMissing: Boolean;
begin
  Result := TCheckResult.Create;

  for I := 0 to ARegistry.Count - 1 do
    if ARegistry[I].Enabled and ARegistry[I].Valid then
      Result.LawsApplied.Add(ARegistry[I].Id);

  { A model with NO kinetics anywhere is not a model with thousands of defects
    -- it is a model this checker has nothing to say about, and saying so once
    is the whole of the truth. Genome-scale reconstructions are the case:
    eleven of them produced 18245 findings between them in the M17 corpus run,
    48% of everything the checker emitted, one of them 4058 times in a single
    file. A reaction missing its kinetics AMONG reactions that have theirs is a
    different statement and is still reported one by one. }
  WithLaws := 0;
  for I := 0 to AModel.ReactionCount - 1 do
    if Trim(AModel.RateLawText(I)) <> '' then Inc(WithLaws);
  ReportMissing := (WithLaws > 0) or (AModel.ReactionCount = 0);

  if not ReportMissing then
    Emit(Result.Diagnostics, 'S015', sevError, nil, '', -1,
      Format('no reaction in this model has a kinetic law, so there is '
           + 'nothing for a rate law checker to look at (%d reactions)',
             [AModel.ReactionCount]), '', '',
      'this is normal for a constraint-based or genome-scale model');

  for I := 0 to AModel.ReactionCount - 1 do
  begin
    RxId      := AModel.ReactionId(I);
    Line      := AModel.SourceLineOf(I);
    Annotated := Trim(AModel.AnnotatedLaw(I));

    ModelLevelChecks(AModel, I, Result.Diagnostics, ReportMissing);

    { Does this rate law work for THIS model, as written? Everything else in
      the behavioural layer tests the law over a grid of its own and never
      reads the model's numbers, so a rate law that divides by a species the
      model starts at zero goes unreported by all of it. Needs no
      association, so it runs before any law is chosen. }
    if ADynamic then
      CheckAtInitialState(AModel, I, Result.Diagnostics);

    { Every bind result is kept alive until the winner has been used: the
      result owns the trees the static engine reads. }
    Held  := TObjectList<TBindResult>.Create(True);
    Cands := nil;
    try
      for J := 0 to ARegistry.Count - 1 do
      begin
        Law := ARegistry[J];
        if not (Law.Enabled and Law.Valid) then Continue;

        Res := BindReaction(Law, AModel, I);
        Held.Add(Res);

        { An applicability failure is only worth carrying when the modeller
          ASSERTED this law -- then it is defect S013. Otherwise the law
          simply is not a candidate and there is nothing to say about it. }
        if Res.Outcome = boNotApplicable then
        begin
          if SameText(Law.Id, Annotated) then
          begin
            C := Default(TAssocCandidate);
            C.LawId := Law.Id; C.Index := Held.Count - 1;
            C.Distance := 1; C.Score := 1;
            C.Applies := False; C.Why := Res.Reason;
            Cands := Cands + [C];
          end;
          Continue;
        end;

        if Res.Outcome <> boBound then Continue;

        C := Default(TAssocCandidate);
        C.LawId    := Law.Id;
        C.Index    := Held.Count - 1;
        C.Distance := Res.Best.Distance;
        C.Score    := Res.Best.Score;
        C.Floor    := Law.AssociationFloor;
        C.Applies     := True;
        C.SameSymbols   := Res.Best.SameSymbols;
        C.SymbolsSubset := Res.Best.SymbolsSubset;
        { From the law as it will actually be compared -- an instantiated
          generative law has as many roles as this reaction gave it, which is
          exactly the specificity that matters here. }
        C.Specificity := Res.EffectiveLaw(Law).RoleCount;
        Cands      := Cands + [C];
      end;

      Decision := DecideAssociation(Cands, Annotated);

      Assoc            := Default(TAssociation);
      Assoc.ReactionId := RxId;
      Assoc.LawId      := Decision.LawId;
      Assoc.Detail     := Decision.Detail;

      case Decision.Outcome of

        aoNone:
          begin
            Assoc.Kind := akNone;
            Emit(Result.Diagnostics, 'S001', sevInfo, nil, RxId, Line,
              'no registered rate law matches this reaction', '', '', '');
          end;

        aoAmbiguous:
          begin
            { Nothing is checked. Reporting against the nearer of two laws
              that fit equally well describes the defect in terms of a law the
              modeller never had in mind, which is worse than saying only
              that the choice is unclear. }
            Assoc.Kind   := akAmbiguous;
            Assoc.Detail := Decision.Detail;
            Emit(Result.Diagnostics, 'S002', sevWarn, nil, RxId, Line,
              'more than one registered law fits this reaction equally well, '
              + 'so none was applied',
              string.Join(', ', Decision.Rivals), '',
              'annotate the reaction with "# @ratelaw <id>" to say which');
          end;

        aoAnnotatedBad:
          begin
            Assoc.Kind := akAnnotated;
            if Decision.Chosen < 0 then
            begin
              Emit(Result.Diagnostics, 'S019', sevWarn, nil, RxId, Line,
                Format('the annotation names "%s", which is not a registered, '
                     + 'enabled law that can apply here', [Annotated]),
                Annotated, '', '');
            end
            else
            begin
              { Declared, but the reaction's own structure contradicts it.
                Checked anyway: the contradiction is the finding. }
              Law := ARegistry.Find(Decision.LawId);
              Emit(Result.Diagnostics, 'S013', sevError, Law, RxId, Line,
                Format('this reaction is annotated as "%s", but %s',
                       [Decision.LawId, Decision.Detail]),
                '', '', '');
              if Law <> nil then
                CheckAgainstLaw(Held[Decision.Chosen].EffectiveLaw(Law),
                                AModel, I, Held[Decision.Chosen],
                                Result.Diagnostics);
            end;
          end;

        aoAnnotated, aoInferred:
          begin
            if Decision.Outcome = aoAnnotated then Assoc.Kind := akAnnotated
            else Assoc.Kind := akInferred;
            Law := ARegistry.Find(Decision.LawId);
            if Law <> nil then
            begin
              CheckAgainstLaw(Held[Decision.Chosen].EffectiveLaw(Law),
                              AModel, I, Held[Decision.Chosen],
                              Result.Diagnostics);
              { The behavioural half. Run against the reaction's OWN
                expression in role vocabulary, not against the law's -- the
                whole point is to find where the model's version fails a
                property the law guarantees. }
              if ADynamic then
              begin
                CheckInvariants(Held[Decision.Chosen].EffectiveLaw(Law),
                                Held[Decision.Chosen].BoundTree,
                                RxId, Line, Result.Diagnostics);
                { Layer 2. Runs after the invariants so that, where the two
                  turn out to compute the same rate, the note saying so sits
                  below the structural findings it explains away. }
                CompareWithCanonical(Held[Decision.Chosen].EffectiveLaw(Law),
                                     Held[Decision.Chosen].BoundTree,
                                     RxId, Line, Result.Diagnostics);
              end;
            end;
          end;
      end;

      Result.Associations.Add(Assoc);
    finally
      Held.Free;
    end;
  end;
end;

end.
