program ModelCheckerLib_Project;

{ Console harness for the model checker. See README.md for the library itself.

  With no arguments it runs the whole suite -- canonicalisation pairs, registry
  loading and layering, role binding, then the model corpus -- and ends with a
  pass/fail line. Everything else selects one part of that, or one case:

    ModelCheckerLib_Project              the whole suite
    ModelCheckerLib_Project -canon       canonicalisation pairs only
    ModelCheckerLib_Project -registry    registry loading and layering only
    ModelCheckerLib_Project -bind        role binding over every corpus case
    ModelCheckerLib_Project -bind NAME   ...for one case: which law each
                                         candidate binds to, and how far off
    ModelCheckerLib_Project -list        the corpus, and why each case exists
    ModelCheckerLib_Project -show NAME   one case rendered through IModelSource
    ModelCheckerLib_Project -check NAME  one case checked, in full
    ModelCheckerLib_Project -laws        every registered law, and whether it
                                         validates against its own invariants
    ModelCheckerLib_Project -coverage    the mutation matrix, per law
    ModelCheckerLib_Project -stress      an alias for -coverage
    ModelCheckerLib_Project -expr EXPR   parse one expression, dump both trees

  The library itself depends on nothing but the RTL -- no FMX, no libantimony,
  no libRoadRunner. That constraint is what keeps it testable here and reusable
  later, and it is the reason this project exists separately from Iridium at
  all: Iridium has no test suite, and the mutation harness that measures the
  static engine's coverage cannot live there.

  Cases compare diagnostic CODES, not message text, so wording can keep
  improving without breaking tests -- and a code not listed by a case fails it,
  so a rule cannot quietly gain a diagnostic without someone noticing.

  -coverage is the measurement that matters most and the one to run after any
  engine change. It mutates each law's own canonical expression in a known way
  and asks whether the engine names the break correctly, so the mutation kind
  IS the expected defect class and nobody gets to decide after the fact that
  whatever came out was close enough. Note that a green suite here is NOT
  evidence the checker is ready: these cases are expressions written as laws,
  real models are SBML, and the two disagree about what a rate law looks like.
  The corpus stayed green through fixes that made the real numbers worse. }

{$APPTYPE CONSOLE}

uses
  System.SysUtils,
  System.Classes,
  RateLaw.Types in 'RateLaw.Types.pas',
  RateLaw.Ast in 'RateLaw.Ast.pas',
  RateLaw.Parser in 'RateLaw.Parser.pas',
  RateLaw.Canonical in 'RateLaw.Canonical.pas',
  RateLaw.BuiltInLaws in 'RateLaw.BuiltInLaws.pas',
  RateLaw.Diff in 'RateLaw.Diff.pas',
  RateLaw.Registry in 'RateLaw.Registry.pas',
  RateLaw.Bind in 'RateLaw.Bind.pas',
  RateLaw.Associate in 'RateLaw.Associate.pas',
  RateLaw.Eval in 'RateLaw.Eval.pas',
  RateLaw.Dynamic in 'RateLaw.Dynamic.pas',
  RateLaw.Static in 'RateLaw.Static.pas',
  RateLaw.Mutate in 'RateLaw.Mutate.pas',
  RateLaw.Generative in 'RateLaw.Generative.pas',
  RateLaw.HardLaws in 'RateLaw.HardLaws.pas',
  RateLaw.TestCorpus in 'RateLaw.TestCorpus.pas',
  System.IOUtils;

var
  GFailures: Integer = 0;

procedure Fail(const AWhat, AWhy: string);
begin
  Inc(GFailures);
  Writeln('  FAIL    ', AWhat);
  if AWhy <> '' then
    Writeln('          why: ', AWhy);
end;

{ ------------------------------------------------------------------ }

procedure ListCases;
var
  C: TRateLawTestCase;
begin
  Writeln(Format('%d model case(s).', [Length(Corpus)]));
  Writeln;
  for C in Corpus do
  begin
    Writeln('  ', C.Name);
    if Length(C.Expect) = 0 then
      Writeln('    expects : (no diagnostics)')
    else
      Writeln('    expects : ', string.Join(', ', C.Expect));
    Writeln('    why     : ', C.Why);
    Writeln;
  end;
end;

procedure ShowCase(const AName: string);
var
  C: TRateLawTestCase;
  Src: IModelSource;
begin
  for C in Corpus do
    if SameText(C.Name, AName) then
    begin
      { Held as the interface so the reference count owns it: the fixture is a
        TInterfacedObject, and freeing it by hand as well would be a double
        free the moment anything else takes a reference. }
      Src := C.Build();
      Writeln('Case: ', C.Name);
      Writeln('Why : ', C.Why);
      Writeln;
      Writeln(DescribeModel(Src));
      Exit;
    end;
  Writeln('No such case: ', AName);
  Writeln('Use -list to see them.');
end;

procedure ShowExpression(const AExpr: string);
var
  Raw, Canon: TAstNode;
  Err: string;
begin
  if not TryParseRateLaw(AExpr, Raw, Err) then
  begin
    Writeln('Will not parse: ', Err);
    ExitCode := 1;
    Exit;
  end;
  try
    Canon := Canonicalise(Raw);
    try
      Writeln('source     : ', AExpr);
      Writeln;
      Writeln('parsed     : ', ToInfix(Raw));
      Writeln('  tree     : ', Signature(Raw));
      Writeln;
      Writeln('canonical  : ', ToInfix(Canon));
      Writeln('  tree     : ', Signature(Canon));
      Writeln;
      Writeln('identifiers: ', string.Join(', ', IdentifiersIn(Canon)));
    finally
      Canon.Free;
    end;
  finally
    Raw.Free;
  end;
end;

{ ------------------------------------------------------------------ }

procedure RunCanonPairs;
var
  Pr: TExprPair;
  N: Integer;
begin
  Writeln('Canonicalisation -- pairs that must agree');
  Writeln('----------------------------------------');
  N := 0;
  for Pr in EquivalentPairs do
  begin
    if CanonicallyEqual(Pr.A, Pr.B) then
      Inc(N)
    else
      Fail(Format('%-24s  =/=  %s', [Pr.A, Pr.B]), Pr.Why + sLineBreak
        + '          ' + Pr.A + ' -> ' + CanonicalSignature(Pr.A) + sLineBreak
        + '          ' + Pr.B + ' -> ' + CanonicalSignature(Pr.B));
  end;
  Writeln(Format('  %d/%d agreed.', [N, Length(EquivalentPairs)]));
  Writeln;

  Writeln('Canonicalisation -- pairs that must stay different');
  Writeln('-------------------------------------------------');
  N := 0;
  for Pr in DistinctPairs do
  begin
    if not CanonicallyEqual(Pr.A, Pr.B) then
      Inc(N)
    else
      Fail(Format('%-24s  ==   %s   (collapsed!)', [Pr.A, Pr.B]), Pr.Why);
  end;
  Writeln(Format('  %d/%d stayed distinct.', [N, Length(DistinctPairs)]));
  Writeln;

  Writeln('Parser -- expressions that must be rejected');
  Writeln('------------------------------------------');
  N := 0;
  for var Bad in MalformedExpressions do
  begin
    var Node: TAstNode := nil;
    var Err: string;
    if TryParseRateLaw(Bad, Node, Err) then
    begin
      Fail(Format('"%s" parsed as %s', [Bad, ToInfix(Node)]),
           'A malformed expression must be reported, not silently given a tree.');
      Node.Free;
    end
    else
      Inc(N);
  end;
  Writeln(Format('  %d/%d rejected.', [N, Length(MalformedExpressions)]));
  Writeln;
end;

procedure RunRegistry;
var
  Reg, Reg2: TRateLawRegistry;
  Law: TRateLawDef;
  Bad: TBadLawCase;
  TempDir: string;
  I, N: Integer;
  D: TRateLawDiagnostic;
  Before, After, Suffix, GotCodes: string;
begin
  Writeln('Registry -- built-in laws load and validate');
  Writeln('------------------------------------------');
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    for I := 0 to Reg.Count - 1 do
    begin
      Law := Reg[I];
      if Law.Valid then
      begin
        Suffix := '';
        if Law.Generative then Suffix := ', generative';
        Writeln(Format('  ok      %-24s %d role(s), %d invariant(s)%s',
          [Law.Id, Law.RoleCount, Law.Invariants.Count, Suffix]));
      end
      else
        Fail(Law.Id, 'A built-in law failed its own validation: '
             + string.Join('; ', Law.Problems));
    end;

    { Errors here would mean a shipped law is broken. Info-level R014 is
      expected -- it records that invariant satisfaction is not yet checked. }
    for D in Reg.LoadDiagnostics do
      if D.Severity = sevError then
        Fail('built-in ' + D.LawId, D.Code + ' ' + D.Message);

    Writeln(Format('  %d law(s), %d active.', [Reg.Count, Reg.ActiveCount]));
    Writeln;

    { --- round trip --- }
    Writeln('Registry -- round trip through disk');
    Writeln('-----------------------------------');
    TempDir := TPath.Combine(TPath.GetTempPath, 'ratelaw_roundtrip');
    try
      if TDirectory.Exists(TempDir) then
        TDirectory.Delete(TempDir, True);
      Reg.SaveToDirectory(TempDir);

      Reg2 := TRateLawRegistry.Create;
      try
        { Loaded as a user layer with no built-ins, so what comes back is
          purely what was written. }
        Reg2.LoadDirectory(TempDir, rlUser);

        if Reg2.Count <> Reg.Count then
          Fail('round-trip', Format('wrote %d law(s), read back %d',
               [Reg.Count, Reg2.Count]))
        else
        begin
          N := 0;
          for I := 0 to Reg.Count - 1 do
          begin
            Law := Reg2.Find(Reg[I].Id);
            if Law = nil then
            begin
              Fail('round-trip', Reg[I].Id + ' did not come back');
              Continue;
            end;
            Before := Reg[I].ToJsonText;
            After  := Law.ToJsonText;
            if Before <> After then
              Fail('round-trip ' + Reg[I].Id,
                   'the re-read entry does not serialise identically')
            else
              Inc(N);
          end;
          Writeln(Format('  %d/%d law(s) round-tripped unchanged.', [N, Reg.Count]));
        end;
      finally
        Reg2.Free;
      end;
    finally
      if TDirectory.Exists(TempDir) then
        TDirectory.Delete(TempDir, True);
    end;
    Writeln;

    { --- enable / disable --- }
    Writeln('Registry -- enable and disable');
    Writeln('------------------------------');
    N := Reg.ActiveCount;
    Reg.Disable('hill_activation');
    if Reg.ActiveCount <> N - 1 then
      Fail('disable', 'disabling a law did not remove it from the active set')
    else
      Writeln('  ok      disable removes a law from the active set');
    Reg.Enable('hill_activation');
    if Reg.ActiveCount <> N then
      Fail('enable', 'enabling a law did not put it back')
    else
      Writeln('  ok      enable puts it back');
    { A built-in must be disable-able but never deletable by disabling. }
    if Reg.Find('hill_activation') = nil then
      Fail('disable', 'disabling deleted the entry instead of flagging it');
    Writeln;
  finally
    Reg.Free;
  end;

  { --- self-validation rejects bad entries --- }
  Writeln('Registry -- entries that must be rejected');
  Writeln('----------------------------------------');
  N := 0;
  for Bad in BadLawEntries do
  begin
    Reg := TRateLawRegistry.Create;
    try
      Law := Reg.AddFromJsonText(Bad.Json, rlUser, Bad.Name + '.json');

      if not Reg.LoadDiagnostics.HasCode(Bad.Code) then
      begin
        if Reg.LoadDiagnostics.Count = 0 then
          GotCodes := '(nothing)'
        else
          GotCodes := string.Join(', ', Reg.LoadDiagnostics.Codes);
        Fail(Format('%s (wanted %s)', [Bad.Name, Bad.Code]),
             Bad.Why + sLineBreak + '          got: ' + GotCodes);
      end
      else if (Law <> nil) and Law.Valid and (Bad.Code <> 'R003') then
        { R003 covers both fatal and advisory problems; the others must all
          be fatal, or a broken law still participates in checking. }
        Fail(Bad.Name, 'reported ' + Bad.Code
             + ' but the law is still marked valid and would be used')
      else if Reg.ActiveCount > 0 then
        Fail(Bad.Name, 'a rejected law is still in the active set')
      else
        Inc(N);
    finally
      Reg.Free;
    end;
  end;
  Writeln(Format('  %d/%d rejected with the right code.',
                 [N, Length(BadLawEntries)]));
  Writeln;
end;

{ A statement, not an expression: every outcome that produced no binding has a
  nil Best, and choosing between Best.Describe and the reason text by any means
  that evaluates both arms up front dereferences that nil. }
function BindSummary(ARes: TBindResult; AWithDistance: Boolean): string;
begin
  if ARes.Best = nil then
    Exit(ARes.Reason);
  if AWithDistance then
    Result := Format('d=%.3f  %s', [ARes.Best.Distance, ARes.Best.Describe])
  else
    Result := ARes.Best.Describe;
end;

procedure RunBinding;
var
  Reg: TRateLawRegistry;
  Law: TRateLawDef;
  Src: IModelSource;
  Res: TBindResult;
  BC: TBindCase;
  N, I: Integer;
  Got, Want: string;
begin
  Writeln('Role binding');
  Writeln('------------');
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    N := 0;

    for BC in BindCases do
    begin
      Law := Reg.Find(BC.LawId);
      if Law = nil then
      begin
        Fail(BC.Name, 'no such law: ' + BC.LawId);
        Continue;
      end;

      Src := BC.Build();
      Res := BindReaction(Law, Src, 0);
      try
        if Res.Outcome <> BC.Outcome then
        begin
          Fail(BC.Name, Format('%s, wanted %s. %s',
            [OutcomeName(Res.Outcome), OutcomeName(BC.Outcome), Res.Reason])
            + sLineBreak + '          ' + BC.Why);
          Continue;
        end;

        { Where a binding was expected, it must be the RIGHT binding. An
          outcome of "bound" with the parameters transposed is worse than no
          binding at all, because everything downstream trusts it. }
        if (BC.Outcome = boBound) and (Length(BC.Expect) > 0) then
        begin
          Got := '';
          for I := 0 to Res.Best.Count - 1 do
          begin
            if I > 0 then Got := Got + ',';
            Got := Got + Res.Best[I].Role + '=' + Res.Best[I].ModelName;
          end;
          Want := string.Join(',', BC.Expect);
          if Got <> Want then
          begin
            Fail(BC.Name, Format('bound [%s], wanted [%s]', [Got, Want])
                 + sLineBreak + '          ' + BC.Why);
            Continue;
          end;
        end;

        if BC.Suspicious and ((Res.Best = nil) or (Length(Res.Best.Suspicious) = 0)) then
        begin
          Fail(BC.Name, 'the binding should have been flagged as suspicious: '
               + BC.Why);
          Continue;
        end;

        Writeln(Format('  ok      %-26s %s',
          [BC.Name, BindSummary(Res, False)]));
        Inc(N);
      finally
        Res.Free;
        Src := nil;
      end;
    end;

    Writeln(Format('  %d/%d bound as expected.', [N, Length(BindCases)]));
    Writeln;
  finally
    Reg.Free;
  end;
end;

procedure ShowBinding(const ACaseName: string);
var
  Reg: TRateLawRegistry;
  Src: IModelSource;
  Res: TBindResult;
  C: TRateLawTestCase;
  I, J: Integer;
  Found: Boolean;
begin
  Found := False;
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    for I := 0 to High(HardLaws) do
      Reg.AddFromJsonText(HardLaws[I], rlUser, 'hard.json');
    for C in Corpus do
      if SameText(C.Name, ACaseName) then
      begin
        Found := True;
        Src := C.Build();
        Writeln('Case: ', C.Name);
        Writeln;
        for I := 0 to Src.ReactionCount - 1 do
        begin
          Writeln(Format('  %s : %s',
            [Src.ReactionId(I), Src.RateLawText(I)]));
          for J := 0 to Reg.Count - 1 do
          begin
            Res := BindReaction(Reg[J], Src, I);
            try
              Writeln(Format('    %-24s %-14s %s',
                [Reg[J].Id, OutcomeName(Res.Outcome), BindSummary(Res, True)]));
              if (Res.Best <> nil) and (Length(Res.Best.Suspicious) > 0) then
                Writeln('        suspicious: ',
                        string.Join('; ', Res.Best.Suspicious));
            finally
              Res.Free;
            end;
          end;
          Writeln;
        end;
        Src := nil;
      end;
    if not Found then
      Writeln('No such case: ', ACaseName);
  finally
    Reg.Free;
  end;
end;

procedure ListLaws;
var
  Reg: TRateLawRegistry;
  Law: TRateLawDef;
  I: Integer;
  P: string;
begin
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    for I := 0 to Reg.Count - 1 do
    begin
      Law := Reg[I];
      Writeln(Format('%-24s %s', [Law.Id, Law.LawName]));
      Writeln('  expression : ', Law.Expression);
      if Law.Canon <> nil then
        Writeln('  canonical  : ', ToInfix(Law.Canon));
      Writeln('  roles      : ', Law.RoleCount,
              '   invariants: ', Law.Invariants.Count,
              '   enabled: ', BoolToStr(Law.Enabled, True),
              '   valid: ', BoolToStr(Law.Valid, True));
      for P in Law.Problems do
        Writeln('  note       : ', P);
      Writeln;
    end;
  finally
    Reg.Free;
  end;
end;

procedure RunModelCases;
var
  C: TRateLawTestCase;
  Src: IModelSource;
  Reg: TRateLawRegistry;
  Res: TCheckResult;
  D: TRateLawDiagnostic;
  Got: TStringList;
  I, N: Integer;
  GotText, WantText: string;
begin
  Writeln('Model corpus');
  Writeln('------------');
  N := 0;
  Reg := nil;
  try
    for C in Corpus do
    begin
      { A registry per case. What else is registered changes the answer --
        ambiguity exists only relative to the alternatives -- so one shared
        registry cannot express the cases that matter most. The hard laws are
        always present so that association has real rivals to choose between;
        with only the three built-ins, almost nothing competes and the margin
        would never be exercised. }
      FreeAndNil(Reg);
      Reg := TRateLawRegistry.Create;
      Reg.LoadBuiltIns;
      for I := 0 to High(HardLaws) do
        Reg.AddFromJsonText(HardLaws[I], rlUser, 'hard.json');
      for I := 0 to High(C.ExtraLaws) do
        Reg.AddFromJsonText(C.ExtraLaws[I], rlUser, 'case.json');

      Src := C.Build();
      Res := CheckModel(Reg, Src, C.Dynamic);
      Got := TStringList.Create;
      try
        { INFO codes are excluded from the comparison. S001 says "no
          registered law matches", which is a statement about the registry's
          coverage rather than about the model -- a case that legitimately has
          no law yet would otherwise look like a failure forever. What the
          corpus asserts is that a correct model produces no WARNING and no
          ERROR. }
        Got.Sorted := True;
        Got.Duplicates := dupIgnore;
        for D in Res.Diagnostics do
          if D.Severity <> sevInfo then
            Got.Add(D.Code);

        GotText  := '';
        for I := 0 to Got.Count - 1 do
        begin
          if I > 0 then GotText := GotText + ',';
          GotText := GotText + Got[I];
        end;
        WantText := string.Join(',', C.Expect);

        if GotText = WantText then
        begin
          if GotText = '' then
            Writeln(Format('  ok      %-26s clean', [C.Name]))
          else
            Writeln(Format('  ok      %-26s [%s]', [C.Name, GotText]));
          Inc(N);
        end
        else
        begin
          if GotText = '' then GotText := '(nothing)';
          if WantText = '' then WantText := '(nothing)';
          Fail(C.Name, Format('reported [%s], expected [%s]',
                              [GotText, WantText])
               + sLineBreak + '          ' + C.Why);
          for D in Res.Diagnostics do
            if D.Severity <> sevInfo then
              Writeln('            ', D.ToString);
        end;
      finally
        Got.Free;
        Res.Free;
        Src := nil;
      end;
    end;

    Writeln(Format('  %d/%d model case(s) as expected.', [N, Length(Corpus)]));
    Writeln;
  finally
    Reg.Free;
  end;
end;

procedure ShowCheck(const ACaseName: string);
var
  C: TRateLawTestCase;
  Src: IModelSource;
  Reg: TRateLawRegistry;
  Res: TCheckResult;
  D: TRateLawDiagnostic;
  A: TAssociation;
begin
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    for C in Corpus do
      if SameText(C.Name, ACaseName) then
      begin
        Src := C.Build();
        Res := CheckModel(Reg, Src, C.Dynamic);
        try
          Writeln('Case: ', C.Name);
          Writeln('Why : ', C.Why);
          Writeln;
          for A in Res.Associations do
            Writeln(Format('  %s -> %s   %s',
              [A.ReactionId, A.LawId, A.Detail]));
          Writeln;
          if Res.Diagnostics.Count = 0 then
            Writeln('  no findings.')
          else
            for D in Res.Diagnostics do
              Writeln('  ', D.ToString);
          Writeln;
          Writeln(Format('  %d error(s), %d warning(s).',
                         [Res.ErrorCount, Res.WarningCount]));
        finally
          Res.Free;
          Src := nil;
        end;
        Exit;
      end;
    Writeln('No such case: ', ACaseName);
  finally
    Reg.Free;
  end;
end;


{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }

{ Mutation coverage.

  Take every law the registry holds, build a reaction from its own roles,
  break that reaction in each of the ways a person breaks one, and see whether
  the engine names the break correctly. The mutation kind IS the expected
  defect code, so "close enough" is not on offer.

  Run over the REGISTRY rather than a hand-written list of laws. A fixture
  written per law is a fixture that has to be written before the law can be
  measured, which in practice means laws get added and never measured.

  Three outcomes per cell, and they mean quite different things:

    ok        the mutation was detected AND classified correctly
    partial   detected, but reported as a different defect. Not a hole -- the
              user is still told something is wrong -- but the message names
              the wrong thing
    MISSED    not detected at all. The only outcome that is a hole
    -         the law cannot express this mutation (no power to change, no
              division to invert). A gap in the CORPUS, not in the engine,
              and the two must not be confused }

type
  TCell = (cNA, cMissed, cPartial, cOk);

function CellText(ACell: TCell): string;
begin
  case ACell of
    cOk:      Result := 'ok';
    cPartial: Result := 'part';
    cMissed:  Result := 'MISS';
  else        Result := '-';
  end;
end;

procedure RunCoverage;
var
  Reg: TRateLawRegistry;
  Law: TRateLawDef;
  Kinds: TArray<string>;
  Cells: array of array of TCell;
  LawIds: TArray<string>;
  Rows, K, I, J: Integer;
  Muts: TArray<TMutation>;
  M: TMutation;
  Src: IModelSource;
  Model: TFixtureModel;
  Res: TCheckResult;
  D: TRateLawDiagnostic;
  Codes: TStringList;
  Got, Header, Row, Base: string;
  Inst: TRateLawDef;
  Reason: string;
  Detected, Exact, Total, NA, CleanOk, CleanTotal: Integer;
  Notes: TStringList;
begin
  Kinds := MutationKinds;
  Detected := 0; Exact := 0; Total := 0; NA := 0;
  CleanOk := 0; CleanTotal := 0;
  Notes := TStringList.Create;

  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadBuiltIns;
    for I := 0 to High(HardLaws) do
      Reg.AddFromJsonText(HardLaws[I], rlUser, 'hard.json');

    LawIds := nil;
    for I := 0 to Reg.Count - 1 do
      if Reg[I].Enabled and Reg[I].Valid then
        LawIds := LawIds + [Reg[I].Id];

    Rows := Length(LawIds);
    SetLength(Cells, Rows, Length(Kinds));
    for I := 0 to Rows - 1 do
      for J := 0 to High(Kinds) do
        Cells[I][J] := cNA;

    Writeln('Mutation coverage');
    Writeln('=================');
    Writeln;

    for I := 0 to Rows - 1 do
    begin
      Law := Reg.Find(LawIds[I]);

      { A family has no expression to mutate until a reaction gives it one, so
        it is instantiated against a model built for it and the concrete form
        is what gets broken. Without this the commonest law in biology would
        sit outside the measurement entirely. }
      Base := Law.Expression;
      Model := ModelForLaw(Law);
      Src := Model;
      if Law.Generative then
      begin
        Inst := nil;
        if InstantiateGenerative(Law, Src, 0, Inst, Reason) then
        try
          Base := Inst.Expression;
        finally
          Inst.Free;
        end;
      end;
      Src := nil;

      { The correct form first. A checker that flags a correctly written law
        is worse than one that misses a defect, so this half of the
        measurement matters more than the other. }
      Inc(CleanTotal);
      Model := ModelForLaw(Law, Base);
      Src := Model;
      Res := CheckModel(Reg, Src);
      try
        Got := '';
        for D in Res.Diagnostics do
          if D.Severity <> sevInfo then Got := Got + D.Code + ' ';
        if Got = '' then Inc(CleanOk)
        else
        begin
          Fail(Law.Id + ' (correct form)',
               'a correctly written law was flagged: ' + Got);
          Notes.Add(Format('  %s: the correct form reports %s',
                           [Law.Id, Trim(Got)]));
        end;
      finally
        Res.Free;
        Src := nil;
      end;

      Muts := MutationsOf(Base);
      for M in Muts do
      begin
        K := -1;
        for J := 0 to High(Kinds) do
          if Kinds[J] = M.Kind then begin K := J; Break; end;
        if K < 0 then Continue;

        Inc(Total);
        Model := ModelForLaw(Law, M.Expr);
        Src := Model;
        Res := CheckModel(Reg, Src);
        Codes := TStringList.Create;
        try
          Codes.Sorted := True;
          Codes.Duplicates := dupIgnore;
          for D in Res.Diagnostics do
            if D.Severity <> sevInfo then Codes.Add(D.Code);

          if Codes.Count = 0 then
          begin
            Cells[I][K] := cMissed;
            Notes.Add(Format('  MISSED  %-24s %-9s %s',
                             [Law.Id, M.Kind, M.Expr]));
          end
          else
          begin
            Inc(Detected);
            if Codes.IndexOf(M.Expected) >= 0 then
            begin
              Cells[I][K] := cOk;
              Inc(Exact);
            end
            else
            begin
              Cells[I][K] := cPartial;
              Notes.Add(Format('  partial %-24s %-9s wanted %s, got %s',
                [Law.Id, M.Kind, M.Expected,
                 string.Join(',', Codes.ToStringArray)]));
            end;
          end;
        finally
          Codes.Free;
          Res.Free;
          Src := nil;
        end;
      end;
    end;

    { --- the matrix --- }
    Header := Format('  %-24s', ['law']);
    for J := 0 to High(Kinds) do
      Header := Header + Format('%-6s', [Copy(Kinds[J], 1, 5)]);
    Header := Header + ' correct';
    Writeln(Header);
    Writeln('  ', StringOfChar('-', Length(Header) - 2));

    for I := 0 to Rows - 1 do
    begin
      Row := Format('  %-24s', [Copy(LawIds[I], 1, 23)]);
      for J := 0 to High(Kinds) do
      begin
        if Cells[I][J] = cNA then Inc(NA);
        Row := Row + Format('%-6s', [CellText(Cells[I][J])]);
      end;
      Writeln(Row);
    end;
    Writeln;

    if Notes.Count > 0 then
    begin
      Writeln('  Gaps');
      Writeln('  ----');
      for I := 0 to Notes.Count - 1 do Writeln(Notes[I]);
      Writeln;
    end;

    Writeln(Format('  %d law(s), %d mutation(s) applicable, %d not expressible',
                   [Rows, Total, NA]));
    Writeln(Format('  correct forms left clean : %d/%d', [CleanOk, CleanTotal]));
    Writeln(Format('  detected at all          : %d/%d', [Detected, Total]));
    Writeln(Format('  classified exactly right : %d/%d', [Exact, Total]));
    Writeln;

    { A miss is a hole in the engine and fails the run. A partial is not: the
      user is still told the reaction is wrong, only under a different name,
      and holding the build hostage to classification precision would make
      the harness something people switch off. }
    for I := 0 to Rows - 1 do
      for J := 0 to High(Kinds) do
        if Cells[I][J] = cMissed then
          Fail(Format('%s / %s', [LawIds[I], Kinds[J]]),
               'the mutation was not detected at all');
  finally
    Notes.Free;
    Reg.Free;
  end;
end;

{ ------------------------------------------------------------------ }

begin
  try
    if (ParamCount >= 1) and SameText(ParamStr(1), '-list') then
      ListCases
    else if (ParamCount >= 2) and SameText(ParamStr(1), '-show') then
      ShowCase(ParamStr(2))
    else if (ParamCount >= 2) and SameText(ParamStr(1), '-expr') then
      ShowExpression(ParamStr(2))
    else if (ParamCount >= 1) and SameText(ParamStr(1), '-canon') then
      RunCanonPairs
    else if (ParamCount >= 1) and SameText(ParamStr(1), '-laws') then
      ListLaws
    else if (ParamCount >= 1) and SameText(ParamStr(1), '-registry') then
      RunRegistry
    else if (ParamCount >= 2) and SameText(ParamStr(1), '-check') then
      ShowCheck(ParamStr(2))
    else if (ParamCount >= 1) and SameText(ParamStr(1), '-stress') or SameText(ParamStr(1), '-coverage') then
      RunCoverage
    else if (ParamCount >= 1) and SameText(ParamStr(1), '-bind') then
      if ParamCount >= 2 then ShowBinding(ParamStr(2)) else RunBinding
    else
    begin
      Writeln('Rate law checker');
      Writeln('================');
      Writeln;
      RunCanonPairs;
      RunRegistry;
      RunBinding;
      RunModelCases;
      Writeln;
      if GFailures = 0 then
        Writeln('All tests passed.')
      else
      begin
        Writeln(Format('%d FAILURE(S).', [GFailures]));
        ExitCode := 1;
      end;
    end;
  except
    on E: Exception do
    begin
      Writeln(ErrOutput, E.ClassName, ': ', E.Message);
      ExitCode := 1;
    end;
  end;
end.
