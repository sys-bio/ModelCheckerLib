unit RateLaw.Dynamic;

{ The dynamic engine, layer one: does the rate law BEHAVE like the law it
  claims to be?

  The static engine asks whether the equation was written correctly. This asks
  a different question, and there are defects only it can see. A rate law can
  be structurally impeccable and still have its half-saturation constant
  somewhere other than half-maximal rate, and no amount of tree comparison
  will notice, because the tree is exactly the right shape.

  Each invariant type is implemented ONCE, generically, over whatever the
  registry declares. Nothing here knows what Michaelis-Menten is: a law says
  'value_at S = Km equals Vm/2' and this evaluates that claim. A law with new
  behavioural claims is a registry entry, exactly as a new structural form is.

  EVERY FAILURE CARRIES A WITNESS -- the actual values at which the property
  broke. A dynamic finding without one cannot be told apart from a bug in the
  checker, and the user cannot reproduce it. The witness is therefore built
  into the reporting path rather than added where convenient. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Types, RateLaw.Ast, RateLaw.Parser, RateLaw.Registry, RateLaw.Eval;

const
  { Relative tolerance for comparing two rates. Loose enough to survive the
    ordinary drift of floating point through a few dozen operations, tight
    enough that a factor-of-two error in a half-saturation constant cannot
    hide under it. }
  DefaultRelTol = 1.0e-6;
  DefaultAbsTol = 1.0e-12;

  { A limit is approached, never reached, so it gets a far looser tolerance.
    Vm*S/(Km+S) at S = 1e8 is still a part in a million short of Vm, and
    calling that a violation would flag every saturating law there is. }
  LimitRelTol = 1.0e-2;

  { Combinations of the variables NOT being swept. Capped so a law with six
    parameters cannot turn one check into millions of evaluations. When the
    cap bites it is reported, never silently applied. }
  MaxContexts = 96;

{ Checks AExpr -- which must be in ROLE vocabulary -- against ALaw's declared
  invariants. Pass '' and -1 for the reaction when checking a law against
  itself. Returns the number of invariants that failed. }
function CheckInvariants(ALaw: TRateLawDef; AExpr: TAstNode;
                         const AReactionId: string; ALine: Integer;
                         ADiags: TRateLawDiagnostics): Integer;

{ Layer 2: evaluate the reaction's rate law and the law's own expression over
  the same grid and see how far apart they actually get.

  This answers a question the structural diff cannot. A diff says the two trees
  differ; it cannot say whether that matters. Two expressions can be
  algebraically identical and structurally different -- the same rate written
  another way round -- and they can be structurally close and numerically poles
  apart outside the regime someone happened to test in.

  Both outcomes are reported, and the second is the more valuable:

    D006  they diverge, with the worst point and how bad it gets there
    D008  they never diverge, so the structural finding above it has no
          numerical consequence at all

  D008 is what lets a report distinguish "you wrote this differently" from
  "you wrote this wrongly", which is otherwise left for the reader to guess. }
function CompareWithCanonical(ALaw: TRateLawDef; AModelExpr: TAstNode;
                              const AReactionId: string; ALine: Integer;
                              ADiags: TRateLawDiagnostics): Integer;

{ Specification 7.3, the half that needed an evaluator: does the law's own
  canonical expression satisfy the law's own declared invariants?

  An entry that fails this produces false positives on every model checked
  afterwards, and the user has no way to tell the tool is wrong rather than
  their model. Returns True when the entry is self-consistent. }
function ValidateLawInvariants(ALaw: TRateLawDef;
                               ADiags: TRateLawDiagnostics): Boolean;

{ Evaluates one reaction's rate law at the initial values the model declares,
  and reports D101 if it has no value there -- a division by zero at t=0 being
  the case that prompted it. Needs no association: it is a statement about the
  model, not about any law. }
procedure CheckAtInitialState(const AModel: IModelSource; AIndex: Integer;
                              ADiags: TRateLawDiagnostics);

implementation

{ ------------------------------------------ the model's own initial state }

{ Everything else in this unit tests the LAW, over a grid it generates itself.
  Nothing in it reads the model's numbers -- which is why setting a species to
  zero in the model changes none of its findings, and why a rate law that
  divides by that species is reported by none of them.

  This is the other question, and the one a modeller is actually asking: does
  this rate law work for THIS model, as written? It is the cheap slice of the
  Layer 3 work deferred in section 11.4 of the specification. No simulation,
  no RoadRunner, no SBML -- the rate law is evaluated once, at the initial
  values the model declares, and reported if it has no value there.

  A rate law that cannot be evaluated at t=0 cannot be integrated from t=0,
  so this is a defect in the model whatever law it does or does not follow.
  It is therefore checked per reaction and needs no association. }
function InitialStateEnv(const AModel: IModelSource;
                         ATree: TAstNode;
                         out AMissing: string): TEvalEnv;
var
  Name: string;
begin
  AMissing := '';
  Result := TEvalEnv.Create;
  for Name in IdentifiersIn(ATree) do
  begin
    if Result.ContainsKey(Name) then Continue;

    { At the initial state time is zero by definition. pi is pi. }
    if SameText(Name, 'time') then
    begin
      Result.Add(Name, 0);
      Continue;
    end;
    if SameText(Name, 'pi') then
    begin
      Result.Add(Name, Pi);
      Continue;
    end;
    if IsBuiltInSymbol(Name) or IsNullSpecies(Name) then
    begin
      Result.Add(Name, 0);
      Continue;
    end;

    if AModel.HasValue(Name) then
    begin
      { HasValue says the model gave one; it does not say it was a NUMBER. A
        species whose initial value is an expression or an initial assignment
        comes back NaN, and evaluating with it produces a failure that says
        far more about the adapter than about the model. Not knowing a
        starting value is not evidence that the rate law breaks at it, so the
        check stands down rather than guessing -- which is what it was doing:
        114 findings over 40 curated models, every one of them a NaN. }
      if IsNan(AModel.ValueOf(Name)) or IsInfinite(AModel.ValueOf(Name)) then
      begin
        AMissing := Name;
        Exit;
      end;
      Result.Add(Name, AModel.ValueOf(Name));
      Continue;
    end;

    { An Antimony species with no initial value starts at zero, which is
      ordinary and is exactly the case worth evaluating. Anything else with
      no value cannot be evaluated at all -- and S014 has already said so, so
      this check stands down rather than reporting the same thing twice. }
    if AModel.KnowsSymbolKinds and (AModel.SymbolKind(Name) = skSpecies) then
      Result.Add(Name, 0)
    else
    begin
      AMissing := Name;
      Exit;
    end;
  end;
end;

procedure CheckAtInitialState(const AModel: IModelSource; AIndex: Integer;
                              ADiags: TRateLawDiagnostics);
var
  Tree: TAstNode;
  Env: TEvalEnv;
  Res: TEvalResult;
  Err, Missing, RxId, Witness, Blame: string;
  Pair: TPair<string, Double>;
  D: TRateLawDiagnostic;
begin
  if Trim(AModel.RateLawText(AIndex)) = '' then Exit;
  if not TryParseRateLaw(AModel.RateLawText(AIndex), Tree, Err) then Exit;
  try
    Env := InitialStateEnv(AModel, Tree, Missing);
    try
      if Missing <> '' then Exit;

      Res := Evaluate(Tree, Env);
      if Res.Ok then Exit;

      { The witness is the initial state itself -- every value that went in,
        so the reader can see which one did it. }
      Witness := '';
      for Pair in Env do
      begin
        if Witness <> '' then Witness := Witness + ', ';
        Witness := Witness + Format('%s=%g', [Pair.Key, Pair.Value]);
      end;

      Blame := Res.Blame;
      if Blame = '' then Blame := EvalStatusName(Res.Status);

      RxId := AModel.ReactionId(AIndex);
      D := Default(TRateLawDiagnostic);
      D.Code       := 'D101';
      D.Severity   := sevError;
      D.ReactionId := RxId;
      D.SourceLine := AModel.SourceLineOf(AIndex);
      { Naming the fault first. "Cannot be worked out" is the whole truth and
        almost no help on a long expression: what a reader needs is which of
        the handful of ways it can fail happened, and where. }
      if Res.Status = evDivideByZero then
        D.Message := 'this reaction divides by zero at the values this model '
                   + 'starts with (' + Blame + '), so it cannot be simulated '
                   + 'from time zero'
      else
        D.Message := 'the rate law cannot be worked out from the values this '
                   + 'model starts with (' + EvalStatusName(Res.Status) + ': '
                   + Blame + '), so it cannot be simulated from time zero';
      D.Found      := AModel.RateLawText(AIndex);
      D.Evidence   := Witness;
      ADiags.Add(D);
    finally
      Env.Free;
    end;
  finally
    Tree.Free;
  end;
end;

type
  TGrid = record
    Name:   string;
    Values: TArray<Double>;
  end;

  TInvContext = record
    Law:        TRateLawDef;
    Expr:       TAstNode;
    ReactionId: string;
    Line:       Integer;
    Diags:      TRateLawDiagnostics;
  end;

{ ------------------------------------------------------------------ helpers }

function IfBlame(const ABlame: string): string;
begin
  if ABlame = '' then Result := '' else Result := ': ' + ABlame;
end;

function CloseEnough(A, B, ARelTol: Double): Boolean;
var
  Scale: Double;
begin
  if IsNan(A) or IsNan(B) then Exit(False);
  Scale := Max(Abs(A), Abs(B));
  if Scale < DefaultAbsTol then Exit(True);
  Result := Abs(A - B) <= ARelTol * Scale + DefaultAbsTol;
end;

function WitnessOf(AEnv: TEvalEnv; const AExtra: string = ''): string;
var
  L: TStringList;
  Pair: TPair<string, Double>;
  I: Integer;
begin
  L := TStringList.Create;
  try
    L.Sorted := True;
    if AEnv <> nil then
      for Pair in AEnv do
        L.Add(Format('%s=%.6g', [Pair.Key, Pair.Value]));
    Result := '';
    for I := 0 to L.Count - 1 do
    begin
      if I > 0 then Result := Result + ', ';
      Result := Result + L[I];
    end;
  finally
    L.Free;
  end;
  if AExtra <> '' then
  begin
    if Result <> '' then Result := Result + ';  ';
    Result := Result + AExtra;
  end;
end;

procedure Report(const C: TInvContext; const ACode: string;
  ASeverity: TSeverity; const AMessage, AWitness: string);
var
  D: TRateLawDiagnostic;
begin
  D := Default(TRateLawDiagnostic);
  D.Code       := ACode;
  D.Severity   := ASeverity;
  D.LawId      := C.Law.Id;
  D.ReactionId := C.ReactionId;
  D.SourceLine := C.Line;
  D.Message    := AMessage;
  D.Evidence   := AWitness;
  C.Diags.Add(D);
end;

{ ------------------------------------------------------------------- grids }

function MakeGrid(const AName: string; ALo, AHi: Double; ACount: Integer;
                  ALog: Boolean): TGrid;
var
  I: Integer;
  T: Double;
begin
  Result.Name := AName;
  if ACount < 1 then ACount := 1;
  SetLength(Result.Values, ACount);
  if ACount = 1 then
  begin
    Result.Values[0] := ALo;
    Exit;
  end;
  if ALog and (ALo > 0) and (AHi > 0) then
    for I := 0 to ACount - 1 do
    begin
      T := I / (ACount - 1);
      Result.Values[I] := Exp(Ln(ALo) + T * (Ln(AHi) - Ln(ALo)));
    end
  else
    for I := 0 to ACount - 1 do
    begin
      T := I / (ACount - 1);
      Result.Values[I] := ALo + T * (AHi - ALo);
    end;
end;

{ What the registry declared for this role, or a default chosen for the kind
  of thing it is. A law that declares no sampling is still checkable;
  requiring one would mean every entry carried boilerplate. }
function GridFor(ALaw: TRateLawDef; const ARole: TRole; AFine: Boolean): TGrid;
var
  I, N: Integer;
  S: TSampling;
  Lo, Hi: Double;
  IsLog: Boolean;
  R: TEvalResult;
begin
  for I := 0 to ALaw.Sampling.Count - 1 do
    if ALaw.Sampling[I].Name = ARole.Name then
    begin
      S := ALaw.Sampling[I];
      R := EvaluateText(S.Lo, nil);
      if R.Ok then Lo := R.Value else Lo := 1e-3;
      R := EvaluateText(S.Hi, nil);
      if R.Ok then Hi := R.Value else Hi := 1e3;
      N := S.N;
      if not AFine then N := Min(N, 4);
      Exit(MakeGrid(ARole.Name, Lo, Hi, N, SameText(S.Scale, 'log')));
    end;

  case ARole.Kind of
    rkSpecies:
      begin
        Lo := 1e-3; Hi := 1e3; IsLog := True;
        if AFine then N := 33 else N := 4;
      end;
    rkCompartment:
      begin
        Lo := 1; Hi := 1; IsLog := False; N := 1;
      end;
  else
    begin
      Lo := 1e-2; Hi := 1e2; IsLog := True;
      if AFine then N := 7 else N := 3;
    end;
  end;
  Result := MakeGrid(ARole.Name, Lo, Hi, N, IsLog);
end;

{ ---------------------------------------------------------------- contexts }

{ The combinations of everything except the swept variable. Owned by the
  caller through a TObjectList. }
function BuildContexts(ALaw: TRateLawDef; const AExclude: TArray<string>;
                       out ATruncated: Boolean): TObjectList<TEvalEnv>;
var
  Grids: TArray<TGrid>;
  I, J, Count, Size: Integer;
  R: TRole;
  Skip: Boolean;
  Env: TEvalEnv;
  Name: string;
  Total, Idx, Rem: Int64;
begin
  ATruncated := False;
  Grids := nil;
  for I := 0 to ALaw.RoleCount - 1 do
  begin
    R := ALaw.Roles[I];
    Skip := False;
    for Name in AExclude do
      if Name = R.Name then begin Skip := True; Break; end;
    if Skip then Continue;
    Grids := Grids + [GridFor(ALaw, R, False)];
  end;

  Result := TObjectList<TEvalEnv>.Create(True);

  { How many combinations there are in all. Int64 and clamped, because six
    roles with a handful of values each already runs to thousands and a
    careless law could run to far more. }
  Total := 1;
  for I := 0 to High(Grids) do
  begin
    Size := Length(Grids[I].Values);
    if Size < 1 then Size := 1;
    Total := Total * Size;
    if Total > 1000000 then
    begin
      Total := 1000000;
      Break;
    end;
  end;
  if Total < 1 then Total := 1;

  if Total <= MaxContexts then Count := Total
  else
  begin
    Count := MaxContexts;
    ATruncated := True;
  end;

  { Each context is decoded from an index into the product space, so EVERY
    variable gets a value in EVERY context.

    The previous version grew the product one variable at a time and stopped
    when it reached the cap -- which left the variables it had not reached yet
    absent altogether. Every invariant on a law with six or more roles then
    failed at load with "undefined symbol", and the law was rejected. It was
    invisible on small laws because the cap was never reached. Found by
    authoring the inhibition and convenience-kinetics entries, which is what
    the registry-expansion exercise is for.

    Indices are strided rather than taken from the front, so a truncated
    sample still spans the whole space instead of pinning every variable but
    the last to its smallest value. }
  for I := 0 to Count - 1 do
  begin
    if Count = 1 then Idx := 0
    else Idx := Round((I * (Total - 1)) / (Count - 1));

    Env := TEvalEnv.Create;
    Rem := Idx;
    for J := High(Grids) downto 0 do
    begin
      Size := Length(Grids[J].Values);
      if Size < 1 then Continue;
      Env.AddOrSetValue(Grids[J].Name, Grids[J].Values[Rem mod Size]);
      Rem := Rem div Size;
    end;
    Result.Add(Env);
  end;
end;

{ Evaluates the expression with AVar set to AValue on top of AEnv, restoring
  AEnv afterwards so a caller can keep reusing it. }
function EvalAt(const C: TInvContext; AEnv: TEvalEnv;
                const AVar: string; AValue: Double): TEvalResult;
var
  Saved: Double;
  HadIt: Boolean;
begin
  HadIt := False;
  if AVar <> '' then
  begin
    HadIt := AEnv.TryGetValue(AVar, Saved);
    AEnv.AddOrSetValue(AVar, AValue);
  end;
  try
    Result := Evaluate(C.Expr, AEnv);
  finally
    if AVar <> '' then
      if HadIt then AEnv.AddOrSetValue(AVar, Saved)
      else AEnv.Remove(AVar);
  end;
end;

{ The species roles, which is what 'all the inputs' means for the invariants
  that do not name their variables. }
function SpeciesRoleNames(ALaw: TRateLawDef): TArray<string>;
var
  I: Integer;
begin
  Result := nil;
  for I := 0 to ALaw.RoleCount - 1 do
    if ALaw.Roles[I].Kind = rkSpecies then
      Result := Result + [ALaw.Roles[I].Name];
end;

function FirstVarOf(const AInv: TInvariant; ALaw: TRateLawDef): string;
var
  Names: TArray<string>;
begin
  if Length(AInv.Vars) > 0 then Exit(AInv.Vars[0]);
  Names := SpeciesRoleNames(ALaw);
  if Length(Names) > 0 then Exit(Names[0]);
  Result := '';
end;

{ --------------------------------------------------------- the invariants }

{ zero_at / value_at: the rate takes a stated value at a stated point.

  This is where a structurally perfect law gets caught. Nothing about the
  shape of Vm*S/(K+S) says whether K is the half-saturation point; only
  evaluating it does. }
function CheckValueAt(const C: TInvContext; const AInv: TInvariant;
                      AExpectZero: Boolean): Boolean;
var
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  Fixed: TArray<string>;
  I, J: Integer;
  Env: TEvalEnv;
  R, Want: TEvalResult;
  PointDesc: string;
  Target: Double;
begin
  Result := True;
  Fixed := nil;
  for I := 0 to High(AInv.Point) do
    Fixed := Fixed + [AInv.Point[I].Name];

  Ctxs := BuildContexts(C.Law, Fixed, Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      Env := Ctxs[I];

      { The point's coordinates may be expressions in the other roles --
        'value_at S = Km' is the whole reason value_at exists -- so they are
        evaluated in this context, not read as numbers. }
      PointDesc := '';
      for J := 0 to High(AInv.Point) do
      begin
        Want := EvaluateText(AInv.Point[J].Expr, Env);
        if not Want.Ok then Continue;
        Env.AddOrSetValue(AInv.Point[J].Name, Want.Value);
        if PointDesc <> '' then PointDesc := PointDesc + ', ';
        PointDesc := PointDesc + Format('%s=%.6g',
                                        [AInv.Point[J].Name, Want.Value]);
      end;

      R := Evaluate(C.Expr, Env);
      if not R.Ok then
      begin
        Report(C, 'D001', sevError,
          Format('the rate law has no value at the point this law calls for '
               + '(%s%s)', [EvalStatusName(R.Status), IfBlame(R.Blame)]),
          WitnessOf(Env));
        Exit(False);
      end;

      if AExpectZero then
        Target := 0
      else
      begin
        Want := EvaluateText(AInv.EqualsExpr, Env);
        if not Want.Ok then Continue;   { cannot be evaluated here; not a finding }
        Target := Want.Value;
      end;

      if not CloseEnough(R.Value, Target, DefaultRelTol) then
      begin
        Report(C, 'D005', sevError,
          Format('this law requires the rate to be %s at %s, but it is %.6g',
            [Format('%.6g', [Target]), PointDesc, R.Value]),
          WitnessOf(Env, Format('rate=%.6g, expected %.6g',
                                [R.Value, Target])));
        Exit(False);
      end;
    end;
  finally
    Ctxs.Free;
  end;
end;

{ zero_at_any_zero: setting any one of the listed variables to zero must
  bring the rate to zero. What makes mass action mass action. }
function CheckZeroAtAnyZero(const C: TInvContext;
                            const AInv: TInvariant): Boolean;
var
  Vars: TArray<string>;
  V: string;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I: Integer;
  R: TEvalResult;
begin
  Result := True;
  Vars := AInv.Vars;
  if Length(Vars) = 0 then Vars := SpeciesRoleNames(C.Law);

  for V in Vars do
  begin
    Ctxs := BuildContexts(C.Law, [V], Trunc);
    try
      for I := 0 to Ctxs.Count - 1 do
      begin
        R := EvalAt(C, Ctxs[I], V, 0);
        if not R.Ok then Continue;   { zero may be outside the domain }
        if not CloseEnough(R.Value, 0, DefaultRelTol) then
        begin
          Report(C, 'D005', sevError,
            Format('this law requires the rate to vanish when %s is zero, '
                 + 'but it is %.6g', [V, R.Value]),
            WitnessOf(Ctxs[I], Format('%s=0, rate=%.6g', [V, R.Value])));
          Exit(False);
        end;
      end;
    finally
      Ctxs.Free;
    end;
  end;
end;

{ nonnegative: a rate that goes negative is running backwards. }
function CheckNonNegative(const C: TInvContext;
                          const AInv: TInvariant): Boolean;
var
  Focus: string;
  Grid: TGrid;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I, J, K: Integer;
  R: TEvalResult;
  Role: TRole;
begin
  Result := True;
  Focus := FirstVarOf(AInv, C.Law);
  if Focus = '' then Exit;
  if not C.Law.FindRole(Focus, Role) then Exit;

  Grid := GridFor(C.Law, Role, True);
  Ctxs := BuildContexts(C.Law, [Focus], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
      for J := 0 to High(Grid.Values) do
      begin
        R := EvalAt(C, Ctxs[I], Focus, Grid.Values[J]);
        if not R.Ok then
        begin
          Report(C, 'D001', sevError,
            Format('the rate law has no value inside the domain this law '
                 + 'declares (%s%s)',
                 [EvalStatusName(R.Status), IfBlame(R.Blame)]),
            WitnessOf(Ctxs[I], Format('%s=%.6g', [Focus, Grid.Values[J]])));
          Exit(False);
        end;
        if R.Value < -DefaultAbsTol then
        begin
          Report(C, 'D002', sevError,
            Format('this law declares the rate non-negative, but it is %.6g '
                 + 'here', [R.Value]),
            WitnessOf(Ctxs[I], Format('%s=%.6g, rate=%.6g',
                                      [Focus, Grid.Values[J], R.Value])));
          Exit(False);
        end;
        { A single unusable K is not fatal on its own. }
        K := 0;
        if K <> 0 then Break;
      end;
  finally
    Ctxs.Free;
  end;
end;

{ monotonic: the rate moves consistently in one direction as the variable
  increases. }
function CheckMonotonic(const C: TInvContext;
                        const AInv: TInvariant): Boolean;
var
  Vars: TArray<string>;
  Focus: string;
  Grid: TGrid;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I, J: Integer;
  Prev, R: TEvalResult;
  Role: TRole;
  WantUp: Boolean;
  Delta: Double;
begin
  Result := True;
  Vars := AInv.Vars;
  if Length(Vars) = 0 then Vars := SpeciesRoleNames(C.Law);
  WantUp := not SameText(AInv.Direction, 'decreasing');

  for Focus in Vars do
  begin
    if not C.Law.FindRole(Focus, Role) then Continue;
    Grid := GridFor(C.Law, Role, True);
    Ctxs := BuildContexts(C.Law, [Focus], Trunc);
    try
      for I := 0 to Ctxs.Count - 1 do
      begin
        Prev := EvalAt(C, Ctxs[I], Focus, Grid.Values[0]);
        for J := 1 to High(Grid.Values) do
        begin
          R := EvalAt(C, Ctxs[I], Focus, Grid.Values[J]);
          if not (Prev.Ok and R.Ok) then
          begin
            Prev := R;
            Continue;
          end;
          Delta := R.Value - Prev.Value;

          { A flat stretch is not a violation -- a saturating law is flat at
            the top, and floating point makes exact equality unreliable, so
            only a move in the wrong direction that is large relative to the
            values involved counts. }
          if Abs(Delta) > DefaultRelTol * Max(Abs(R.Value), Abs(Prev.Value)) then
            if (WantUp and (Delta < 0)) or ((not WantUp) and (Delta > 0)) then
            begin
              Report(C, 'D003', sevError,
                Format('this law declares the rate %s in %s, but it moves the '
                     + 'other way between %.6g and %.6g',
                  [AInv.Direction, Focus, Grid.Values[J - 1], Grid.Values[J]]),
                WitnessOf(Ctxs[I],
                  Format('%s: %.6g -> %.6g gives rate %.6g -> %.6g',
                    [Focus, Grid.Values[J - 1], Grid.Values[J],
                     Prev.Value, R.Value])));
              Exit(False);
            end;
          Prev := R;
        end;
      end;
    finally
      Ctxs.Free;
    end;
  end;
end;

{ limit: the rate approaches a stated expression as a variable runs to zero
  or to infinity. }
function CheckLimit(const C: TInvContext; const AInv: TInvariant): Boolean;
var
  Focus: string;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc, Usable: Boolean;
  I, J: Integer;
  R, Want: TEvalResult;
  ToInf: Boolean;
  Probes, Errors, Values: array [0 .. 2] of Double;
begin
  Result := True;
  Focus := FirstVarOf(AInv, C.Law);
  if Focus = '' then Exit;
  ToInf := SameText(AInv.Toward, 'inf');

  Ctxs := BuildContexts(C.Law, [Focus], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      Want := EvaluateText(AInv.EqualsExpr, Ctxs[I]);
      if not Want.Ok then Continue;

      { A limit is APPROACHED, so one probe far out is not enough to judge
        it. Reversible Michaelis-Menten really does tend to Vf as S grows, but
        where the reverse term is large the approach is slow enough that even
        S = 1e10 is still ten per cent short -- and rejecting the law for that
        would be rejecting it for being correct.

        So: accept if the far probe is close, OR if the error is genuinely
        collapsing as the variable grows. A law tending to the declared value
        has errors that shrink by a large factor each decade; one tending
        somewhere else has errors that flatten out. }
      Probes[0] := 1e4; Probes[1] := 1e7; Probes[2] := 1e10;
      if not ToInf then
      begin
        Probes[0] := 1e-4; Probes[1] := 1e-7; Probes[2] := 1e-10;
      end;

      Usable := True;
      for J := 0 to 2 do
      begin
        R := EvalAt(C, Ctxs[I], Focus, Probes[J]);
        if not R.Ok then begin Usable := False; Break; end;
        Errors[J] := Abs(R.Value - Want.Value);
        Values[J] := R.Value;
      end;
      if not Usable then Continue;

      if CloseEnough(Values[2], Want.Value, LimitRelTol) then Continue;

      { Converging: each step cuts the error to a fraction of the last. }
      if (Errors[2] < Errors[1] * 0.5) and (Errors[1] < Errors[0] * 0.5) then
        Continue;

      Report(C, 'D004', sevError,
        Format('this law requires the rate to approach %.6g as %s runs to '
             + '%s, but at %s = %.3g it is %.6g and is not closing on it',
          [Want.Value, Focus, AInv.Toward, Focus, Probes[2], Values[2]]),
        WitnessOf(Ctxs[I], Format('%s=%.3g gives %.6g, expected ~%.6g',
                                  [Focus, Probes[2], Values[2], Want.Value])));
      Exit(False);
    end;
  finally
    Ctxs.Free;
  end;
end;

{ bounded_above: the rate never exceeds a stated expression. }
function CheckBoundedAbove(const C: TInvContext;
                           const AInv: TInvariant): Boolean;
var
  Focus: string;
  Grid: TGrid;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I, J: Integer;
  R, Want: TEvalResult;
  Role: TRole;
begin
  Result := True;
  Focus := FirstVarOf(AInv, C.Law);
  if (Focus = '') or not C.Law.FindRole(Focus, Role) then Exit;

  Grid := GridFor(C.Law, Role, True);
  Ctxs := BuildContexts(C.Law, [Focus], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      Want := EvaluateText(AInv.EqualsExpr, Ctxs[I]);
      if not Want.Ok then Continue;
      for J := 0 to High(Grid.Values) do
      begin
        R := EvalAt(C, Ctxs[I], Focus, Grid.Values[J]);
        if not R.Ok then Continue;
        if R.Value > Want.Value * (1 + LimitRelTol) + DefaultAbsTol then
        begin
          Report(C, 'D004', sevError,
            Format('this law bounds the rate above by %.6g, but it reaches '
                 + '%.6g', [Want.Value, R.Value]),
            WitnessOf(Ctxs[I], Format('%s=%.6g, rate=%.6g',
                                      [Focus, Grid.Values[J], R.Value])));
          Exit(False);
        end;
      end;
    end;
  finally
    Ctxs.Free;
  end;
end;

{ sigmoidal: the curve has exactly one inflection over the domain. }
function CheckSigmoidal(const C: TInvContext;
                        const AInv: TInvariant): Boolean;
var
  Focus: string;
  Grid: TGrid;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I, J, Flips: Integer;
  Vals: TArray<Double>;
  R: TEvalResult;
  Role: TRole;
  D2, PrevD2, Scale: Double;
  Known, Holds: Boolean;
  Usable: Boolean;
begin
  Result := True;
  Focus := FirstVarOf(AInv, C.Law);
  if (Focus = '') or not C.Law.FindRole(Focus, Role) then Exit;

  Grid := GridFor(C.Law, Role, True);
  if Length(Grid.Values) < 5 then Exit;

  Ctxs := BuildContexts(C.Law, [Focus], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      { A 'when' clause restricts the claim -- Hill is only sigmoidal for
        n > 1 -- and a context where it does not hold is simply not a case
        this invariant speaks about. }
      if AInv.WhenExpr <> '' then
      begin
        Holds := EvaluateCondition(AInv.WhenExpr, Ctxs[I], Known);
        if not Known then Continue;
        if not Holds then Continue;
      end;

      SetLength(Vals, Length(Grid.Values));
      Usable := True;
      for J := 0 to High(Grid.Values) do
      begin
        R := EvalAt(C, Ctxs[I], Focus, Grid.Values[J]);
        if not R.Ok then begin Usable := False; Break; end;
        Vals[J] := R.Value;
      end;
      if not Usable then Continue;

      Scale := 0;
      for J := 0 to High(Vals) do Scale := Max(Scale, Abs(Vals[J]));
      if Scale <= DefaultAbsTol then Continue;

      Flips := 0;
      PrevD2 := 0;
      for J := 1 to High(Vals) - 1 do
      begin
        D2 := Vals[J + 1] - 2 * Vals[J] + Vals[J - 1];
        if Abs(D2) < 1e-4 * Scale then Continue;   { flat: no opinion }
        if (PrevD2 <> 0) and (Sign(D2) <> Sign(PrevD2)) then Inc(Flips);
        PrevD2 := D2;
      end;

      if Flips <> 1 then
      begin
        Report(C, 'D007', sevError,
          Format('this law declares the curve sigmoidal in %s, but its '
               + 'curvature changes sign %d times over the sampled domain '
               + 'rather than once', [Focus, Flips]),
          WitnessOf(Ctxs[I], Format('%s swept from %.3g to %.3g',
            [Focus, Grid.Values[0], Grid.Values[High(Grid.Values)]])));
        Exit(False);
      end;
    end;
  finally
    Ctxs.Free;
  end;
end;

{ symmetric: swapping two variables leaves the rate unchanged. }
function CheckSymmetric(const C: TInvContext;
                        const AInv: TInvariant): Boolean;
var
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I: Integer;
  A, B: string;
  VA, VB: Double;
  R1, R2: TEvalResult;
begin
  Result := True;
  if Length(AInv.Vars) < 2 then Exit;
  A := AInv.Vars[0];
  B := AInv.Vars[1];

  Ctxs := BuildContexts(C.Law, [], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      if not Ctxs[I].TryGetValue(A, VA) then Continue;
      if not Ctxs[I].TryGetValue(B, VB) then Continue;
      if SameValue(VA, VB) then Continue;

      R1 := Evaluate(C.Expr, Ctxs[I]);
      Ctxs[I].AddOrSetValue(A, VB);
      Ctxs[I].AddOrSetValue(B, VA);
      R2 := Evaluate(C.Expr, Ctxs[I]);
      Ctxs[I].AddOrSetValue(A, VA);
      Ctxs[I].AddOrSetValue(B, VB);

      if not (R1.Ok and R2.Ok) then Continue;
      if not CloseEnough(R1.Value, R2.Value, DefaultRelTol) then
      begin
        Report(C, 'D007', sevError,
          Format('this law declares the rate symmetric in %s and %s, but '
               + 'exchanging them changes it from %.6g to %.6g',
            [A, B, R1.Value, R2.Value]),
          WitnessOf(Ctxs[I], Format('%s<->%s gives %.6g vs %.6g',
                                    [A, B, R1.Value, R2.Value])));
        Exit(False);
      end;
    end;
  finally
    Ctxs.Free;
  end;
end;

{ homogeneous: scaling the inputs by a factor scales the rate by that factor
  raised to the declared degree. }
function CheckHomogeneous(const C: TInvContext;
                          const AInv: TInvariant): Boolean;
const
  Lambda = 2.0;
var
  Vars: TArray<string>;
  V: string;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I: Integer;
  R1, R2, Deg: TEvalResult;
  Orig: TDictionary<string, Double>;
  Val, Expected: Double;
begin
  Result := True;
  Vars := AInv.Vars;
  if Length(Vars) = 0 then Vars := SpeciesRoleNames(C.Law);
  if Length(Vars) = 0 then Exit;

  Ctxs := BuildContexts(C.Law, [], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
    begin
      Deg := EvaluateText(AInv.Degree, Ctxs[I]);
      if not Deg.Ok then Continue;   { a degree we cannot evaluate is not a finding }

      R1 := Evaluate(C.Expr, Ctxs[I]);
      if not R1.Ok then Continue;

      Orig := TDictionary<string, Double>.Create;
      try
        for V in Vars do
          if Ctxs[I].TryGetValue(V, Val) then
          begin
            Orig.Add(V, Val);
            Ctxs[I].AddOrSetValue(V, Val * Lambda);
          end;
        R2 := Evaluate(C.Expr, Ctxs[I]);
        for V in Orig.Keys do
          Ctxs[I].AddOrSetValue(V, Orig[V]);
      finally
        Orig.Free;
      end;

      if not R2.Ok then Continue;
      Expected := R1.Value * Power(Lambda, Deg.Value);
      if not CloseEnough(R2.Value, Expected, DefaultRelTol) then
      begin
        Report(C, 'D007', sevError,
          Format('this law declares degree %.6g homogeneity, so doubling the '
               + 'inputs should give %.6g, but it gives %.6g',
            [Deg.Value, Expected, R2.Value]),
          WitnessOf(Ctxs[I], Format('rate %.6g -> %.6g, expected %.6g',
                                    [R1.Value, R2.Value, Expected])));
        Exit(False);
      end;
    end;
  finally
    Ctxs.Free;
  end;
end;

{ ------------------------------------------------- differential comparison }

function CompareWithCanonical(ALaw: TRateLawDef; AModelExpr: TAstNode;
  const AReactionId: string; ALine: Integer;
  ADiags: TRateLawDiagnostics): Integer;
var
  Focus: string;
  Role: TRole;
  Grid: TGrid;
  Ctxs: TObjectList<TEvalEnv>;
  Trunc: Boolean;
  I, J, Compared: Integer;
  Mine, Theirs: TEvalResult;
  Dev, Worst, Scale: Double;
  WorstAt: string;
  D: TRateLawDiagnostic;
begin
  Result := 0;
  if (ALaw = nil) or (AModelExpr = nil) or (ALaw.Expr = nil) then Exit;
  if ADiags = nil then Exit;

  { Identical trees cannot diverge, and saying so would be noise. }
  if Signature(AModelExpr) = Signature(ALaw.Expr) then Exit;

  Focus := '';
  for I := 0 to ALaw.RoleCount - 1 do
    if ALaw.Roles[I].Kind = rkSpecies then
    begin
      Focus := ALaw.Roles[I].Name;
      Break;
    end;
  if (Focus = '') or not ALaw.FindRole(Focus, Role) then Exit;

  Grid     := GridFor(ALaw, Role, True);
  Worst    := 0;
  WorstAt  := '';
  Compared := 0;

  Ctxs := BuildContexts(ALaw, [Focus], Trunc);
  try
    for I := 0 to Ctxs.Count - 1 do
      for J := 0 to High(Grid.Values) do
      begin
        Ctxs[I].AddOrSetValue(Focus, Grid.Values[J]);
        Mine   := Evaluate(AModelExpr, Ctxs[I]);
        Theirs := Evaluate(ALaw.Expr,  Ctxs[I]);

        { A point where either has no value says nothing about how far apart
          they are; the invariant checks report those separately. }
        if not (Mine.Ok and Theirs.Ok) then Continue;
        Inc(Compared);

        Scale := Max(Abs(Mine.Value), Abs(Theirs.Value));
        if Scale < DefaultAbsTol then Continue;
        Dev := Abs(Mine.Value - Theirs.Value) / Scale;

        if Dev > Worst then
        begin
          Worst   := Dev;
          WorstAt := WitnessOf(Ctxs[I],
            Format('rate %.6g against %.6g, a %.1f%% difference',
                   [Mine.Value, Theirs.Value, Dev * 100]));
        end;
      end;
  finally
    Ctxs.Free;
  end;

  if Compared = 0 then Exit;

  D := Default(TRateLawDiagnostic);
  D.LawId      := ALaw.Id;
  D.ReactionId := AReactionId;
  D.SourceLine := ALine;

  if Worst <= DefaultRelTol then
  begin
    { Written differently, computed identically. Worth saying plainly: without
      it the reader has no way to tell a difference of form from a real error,
      and the structural finding sitting above this one looks damning. }
    D.Code     := 'D008';
    D.Severity := sevInfo;
    D.Message  := 'this is written differently from the law but computes the '
                + 'same rate everywhere it was sampled, so the difference in '
                + 'form has no effect on the model';
    D.Evidence := Format('%d points compared, largest difference %.2g%%',
                         [Compared, Worst * 100]);
    ADiags.Add(D);
    Exit;
  end;

  D.Code     := 'D006';
  D.Severity := sevWarn;
  D.Message  := Format('this differs from the law by up to %.1f%% over the '
                     + 'sampled range', [Worst * 100]);
  D.Expected := ALaw.Expression;
  D.Evidence := WorstAt;
  ADiags.Add(D);
  Result := 1;
end;

{ ------------------------------------------------------------- the dispatch }

function CheckInvariants(ALaw: TRateLawDef; AExpr: TAstNode;
  const AReactionId: string; ALine: Integer;
  ADiags: TRateLawDiagnostics): Integer;
var
  C: TInvContext;
  Inv: TInvariant;
  Ok: Boolean;
begin
  Result := 0;
  if (ALaw = nil) or (AExpr = nil) or (ADiags = nil) then Exit;
  if ALaw.Invariants.Count = 0 then Exit;

  C.Law        := ALaw;
  C.Expr       := AExpr;
  C.ReactionId := AReactionId;
  C.Line       := ALine;
  C.Diags      := ADiags;

  for Inv in ALaw.Invariants do
  begin
    case Inv.Kind of
      ivZeroAt:        Ok := CheckValueAt(C, Inv, True);
      ivValueAt:       Ok := CheckValueAt(C, Inv, False);
      ivZeroAtAnyZero: Ok := CheckZeroAtAnyZero(C, Inv);
      ivNonNegative:   Ok := CheckNonNegative(C, Inv);
      ivMonotonic:     Ok := CheckMonotonic(C, Inv);
      ivLimit:         Ok := CheckLimit(C, Inv);
      ivBoundedAbove:  Ok := CheckBoundedAbove(C, Inv);
      ivSigmoidal:     Ok := CheckSigmoidal(C, Inv);
      ivSymmetric:     Ok := CheckSymmetric(C, Inv);
      ivHomogeneous:   Ok := CheckHomogeneous(C, Inv);
    else
      Ok := True;   { unknown types are rejected at load, not here }
    end;
    if not Ok then Inc(Result);
  end;
end;

procedure ValidatorHook(ALaw: TRateLawDef; ADiags: TRateLawDiagnostics);
begin
  ValidateLawInvariants(ALaw, ADiags);
end;

function ValidateLawInvariants(ALaw: TRateLawDef;
  ADiags: TRateLawDiagnostics): Boolean;
var
  Probe: TRateLawDiagnostics;
  D: TRateLawDiagnostic;
  Failures: Integer;
begin
  Result := True;
  if (ALaw = nil) or (ALaw.Expr = nil) or (ALaw.Invariants.Count = 0) then Exit;

  { A GENERATIVE law has no expression to evaluate. 'k * prod(Si^ai)' is a
    shape: prod is not a function this or any evaluator implements, and ai is
    an index variable that only acquires a value once the family is
    instantiated for a particular reaction. Probing it numerically finds an
    undefined symbol every time and would mark the entry invalid -- which is
    what happened, and it silently disabled mass action for every model.

    Its invariants are still checked, on the instantiated form, at the point
    where there is a reaction to instantiate for. }
  if ALaw.Generative then Exit;

  { Run into a scratch list so the law's own failures can be re-reported as
    REGISTRY defects. A law that fails its own invariants is not a finding
    about any model -- reporting it with a D-code against a reaction would
    blame the modeller for the registry's mistake. }
  Probe := TRateLawDiagnostics.Create;
  try
    Failures := CheckInvariants(ALaw, ALaw.Expr, '', -1, Probe);
    Result := Failures = 0;
    if Result then Exit;

    for D in Probe do
    begin
      var E := Default(TRateLawDiagnostic);
      E.Code       := 'R015';
      E.Severity   := sevError;
      E.LawId      := ALaw.Id;
      E.SourceLine := -1;
      E.Message    := 'this law does not satisfy its own declared invariant: '
                    + D.Message;
      E.Evidence   := D.Evidence;
      if ADiags <> nil then ADiags.Add(E);
      ALaw.Problems := ALaw.Problems
        + ['R015 ' + E.Message];
    end;
    ALaw.Valid := False;
  finally
    Probe.Free;
  end;
end;

initialization
  SetInvariantValidator(ValidatorHook);

finalization
  SetInvariantValidator(nil);

end.
