unit RateLaw.Eval;

{ Numeric evaluation of an expression tree.

  Ours, deliberately, rather than RoadRunner's. Probing one invariant means
  sampling a rate law over a grid -- 64 substrate values by 6 by 6 for
  Michaelis-Menten is 2304 evaluations for ONE reaction against ONE law.
  Driving that through setValue/getReactionRates would mutate the user's
  loaded engine thousands of times per check and leave the session in a state
  they never asked for. It would also make the dynamic engine unavailable on a
  model that does not simulate, which is exactly the model a checker is most
  needed for.

  Evaluation is total: it never raises. Every way an expression can fail to
  have a value -- an unknown symbol, a division by zero, a negative base under
  a fractional power, an overflow -- comes back as a status, because those
  failures are findings rather than accidents. A dynamic check whose whole
  purpose is to discover that a rate law blows up cannot itself blow up. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Ast, RateLaw.Parser;

type
  TEvalStatus = (
    evOk,
    evUndefined,   // a symbol with no value in the environment
    evDivideByZero,// a denominator that comes out zero
    evDomain,      // log of a negative, sqrt of a negative, and the like
    evOverflow,    // the result is not finite
    evUnsupported  // a function this evaluator does not implement
  );

  TEvalEnv = TDictionary<string, Double>;

  TEvalResult = record
    Status: TEvalStatus;
    Value:  Double;
    { The symbol or function that could not be handled, for the witness. }
    Blame:  string;
    function Ok: Boolean;
  end;

{ Evaluates ANode under AEnv. Never raises. }
function Evaluate(ANode: TAstNode; AEnv: TEvalEnv): TEvalResult;

{ Parses and evaluates. For the short expressions that appear inside an
  invariant -- 'Vm/2', 'Vm', 'sum(ai)'. }
function EvaluateText(const AText: string; AEnv: TEvalEnv): TEvalResult;

{ A comparison, for an invariant's 'when' clause: 'n > 1'.

  The expression grammar has no comparison operators, and giving it some would
  mean rate laws could contain them, which they cannot. So the condition is
  split at the operator and each side evaluated as an ordinary expression.
  Returns False, with AKnown False, when the condition cannot be evaluated --
  which the caller must not read as "the condition did not hold". }
function EvaluateCondition(const AText: string; AEnv: TEvalEnv;
                           out AKnown: Boolean): Boolean;

function EvalStatusName(AStatus: TEvalStatus): string;

implementation

function TEvalResult.Ok: Boolean;
begin
  Result := Status = evOk;
end;

function EvalStatusName(AStatus: TEvalStatus): string;
begin
  case AStatus of
    evOk:          Result := 'ok';
    evUndefined:   Result := 'undefined symbol';
    evDivideByZero: Result := 'division by zero';
    evDomain:      Result := 'outside the domain';
    evOverflow:    Result := 'not finite';
  else             Result := 'unsupported function';
  end;
end;

function Res(AStatus: TEvalStatus; AValue: Double;
             const ABlame: string = ''): TEvalResult;
begin
  Result.Status := AStatus;
  Result.Value  := AValue;
  Result.Blame  := ABlame;
end;

{ A finite check applied after every operation. An expression that overflows
  to infinity mid-way and back to a finite number later would otherwise pass
  silently, and 'the rate is infinite somewhere in its domain' is a finding. }
function Finite(AValue: Double; const ABlame: string): TEvalResult;
begin
  if IsNan(AValue) then Exit(Res(evDomain, AValue, ABlame));
  if IsInfinite(AValue) then Exit(Res(evOverflow, AValue, ABlame));
  Result := Res(evOk, AValue);
end;

function EvalFunction(const AName: string; const AArgs: TArray<Double>;
                      out AValue: Double): TEvalStatus;
var
  N: Integer;
begin
  N := Length(AArgs);
  AValue := NaN;

  if SameText(AName, 'exp') and (N = 1) then
  begin
    { Guarded: exp(1000) is an overflow, and raising here would abort a probe
      whose whole purpose is to find out that the law overflows. }
    if AArgs[0] > 700 then Exit(evOverflow);
    AValue := Exp(AArgs[0]);
  end
  else if (SameText(AName, 'ln') or SameText(AName, 'log')) and (N = 1) then
  begin
    if AArgs[0] <= 0 then Exit(evDomain);
    AValue := Ln(AArgs[0]);
  end
  else if SameText(AName, 'log10') and (N = 1) then
  begin
    if AArgs[0] <= 0 then Exit(evDomain);
    AValue := Log10(AArgs[0]);
  end
  else if SameText(AName, 'log') and (N = 2) then
  begin
    if (AArgs[0] <= 0) or (AArgs[1] <= 0) or SameValue(AArgs[0], 1) then
      Exit(evDomain);
    AValue := LogN(AArgs[0], AArgs[1]);
  end
  else if SameText(AName, 'sqrt') and (N = 1) then
  begin
    if AArgs[0] < 0 then Exit(evDomain);
    AValue := Sqrt(AArgs[0]);
  end
  else if SameText(AName, 'abs') and (N = 1) then AValue := Abs(AArgs[0])
  else if SameText(AName, 'pow') and (N = 2) then
  begin
    if (AArgs[0] < 0) and (Frac(AArgs[1]) <> 0) then Exit(evDomain);
    if (AArgs[0] = 0) and (AArgs[1] < 0) then Exit(evDomain);
    AValue := Power(AArgs[0], AArgs[1]);
  end
  else if SameText(AName, 'sin') and (N = 1) then AValue := Sin(AArgs[0])
  else if SameText(AName, 'cos') and (N = 1) then AValue := Cos(AArgs[0])
  else if SameText(AName, 'tan') and (N = 1) then AValue := Tan(AArgs[0])
  else if SameText(AName, 'floor') and (N = 1) then AValue := Floor(AArgs[0])
  else if SameText(AName, 'ceil') and (N = 1) then AValue := Ceil(AArgs[0])
  else if SameText(AName, 'min') and (N = 2) then AValue := Min(AArgs[0], AArgs[1])
  else if SameText(AName, 'max') and (N = 2) then AValue := Max(AArgs[0], AArgs[1])
  else
    Exit(evUnsupported);

  Result := evOk;
end;

function Evaluate(ANode: TAstNode; AEnv: TEvalEnv): TEvalResult;
var
  I: Integer;
  L, R: TEvalResult;
  Acc: Double;
  Args: TArray<Double>;
  V: Double;
  St: TEvalStatus;
begin
  if ANode = nil then Exit(Res(evUndefined, NaN, '<nil>'));

  case ANode.Kind of

    nkNumber:
      Exit(Finite(ANode.Value, ''));

    nkIdent:
      begin
        if (AEnv <> nil) and AEnv.TryGetValue(ANode.Name, V) then
          Exit(Finite(V, ANode.Name));
        Exit(Res(evUndefined, NaN, ANode.Name));
      end;

    nkNeg:
      begin
        L := Evaluate(ANode[0], AEnv);
        if not L.Ok then Exit(L);
        Exit(Finite(-L.Value, ''));
      end;

    nkAdd:
      begin
        Acc := 0;
        for I := 0 to ANode.Count - 1 do
        begin
          L := Evaluate(ANode[I], AEnv);
          if not L.Ok then Exit(L);
          Acc := Acc + L.Value;
        end;
        Exit(Finite(Acc, ''));
      end;

    nkSub:
      begin
        L := Evaluate(ANode[0], AEnv);
        if not L.Ok then Exit(L);
        R := Evaluate(ANode[1], AEnv);
        if not R.Ok then Exit(R);
        Exit(Finite(L.Value - R.Value, ''));
      end;

    nkMul:
      begin
        Acc := 1;
        for I := 0 to ANode.Count - 1 do
        begin
          L := Evaluate(ANode[I], AEnv);
          if not L.Ok then Exit(L);
          Acc := Acc * L.Value;
        end;
        Exit(Finite(Acc, ''));
      end;

    nkDiv:
      begin
        L := Evaluate(ANode[0], AEnv);
        if not L.Ok then Exit(L);
        R := Evaluate(ANode[1], AEnv);
        if not R.Ok then Exit(R);
        if R.Value = 0 then
          Exit(Res(evDivideByZero, NaN, ToInfix(ANode[1]) + ' = 0'));
        Exit(Finite(L.Value / R.Value, ''));
      end;

    nkPow:
      begin
        L := Evaluate(ANode[0], AEnv);
        if not L.Ok then Exit(L);
        R := Evaluate(ANode[1], AEnv);
        if not R.Ok then Exit(R);

        { The two ways a power has no real value, kept apart from a genuine
          overflow so the witness can say which. }
        if (L.Value < 0) and (Frac(R.Value) <> 0) then
          Exit(Res(evDomain, NaN,
            Format('%s^%s with a negative base and a fractional exponent',
                   [ToInfix(ANode[0]), ToInfix(ANode[1])])));
        { 0^-n is 1/(0^n): a division by zero wearing a different hat, and
          worth saying so rather than calling it a domain error. }
        if (L.Value = 0) and (R.Value < 0) then
          Exit(Res(evDivideByZero, NaN, ToInfix(ANode[0]) + ' = 0 raised to a '
               + 'negative power'));

        try
          Acc := Power(L.Value, R.Value);
        except
          Exit(Res(evOverflow, NaN, ToInfix(ANode)));
        end;
        Exit(Finite(Acc, ToInfix(ANode)));
      end;

    nkFunc:
      begin
        SetLength(Args, ANode.Count);
        for I := 0 to ANode.Count - 1 do
        begin
          L := Evaluate(ANode[I], AEnv);
          if not L.Ok then Exit(L);
          Args[I] := L.Value;
        end;
        St := EvalFunction(ANode.Name, Args, V);
        if St <> evOk then Exit(Res(St, NaN, ANode.Name));
        Exit(Finite(V, ANode.Name));
      end;
  end;

  Result := Res(evUnsupported, NaN, ToInfix(ANode));
end;

function EvaluateText(const AText: string; AEnv: TEvalEnv): TEvalResult;
var
  Node: TAstNode;
  Err: string;
begin
  if Trim(AText) = '' then Exit(Res(evUndefined, NaN, '<empty>'));
  if not TryParseRateLaw(AText, Node, Err) then
    Exit(Res(evUnsupported, NaN, AText));
  try
    Result := Evaluate(Node, AEnv);
  finally
    Node.Free;
  end;
end;

function EvaluateCondition(const AText: string; AEnv: TEvalEnv;
  out AKnown: Boolean): Boolean;
const
  Ops: array [0 .. 5] of string = ('>=', '<=', '==', '!=', '>', '<');
var
  I, P: Integer;
  Op, Lhs, Rhs: string;
  L, R: TEvalResult;
begin
  AKnown := False;
  Result := False;

  Op := '';
  for I := 0 to High(Ops) do
  begin
    P := Pos(Ops[I], AText);
    if P > 0 then
    begin
      Op := Ops[I];
      Break;
    end;
  end;
  if Op = '' then Exit;

  Lhs := Trim(Copy(AText, 1, P - 1));
  Rhs := Trim(Copy(AText, P + Length(Op), MaxInt));

  L := EvaluateText(Lhs, AEnv);
  R := EvaluateText(Rhs, AEnv);
  if not (L.Ok and R.Ok) then Exit;

  AKnown := True;
  if Op = '>=' then Result := L.Value >= R.Value
  else if Op = '<=' then Result := L.Value <= R.Value
  else if Op = '==' then Result := SameValue(L.Value, R.Value)
  else if Op = '!=' then Result := not SameValue(L.Value, R.Value)
  else if Op = '>' then Result := L.Value > R.Value
  else Result := L.Value < R.Value;
end;

end.
