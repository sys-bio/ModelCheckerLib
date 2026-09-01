unit RateLaw.Diff;

{ Structural difference between two expression trees, and its cost.

  Extracted from the static engine so the BINDER can use it too. Association
  and classification were previously answering the same question with two
  different measures -- an approximate Dice coefficient decided which law to
  compare against, an exact diff decided what was wrong with it -- and they
  disagreed. The approximation is a bag of parts: it cannot tell
  Vm*S^n/(K^n + K^n) from Hill repression, which contains the same parts
  rearranged, even though Hill activation is one edit away and repression is
  two. Every finding was then reported against a law the model never
  resembled.

  One measure now. The distance IS the cost of the diff that will be
  performed, so the law chosen is by construction the law with least to
  explain. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Ast;

type
  TDiffKind = (dfOperator,   // the two nodes are different operators
               dfIdent,      // both identifiers, different names
               dfLiteral,    // both numbers, different values
               dfExponent,   // difference sits in an exponent
               dfDuplicate,  // an operand repeated where distinct ones belong
               dfExtra,      // an operand the model has and the law does not
               dfMissing,    // an operand the law has and the model does not
               dfArity);     // same operator, different number of operands

  TTreeDiff = record
    Kind:         TDiffKind;
    ModelNode:    TAstNode;   // may be nil for dfMissing
    ExpectNode:   TAstNode;   // may be nil for dfExtra
    ModelParent:  TAstNode;
    ExpectParent: TAstNode;
  end;

{ Structural difference between two trees, which must already be in the same
  vocabulary -- role names -- or everything differs. }
procedure DiffTrees(AModel, AExpect: TAstNode; ADiffs: TList<TTreeDiff>);

{ How much of the two trees the diff fails to account for, in [0, 1].

  Each difference costs the size of the larger subtree involved, so replacing
  a leaf is cheap and replacing a whole denominator is not. Normalised by the
  combined size of both trees, which keeps a small expression's single defect
  from scoring the same as a large one's. Identical trees cost nothing. }
function DiffCost(AModel, AExpect: TAstNode): Double;

{ Do these two nodes join the same operands? Tells a substituted operator
  apart from a misplaced parenthesis. See the static engine for why. }
function SameChildMultiset(A, B: TAstNode): Boolean;

{ How many children of AParent have this exact signature -- what makes a
  duplicated operand nameable. }
function CountChildSignature(AParent: TAstNode; const ASig: string): Integer;

{ Nodes in a subtree, root included. }
function NodeCount(ANode: TAstNode): Integer;

implementation

function NodeCount(ANode: TAstNode): Integer;
var
  I: Integer;
begin
  if ANode = nil then Exit(0);
  Result := 1;
  for I := 0 to ANode.Count - 1 do
    Inc(Result, NodeCount(ANode[I]));
end;

function SameChildMultiset(A, B: TAstNode): Boolean;
var
  LA, LB: TStringList;
  I: Integer;
begin
  if (A = nil) or (B = nil) then Exit(False);
  if A.Count <> B.Count then Exit(False);
  if A.Count = 0 then Exit(False);

  LA := TStringList.Create;
  LB := TStringList.Create;
  try
    for I := 0 to A.Count - 1 do LA.Add(Signature(A[I]));
    for I := 0 to B.Count - 1 do LB.Add(Signature(B[I]));
    LA.Sort;
    LB.Sort;
    Result := LA.Text = LB.Text;
  finally
    LB.Free;
    LA.Free;
  end;
end;

function CountChildSignature(AParent: TAstNode; const ASig: string): Integer;
var
  I: Integer;
begin
  Result := 0;
  if AParent = nil then Exit;
  for I := 0 to AParent.Count - 1 do
    if Signature(AParent[I]) = ASig then Inc(Result);
end;

procedure AddDiff(ADiffs: TList<TTreeDiff>; AKind: TDiffKind;
  AModelNode, AExpectNode, AModelParent, AExpectParent: TAstNode);
var
  D: TTreeDiff;
begin
  D.Kind         := AKind;
  D.ModelNode    := AModelNode;
  D.ExpectNode   := AExpectNode;
  D.ModelParent  := AModelParent;
  D.ExpectParent := AExpectParent;
  ADiffs.Add(D);
end;

procedure DiffNodes(AModel, AExpect, AModelParent, AExpectParent: TAstNode;
                    AInExponent: Boolean; ADiffs: TList<TTreeDiff>);
var
  I, J: Integer;
  MLeft, ELeft: TList<TAstNode>;
  Matched: array of Boolean;
  Sig: string;
  Found: Boolean;
begin
  if (AModel = nil) or (AExpect = nil) then Exit;
  if Signature(AModel) = Signature(AExpect) then Exit;

  if AModel.Kind <> AExpect.Kind then
  begin
    if AInExponent then
      AddDiff(ADiffs, dfExponent, AModel, AExpect, AModelParent, AExpectParent)
    else
      AddDiff(ADiffs, dfOperator, AModel, AExpect, AModelParent, AExpectParent);
    Exit;
  end;

  { A leaf that differs inside an exponent is an exponent defect, whatever
    kind of leaf it is. }
  if AInExponent and (AModel.Kind in [nkIdent, nkNumber]) then
  begin
    AddDiff(ADiffs, dfExponent, AModel, AExpect, AModelParent, AExpectParent);
    Exit;
  end;

  case AModel.Kind of
    nkIdent:
      begin
        AddDiff(ADiffs, dfIdent, AModel, AExpect, AModelParent, AExpectParent);
        Exit;
      end;
    nkNumber:
      begin
        AddDiff(ADiffs, dfLiteral, AModel, AExpect, AModelParent, AExpectParent);
        Exit;
      end;
  end;

  { Powers: base and exponent are positional, and a difference in the exponent
    is worth naming separately -- a wrong power is a different mistake from a
    wrong operand and is fixed differently. }
  if AModel.Kind = nkPow then
  begin
    if (AModel.Count = 2) and (AExpect.Count = 2) then
    begin
      DiffNodes(AModel[0], AExpect[0], AModel, AExpect, AInExponent, ADiffs);
      DiffNodes(AModel[1], AExpect[1], AModel, AExpect, True, ADiffs);
    end
    else
      AddDiff(ADiffs, dfArity, AModel, AExpect, AModelParent, AExpectParent);
    Exit;
  end;

  { Commutative operators: children aligned by signature, not by position.
    Aligning positionally would report a + b against b + a as two differences,
    which is not a defect in any sense a user would recognise. }
  if AModel.IsCommutative then
  begin
    MLeft := TList<TAstNode>.Create;
    ELeft := TList<TAstNode>.Create;
    try
      SetLength(Matched, AExpect.Count);
      for J := 0 to AExpect.Count - 1 do Matched[J] := False;

      for I := 0 to AModel.Count - 1 do
      begin
        Sig   := Signature(AModel[I]);
        Found := False;
        for J := 0 to AExpect.Count - 1 do
          if (not Matched[J]) and (Signature(AExpect[J]) = Sig) then
          begin
            Matched[J] := True;
            Found := True;
            Break;
          end;
        if not Found then MLeft.Add(AModel[I]);
      end;

      for J := 0 to AExpect.Count - 1 do
        if not Matched[J] then ELeft.Add(AExpect[J]);

      if (MLeft.Count = 1) and (ELeft.Count = 1) then
      begin
        { ...unless the unmatched model operand is a repeat of one of its own
          siblings. Then the defect is the repetition itself and must be named
          HERE, at the parent holding both copies. Recursing would descend into
          the copy and lose the duplication entirely once the operand is a
          subtree rather than a leaf, as in K^n + K^n. }
        if CountChildSignature(AModel, Signature(MLeft[0])) > 1 then
          AddDiff(ADiffs, dfDuplicate, MLeft[0], ELeft[0], AModel, AExpect)
        else
          DiffNodes(MLeft[0], ELeft[0], AModel, AExpect, AInExponent, ADiffs);
      end
      else
      begin
        for I := 0 to MLeft.Count - 1 do
          AddDiff(ADiffs, dfExtra, MLeft[I], nil, AModel, AExpect);
        for I := 0 to ELeft.Count - 1 do
          AddDiff(ADiffs, dfMissing, nil, ELeft[I], AModel, AExpect);
      end;
    finally
      ELeft.Free;
      MLeft.Free;
    end;
    Exit;
  end;

  { Everything else -- functions, and the pre-canonical Sub and Div -- is
    positional. }
  if AModel.Count <> AExpect.Count then
  begin
    AddDiff(ADiffs, dfArity, AModel, AExpect, AModelParent, AExpectParent);
    Exit;
  end;
  for I := 0 to AModel.Count - 1 do
    DiffNodes(AModel[I], AExpect[I], AModel, AExpect, AInExponent, ADiffs);
end;

procedure DiffTrees(AModel, AExpect: TAstNode; ADiffs: TList<TTreeDiff>);
begin
  DiffNodes(AModel, AExpect, nil, nil, False, ADiffs);
end;

{ The cost of turning one tree into the other, in nodes.

  A cheap tree edit distance, and deliberately NOT the sum of the diff's own
  findings. The diff stops at the first mismatched operator and reports it as
  one difference, which is right for a report -- "the grouping is wrong" is a
  single thing to fix -- but charging the whole subtree for it puts every
  misplaced parenthesis at maximum distance and the reaction associates with
  nothing at all. So this keeps descending past a mismatch and charges only
  what genuinely differs underneath. }
function SubtreeCost(A, B: TAstNode): Integer; forward;

{ Pairs up two sets of operands as cheaply as it can: identical ones first,
  then greedily by least cost, then whatever is left over is charged in full. }
function AlignChildrenCost(A, B: TAstNode): Integer;
var
  MLeft, ELeft: TList<TAstNode>;
  Matched: array of Boolean;
  I, J, Best, BestJ, C: Integer;
  Sig: string;
  Found: Boolean;
begin
  Result := 0;
  MLeft := TList<TAstNode>.Create;
  ELeft := TList<TAstNode>.Create;
  try
    SetLength(Matched, B.Count);
    for J := 0 to B.Count - 1 do Matched[J] := False;

    for I := 0 to A.Count - 1 do
    begin
      Sig := Signature(A[I]);
      Found := False;
      for J := 0 to B.Count - 1 do
        if (not Matched[J]) and (Signature(B[J]) = Sig) then
        begin
          Matched[J] := True;
          Found := True;
          Break;
        end;
      if not Found then MLeft.Add(A[I]);
    end;
    for J := 0 to B.Count - 1 do
      if not Matched[J] then ELeft.Add(B[J]);

    while (MLeft.Count > 0) and (ELeft.Count > 0) do
    begin
      Best := MaxInt; BestJ := 0;
      for J := 0 to ELeft.Count - 1 do
      begin
        C := SubtreeCost(MLeft[0], ELeft[J]);
        if C < Best then begin Best := C; BestJ := J; end;
      end;
      Inc(Result, Best);
      MLeft.Delete(0);
      ELeft.Delete(BestJ);
    end;

    for I := 0 to MLeft.Count - 1 do Inc(Result, NodeCount(MLeft[I]));
    for I := 0 to ELeft.Count - 1 do Inc(Result, NodeCount(ELeft[I]));
  finally
    ELeft.Free;
    MLeft.Free;
  end;
end;

function SubtreeCost(A, B: TAstNode): Integer;
var
  I: Integer;
begin
  if (A = nil) and (B = nil) then Exit(0);
  if A = nil then Exit(NodeCount(B));
  if B = nil then Exit(NodeCount(A));
  if Signature(A) = Signature(B) then Exit(0);

  { A different operator: the node itself is wrong, and whatever it joins is
    compared anyway. }
  if A.Kind <> B.Kind then
  begin
    if (A.Count = 0) or (B.Count = 0) then
      Exit(Max(NodeCount(A), NodeCount(B)));
    Exit(1 + AlignChildrenCost(A, B));
  end;

  if A.Count = 0 then Exit(1);           // two different leaves

  { The SAME commutative operator with a different number of operands is not
    a wrong operator -- it is a missing or extra operand, which the alignment
    already charges for. Adding a penalty for the arity as well charges twice
    for one defect, and it was enough to push k1*A (against a two-substrate
    mass action) past the association floor: the law it is a defective copy
    of was rejected, and the omitted substrate went unreported. }
  if A.IsCommutative then
    Exit(AlignChildrenCost(A, B));

  if A.Count <> B.Count then
    Exit(1 + AlignChildrenCost(A, B));

  Result := 0;
  for I := 0 to A.Count - 1 do
    Inc(Result, SubtreeCost(A[I], B[I]));
end;

function DiffCost(AModel, AExpect: TAstNode): Double;
var
  Total: Integer;
begin
  if (AModel = nil) or (AExpect = nil) then Exit(1);
  if Signature(AModel) = Signature(AExpect) then Exit(0);

  Total := NodeCount(AModel) + NodeCount(AExpect);
  if Total = 0 then Exit(1);

  Result := (2 * SubtreeCost(AModel, AExpect)) / Total;
  if Result > 1 then Result := 1;
end;

end.
