unit RateLaw.Mutate;

{ Programmatic mutation of a correct rate law, for measuring what the static
  engine can actually discriminate.

  A checker tested only on Michaelis-Menten proves nothing: two operators and
  three symbols leave almost nowhere for a defect to hide. The question that
  matters is whether the same generic rules still separate one defect class
  from another inside an expression with four parameters, nested sums in a
  denominator, and the same identifier occurring five times.

  So: take a law's own canonical expression, break it in a known way, and see
  whether the engine names the break correctly. The mutation kind IS the
  expected defect class, which makes the measurement objective -- no one gets
  to decide after the fact that whatever came out was close enough.

  These are deliberately the mutations a person makes: a slipped operator, a
  copied-and-not-edited operand, a parenthesis in the wrong place, two
  identifiers transposed, an exponent left off. Not random corruption. }

interface

uses
  System.SysUtils, System.Classes, System.Generics.Collections,
  RateLaw.Ast, RateLaw.Parser, RateLaw.Canonical;

type
  TMutation = record
    Kind:     string;   // see MutationKinds
    Expected: string;   // the defect code this must produce
    Expr:     string;   // the mutated expression
    Note:     string;   // what was done, for the report
  end;

{ Every applicable mutation of AExpr. An expression with no power has no
  exponent mutation, and so on -- inapplicable mutations are omitted rather
  than faked. }
function MutationsOf(const AExpr: string): TArray<TMutation>;

{ Every kind this unit can produce, in report order. A kind that no law can
  exercise is a gap in the CORPUS; a kind exercised and not detected is a gap
  in the ENGINE, and the coverage report has to tell them apart. }
function MutationKinds: TArray<string>;

implementation

function MutationKinds: TArray<string>;
begin
  Result := ['operator', 'duplicate', 'regroup', 'transpose', 'exponent',
             'drop', 'invert'];
end;

{ -------------------------------------------------------------- tree search }

function FindKind(ANode: TAstNode; AKind: TNodeKind;
                  AMinChildren: Integer = 0): TAstNode;
var
  I: Integer;
begin
  if ANode = nil then Exit(nil);
  if (ANode.Kind = AKind) and (ANode.Count >= AMinChildren) then Exit(ANode);
  for I := 0 to ANode.Count - 1 do
  begin
    Result := FindKind(ANode[I], AKind, AMinChildren);
    if Result <> nil then Exit;
  end;
  Result := nil;
end;

{ A Div whose divisor is a sum -- the shape a misplaced parenthesis attacks. }
function FindDivOverSum(ANode: TAstNode): TAstNode;
var
  I: Integer;
begin
  if ANode = nil then Exit(nil);
  if (ANode.Kind = nkDiv) and (ANode.Count = 2) and
     (ANode[1].Kind = nkAdd) and (ANode[1].Count >= 2) then Exit(ANode);
  for I := 0 to ANode.Count - 1 do
  begin
    Result := FindDivOverSum(ANode[I]);
    if Result <> nil then Exit;
  end;
  Result := nil;
end;

{ The terms of a sum, however it was nested. Clones, so the caller owns them
  independently of the tree they came from. }
procedure FlattenSum(ANode: TAstNode; AInto: TObjectList<TAstNode>);
var
  I: Integer;
begin
  if ANode = nil then Exit;
  if ANode.Kind = nkAdd then
    for I := 0 to ANode.Count - 1 do
      FlattenSum(ANode[I], AInto)
  else
    AInto.Add(ANode.Clone);
end;

procedure RenameIdent(ANode: TAstNode; const AFrom, ATo: string);
var
  I: Integer;
begin
  if ANode = nil then Exit;
  if (ANode.Kind = nkIdent) and (ANode.Name = AFrom) then
    ANode.Name := ATo;
  for I := 0 to ANode.Count - 1 do
    RenameIdent(ANode[I], AFrom, ATo);
end;

{ Replaces AOld, a child of AParent, with ANew. AOld is freed. }
procedure ReplaceChild(AParent, AOld, ANew: TAstNode);
var
  I: Integer;
  Kept: TObjectList<TAstNode>;
begin
  { TObjectList owns its children, so the old node has to be extracted before
    anything else touches the list, and the replacement inserted at the same
    position -- appending would silently reorder a non-commutative operator. }
  Kept := TObjectList<TAstNode>.Create(False);
  try
    for I := 0 to AParent.Count - 1 do
      if AParent[I] = AOld then Kept.Add(ANew)
      else Kept.Add(AParent[I]);
    for I := AParent.Count - 1 downto 0 do
      AParent.ExtractChild(I);
    AOld.Free;
    for I := 0 to Kept.Count - 1 do
      AParent.AddChild(Kept[I]);
  finally
    Kept.Free;
  end;
end;

function ParentOf(ARoot, AChild: TAstNode): TAstNode;
var
  I: Integer;
begin
  if ARoot = nil then Exit(nil);
  for I := 0 to ARoot.Count - 1 do
    if ARoot[I] = AChild then Exit(ARoot);
  for I := 0 to ARoot.Count - 1 do
  begin
    Result := ParentOf(ARoot[I], AChild);
    if Result <> nil then Exit;
  end;
  Result := nil;
end;

{ ---------------------------------------------------------------- mutations }

function MutationsOf(const AExpr: string): TArray<TMutation>;
var
  Err: string;
  { Accumulated here rather than through Result: inside the nested Add,
    Result names Add's own result, and naming the outer function instead
    reads as a recursive call. }
  Acc: TArray<TMutation>;

  function Add(const AKind, AExpected, ANote: string;
               ATree: TAstNode): Boolean;
  var
    M: TMutation;
  begin
    Result := False;
    if ATree = nil then Exit;
    M.Kind     := AKind;
    M.Expected := AExpected;
    M.Note     := ANote;
    M.Expr := ToInfix(ATree);

    { A mutation that changes nothing is not a mutation, and comparing the
      TEXT is not enough to tell. Transposing the two operands of a product
      gives Si*k where the original was k*Si -- different text, identical
      expression -- and scoring the engine for failing to report it measures
      the harness rather than the engine. Compared canonically. }
    if (M.Expr <> AExpr) and
       not CanonicallyEqual(M.Expr, AExpr) then
    begin
      Acc := Acc + [M];
      Result := True;
    end;
  end;

  { --- operator substitution: a sum in a denominator becomes a product --- }
  procedure MutateOperator;
  var
    T, Target, NewNode: TAstNode;
    I: Integer;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindKind(T, nkAdd, 2);
      if Target = nil then Exit;
      NewNode := TAstNode.Create(nkMul);
      for I := 0 to Target.Count - 1 do
        NewNode.AddChild(Target[I].Clone);
      if Target = T then
      begin
        Add('operator', 'S003', 'a sum written as a product', NewNode);
        NewNode.Free;
      end
      else
      begin
        ReplaceChild(ParentOf(T, Target), Target, NewNode);
        Add('operator', 'S003', 'a sum written as a product', T);
      end;
    finally
      T.Free;
    end;
  end;

  { --- duplicated operand: the Km + Km slip --- }
  procedure MutateDuplicate;
  var
    T, Target, Terms, Rebuilt, Chain: TAstNode;
    Flat: TObjectList<TAstNode>;
    I, Src, Dst: Integer;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindKind(T, nkAdd, 2);
      if Target = nil then Exit;

      { A sum of three or more terms parses left-nested, so replacing the
        outer node's second child would swap out everything but the last
        term -- a mutation that both duplicates and deletes, which is not the
        slip being modelled and is not fair to score as one. Flattening first
        makes this replace exactly one term of the sum. }
      Flat := TObjectList<TAstNode>.Create(True);
      try
        FlattenSum(Target, Flat);
        if Flat.Count < 2 then Exit;

        { Two distinct NON-NUMERIC terms. Duplicating a literal is folded away
          by constant folding -- 1 + 1 becomes 2 -- so the mutant never has
          the duplicated-operand shape and scoring the engine against it would
          be measuring the harness. }
        Src := -1; Dst := -1;
        for I := 0 to Flat.Count - 1 do
          if not Flat[I].IsNumber then
            if Src < 0 then Src := I
            else if Signature(Flat[I]) <> Signature(Flat[Src]) then
            begin
              Dst := I;
              Break;
            end;
        if (Src < 0) or (Dst < 0) then Exit;

        Chain := nil;
        for I := 0 to Flat.Count - 1 do
        begin
          if I = Dst then Terms := Flat[Src].Clone else Terms := Flat[I].Clone;
          if Chain = nil then Chain := Terms
          else Chain := TAstNode.Op(nkAdd, [Chain, Terms]);
        end;

        if Target = T then
        begin
          Add('duplicate', 'S004', 'one term copied over its neighbour', Chain);
          Chain.Free;
        end
        else
        begin
          Rebuilt := ParentOf(T, Target);
          ReplaceChild(Rebuilt, Target, Chain);
          Add('duplicate', 'S004', 'one term copied over its neighbour', T);
        end;
      finally
        Flat.Free;
      end;
    finally
      T.Free;
    end;
  end;

  { --- regrouping: a/(b + c) written as a/b + c --- }
  procedure MutateRegroup;
  var
    T, Target, Sum, NewAdd, NewDiv: TAstNode;
    I: Integer;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindDivOverSum(T);
      if Target = nil then Exit;

      Sum := Target[1];
      NewDiv := TAstNode.Create(nkDiv);
      NewDiv.AddChild(Target[0].Clone);
      NewDiv.AddChild(Sum[0].Clone);

      NewAdd := TAstNode.Create(nkAdd);
      NewAdd.AddChild(NewDiv);
      for I := 1 to Sum.Count - 1 do
        NewAdd.AddChild(Sum[I].Clone);

      if Target = T then
      begin
        Add('regroup', 'S010', 'a closing parenthesis moved left', NewAdd);
        NewAdd.Free;
      end
      else
      begin
        ReplaceChild(ParentOf(T, Target), Target, NewAdd);
        Add('regroup', 'S010', 'a closing parenthesis moved left', T);
      end;
    finally
      T.Free;
    end;
  end;

  { --- transposition: two identifiers exchanged throughout --- }
  procedure MutateTranspose;
  var
    T: TAstNode;
    Ids: TArray<string>;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Ids := IdentifiersIn(T);
      if Length(Ids) < 2 then Exit;
      RenameIdent(T, Ids[0], '__tmp__');
      RenameIdent(T, Ids[1], Ids[0]);
      RenameIdent(T, '__tmp__', Ids[1]);
      Add('transpose', 'S007',
          Format('%s and %s exchanged', [Ids[0], Ids[1]]), T);
    finally
      T.Free;
    end;
  end;

  { --- exponent: a power quietly changed --- }
  procedure MutateExponent;
  var
    T, Target, NewPow: TAstNode;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindKind(T, nkPow, 2);
      if Target = nil then Exit;
      NewPow := TAstNode.Create(nkPow);
      NewPow.AddChild(Target[0].Clone);
      if Target[1].Kind = nkNumber then
        NewPow.AddChild(TAstNode.Num(Target[1].Value + 1))
      else
        NewPow.AddChild(TAstNode.Num(2));
      if Target = T then
      begin
        Add('exponent', 'S008', 'the exponent changed', NewPow);
        NewPow.Free;
      end
      else
      begin
        ReplaceChild(ParentOf(T, Target), Target, NewPow);
        Add('exponent', 'S008', 'the exponent changed', T);
      end;
    finally
      T.Free;
    end;
  end;

  { --- a term of a sum simply left out --- }
  procedure MutateDropTerm;
  var
    T, Target, Chain, Term: TAstNode;
    Flat: TObjectList<TAstNode>;
    I, Drop: Integer;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindKind(T, nkAdd, 2);
      if Target = nil then Exit;
      Flat := TObjectList<TAstNode>.Create(True);
      try
        FlattenSum(Target, Flat);
        if Flat.Count < 2 then Exit;

        { Drop a non-numeric term: dropping a literal is usually absorbed by
          constant folding and would not model the mistake. }
        Drop := -1;
        for I := 0 to Flat.Count - 1 do
          if not Flat[I].IsNumber then begin Drop := I; Break; end;
        if Drop < 0 then Exit;

        Chain := nil;
        for I := 0 to Flat.Count - 1 do
        begin
          if I = Drop then Continue;
          Term := Flat[I].Clone;
          if Chain = nil then Chain := Term
          else Chain := TAstNode.Op(nkAdd, [Chain, Term]);
        end;
        if Chain = nil then Exit;

        if Target = T then
        begin
          Add('drop', 'S005', 'a term of a sum left out', Chain);
          Chain.Free;
        end
        else
        begin
          ReplaceChild(ParentOf(T, Target), Target, Chain);
          Add('drop', 'S005', 'a term of a sum left out', T);
        end;
      finally
        Flat.Free;
      end;
    finally
      T.Free;
    end;
  end;

  { --- a numerator and denominator the wrong way round --- }
  procedure MutateInvert;
  var
    T, Target, NewDiv: TAstNode;
  begin
    if not TryParseRateLaw(AExpr, T, Err) then Exit;
    try
      Target := FindKind(T, nkDiv, 2);
      if Target = nil then Exit;
      NewDiv := TAstNode.Create(nkDiv);
      NewDiv.AddChild(Target[1].Clone);
      NewDiv.AddChild(Target[0].Clone);
      if Target = T then
      begin
        Add('invert', 'S010', 'a division turned upside down', NewDiv);
        NewDiv.Free;
      end
      else
      begin
        ReplaceChild(ParentOf(T, Target), Target, NewDiv);
        Add('invert', 'S010', 'a division turned upside down', T);
      end;
    finally
      T.Free;
    end;
  end;

begin
  Acc := nil;
  MutateOperator;
  MutateDuplicate;
  MutateRegroup;
  MutateTranspose;
  MutateExponent;
  MutateDropTerm;
  MutateInvert;
  Result := Acc;
end;

end.
