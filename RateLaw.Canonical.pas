unit RateLaw.Canonical;

{ Normalisation, so that trivially different but identically-written
  expressions compare equal.

  Canonicalise returns a NEW tree. The pre-canonical tree must survive: a
  parenthesisation defect is visible only before normalisation (normalising is
  exactly what erases it) and a duplicated operand only after, so the static
  engine reads both.

  Rules applied, in the order they are reached bottom-up:

    1. Flatten n-ary associative operators (+, *).
    2. Rewrite a - b as a + (-1)*b, and a / b as a * b^(-1), and -a as (-1)*a.
    3. Fold numeric literal constants.
    4. Sort commutative operand lists by the canonical key.
    5. Collect equal bases in a product, so S*S and S^2 agree.

  WHAT IS DELIBERATELY NOT DONE, and why
  --------------------------------------
  This normalises *writing*, not algebra. Every rule added trades a false
  positive for stylistic variation against a false negative for a real defect,
  and two trades are refused here:

  * Like terms in a sum are NOT collected: Km + Km stays a sum of two
    identical operands rather than becoming 2*Km. That is the founding defect
    of this whole project -- Vm*S/(Km + Km) -- and leaving the duplication
    literally visible in the tree is what lets the static engine name it as a
    duplicated operand rather than as "a coefficient where none was expected".
    The cost is that x + x and 2*x do not compare equal. Accepted knowingly.

  * Products are NOT distributed over sums: (x+y)*z stays as written rather
    than becoming x*z + y*z. Distribution would let a genuine parenthesisation
    error normalise into the correct form and disappear.

  Powers ARE collected (rule 5 is required), which makes the treatment of sums
  and products deliberately asymmetric. That asymmetry is the point, not an
  oversight. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Ast;

{ The caller owns the returned tree. The input is left untouched. }
function Canonicalise(ANode: TAstNode): TAstNode;

{ Parse both, canonicalise both, compare. For the corpus and for quick checks. }
function CanonicallyEqual(const A, B: string): Boolean;

{ The canonical signature of an expression given as text. '' when it will not
  parse -- callers that care about the difference should parse themselves. }
function CanonicalSignature(const AText: string): string;

implementation

uses
  RateLaw.Parser, System.Generics.Defaults;

type
  { A product factor, decomposed as base^exponent so equal bases can be
    collected. A plain identifier is base=itself, exponent=1. }
  TFactor = record
    Base:      TAstNode;            // owned here until it is handed back
    Exponents: TObjectList<TAstNode>;
  end;

function CanonNode(ANode: TAstNode): TAstNode; forward;

{ ------------------------------------------------------------------ flatten }

{ Appends the canonical children of ANode into AInto, flattening nested nodes
  of the same associative kind. Takes ownership of what it appends. }
procedure FlattenInto(ANode: TAstNode; AKind: TNodeKind;
                      AInto: TObjectList<TAstNode>);
begin
  if ANode.Kind = AKind then
  begin
    { Each child must be EXTRACTED before it is passed on. Reading it with
      ANode[I] and freeing ANode afterwards hands out pointers that the node's
      own child list then frees -- every recipient is left holding a dangling
      node. It survives a two-operand product (nothing recurses) and corrupts
      the tree from three operands up, which is exactly the kind of bug that
      looks like a parser problem. }
    while ANode.Count > 0 do
      FlattenInto(ANode.ExtractChild(0), AKind, AInto);
    ANode.Free;
  end
  else
    AInto.Add(ANode);
end;

{ -------------------------------------------------------------------- sums }

{ Consumes the non-numeric terms of ATerms (extracting them, so the caller's
  list no longer owns them) and folds the numeric ones. Numeric terms are LEFT
  in ATerms deliberately: the caller's list owns them and frees them with
  itself, which is what keeps the folded literals from leaking. }
function BuildAdd(ATerms: TObjectList<TAstNode>): TAstNode;
var
  I: Integer;
  Sum: Double;
  V: Double;
  Kept: TObjectList<TAstNode>;
begin
  Sum := 0;
  { Non-owning: it holds nodes this function is handing on to the result. }
  Kept := TObjectList<TAstNode>.Create(False);
  try
    { Backwards, because extracting shrinks the list -- and a Delphi for-loop
      evaluates its bound once, so a forward loop would run off the end.
      Insert(0) puts the survivors back in source order. }
    for I := ATerms.Count - 1 downto 0 do
      if ATerms[I].IsNumber(V) then
        Sum := Sum + V
      else
        Kept.Insert(0, ATerms.Extract(ATerms[I]));

    if Kept.Count = 0 then
      Exit(TAstNode.Num(Sum));

    if (Kept.Count = 1) and (Sum = 0) then
      Exit(Kept[0]);

    Result := TAstNode.Create(nkAdd);
    for I := 0 to Kept.Count - 1 do
      Result.AddChild(Kept[I]);
    { A zero term adds nothing and would only make two equal expressions
      differ by its presence. }
    if Sum <> 0 then
      Result.AddChild(TAstNode.Num(Sum));
    Result.SortChildrenBySignature;
  finally
    Kept.Free;
  end;
end;

{ ---------------------------------------------------------------- products }

{ Splits a canonical factor into base and exponent. The exponent node is a
  clone, so the caller owns both halves independently. }
procedure SplitFactor(AFactor: TAstNode; out ABase, AExp: TAstNode);
begin
  if (AFactor.Kind = nkPow) and (AFactor.Count = 2) then
  begin
    AExp  := AFactor.ExtractChild(1);
    ABase := AFactor.ExtractChild(0);
    AFactor.Free;
  end
  else
  begin
    ABase := AFactor;
    AExp  := TAstNode.Num(1);
  end;
end;

{ Same ownership contract as BuildAdd: non-numeric factors are extracted from
  AFactors, numeric ones are left for the caller's list to free. }
function BuildMul(AFactors: TObjectList<TAstNode>): TAstNode;
var
  I, Found: Integer;
  Coeff, V: Double;
  Base, Exp: TAstNode;
  Taken: TObjectList<TAstNode>;
  Bases: TObjectList<TAstNode>;
  ExpLists: TObjectList<TObjectList<TAstNode>>;
  Keys: TStringList;
  Sig: string;
  ExpNode, Combined: TAstNode;
  Parts: TObjectList<TAstNode>;
  Zero: Boolean;
begin
  Coeff    := 1;
  Zero     := False;
  Taken    := TObjectList<TAstNode>.Create(True);   // owns until split
  Bases    := TObjectList<TAstNode>.Create(False);
  ExpLists := TObjectList<TObjectList<TAstNode>>.Create(True);
  Keys     := TStringList.Create;
  Parts    := TObjectList<TAstNode>.Create(False);
  try
    { Coefficient pass. Backwards, for the same reason as BuildAdd: extracting
      shrinks the list and a for-loop bound is fixed at entry. }
    for I := AFactors.Count - 1 downto 0 do
      if AFactors[I].IsNumber(V) then
      begin
        Coeff := Coeff * V;
        if V = 0 then Zero := True;
      end
      else
        Taken.Insert(0, AFactors.Extract(AFactors[I]));

    { Decided before anything is taken apart, so the early exit has only one
      list to clean up. }
    if Zero then
      Exit(TAstNode.Num(0));

    while Taken.Count > 0 do
    begin
      SplitFactor(Taken.Extract(Taken[0]), Base, Exp);

      { Rule 5: equal bases collect. The key is the base's signature, which is
        already canonical because children were canonicalised first. }
      Sig   := Signature(Base);
      Found := Keys.IndexOf(Sig);
      if Found >= 0 then
      begin
        ExpLists[Found].Add(Exp);
        Base.Free;
      end
      else
      begin
        Keys.Add(Sig);
        Bases.Add(Base);
        ExpLists.Add(TObjectList<TAstNode>.Create(True));
        ExpLists[ExpLists.Count - 1].Add(Exp);
      end;
    end;

    for I := 0 to Bases.Count - 1 do
    begin
      { Exponents of a collected base sum: x^a * x^b is x^(a+b). Routed through
        BuildAdd so numeric exponents fold and the same ownership rules apply --
        leftovers stay in ExpLists[I] and die with it. }
      ExpNode := BuildAdd(ExpLists[I]);

      if ExpNode.IsNumberEqualTo(0) then
      begin
        { x^0 is 1 and contributes nothing to the product. }
        ExpNode.Free;
        Bases[I].Free;
        Continue;
      end;

      if ExpNode.IsNumberEqualTo(1) then
      begin
        ExpNode.Free;
        Parts.Add(Bases[I]);
      end
      else
      begin
        Combined := TAstNode.Create(nkPow);
        Combined.AddChild(Bases[I]);
        Combined.AddChild(ExpNode);
        Parts.Add(Combined);
      end;
    end;

    if Parts.Count = 0 then
      Exit(TAstNode.Num(Coeff));

    if (Parts.Count = 1) and (Coeff = 1) then
      Exit(Parts[0]);

    Result := TAstNode.Create(nkMul);
    { A coefficient of exactly 1 is dropped: it changes nothing and would make
      two equal products differ by its presence. Sorting places the rest. }
    if Coeff <> 1 then
      Result.AddChild(TAstNode.Num(Coeff));
    for I := 0 to Parts.Count - 1 do
      Result.AddChild(Parts[I]);
    Result.SortChildrenBySignature;
  finally
    Parts.Free;
    Keys.Free;
    ExpLists.Free;
    Bases.Free;
    Taken.Free;
  end;
end;

{ ------------------------------------------------------------------- powers }

function BuildPow(ABase, AExp: TAstNode): TAstNode;
var
  B, E: Double;
  Inner, InnerExp: TAstNode;
  Prod: TObjectList<TAstNode>;
begin
  { Rule 3 on powers of literals. Guarded: a negative base with a fractional
    exponent has no real value, and folding it would put a NaN into the tree
    where the expression itself is perfectly legitimate to leave alone. }
  if ABase.IsNumber(B) and AExp.IsNumber(E) then
    if (B > 0) or (Frac(E) = 0) then
    begin
      Result := TAstNode.Num(Power(B, E));
      ABase.Free; AExp.Free;
      Exit;
    end;

  if AExp.IsNumberEqualTo(1) then
  begin
    AExp.Free;
    Exit(ABase);
  end;

  if AExp.IsNumberEqualTo(0) then
  begin
    ABase.Free; AExp.Free;
    Exit(TAstNode.Num(1));
  end;

  { (x^a)^b is x^(a*b). Needed for rule 5 to be consistent: without it,
    (x^2)^3 and x^6 would not collect to the same factor. }
  if ABase.Kind = nkPow then
  begin
    InnerExp := ABase.ExtractChild(1);
    Inner    := ABase.ExtractChild(0);
    ABase.Free;
    Prod := TObjectList<TAstNode>.Create(True);
    try
      Prod.Add(InnerExp);
      Prod.Add(AExp);
      Result := TAstNode.Create(nkPow);
      Result.AddChild(Inner);
      Result.AddChild(BuildMul(Prod));
    finally
      Prod.Free;
    end;
    Exit;
  end;

  Result := TAstNode.Create(nkPow);
  Result.AddChild(ABase);
  Result.AddChild(AExp);
end;

{ ------------------------------------------------------------- the recursion }

function CanonNode(ANode: TAstNode): TAstNode;
var
  Items: TObjectList<TAstNode>;
  I: Integer;
  L, R: TAstNode;
  Fn: TAstNode;
begin
  case ANode.Kind of

    nkNumber: Exit(TAstNode.Num(ANode.Value));
    nkIdent:  Exit(TAstNode.Ident(ANode.Name));

    nkFunc:
      begin
        { Arguments are canonicalised; the argument list is NOT sorted, since
          a function is not commutative in general and pretending otherwise
          would make f(a,b) and f(b,a) the same expression. }
        Fn := TAstNode.Create(nkFunc);
        Fn.Name := ANode.Name;
        for I := 0 to ANode.Count - 1 do
          Fn.AddChild(CanonNode(ANode[I]));
        Exit(Fn);
      end;

    nkAdd, nkSub:
      begin
        Items := TObjectList<TAstNode>.Create(True);
        try
          if ANode.Kind = nkAdd then
          begin
            for I := 0 to ANode.Count - 1 do
              FlattenInto(CanonNode(ANode[I]), nkAdd, Items);
          end
          else
          begin
            { Rule 2: a - b becomes a + (-1)*b. }
            FlattenInto(CanonNode(ANode[0]), nkAdd, Items);
            var Neg := TObjectList<TAstNode>.Create(True);
            try
              Neg.Add(TAstNode.Num(-1));
              Neg.Add(CanonNode(ANode[1]));
              FlattenInto(BuildMul(Neg), nkAdd, Items);
            finally
              Neg.Free;
            end;
          end;
          Result := BuildAdd(Items);
        finally
          Items.Free;
        end;
        Exit;
      end;

    nkNeg:
      begin
        Items := TObjectList<TAstNode>.Create(True);
        try
          Items.Add(TAstNode.Num(-1));
          Items.Add(CanonNode(ANode[0]));
          Result := BuildMul(Items);
        finally
          Items.Free;
        end;
        Exit;
      end;

    nkMul, nkDiv:
      begin
        Items := TObjectList<TAstNode>.Create(True);
        try
          if ANode.Kind = nkMul then
          begin
            for I := 0 to ANode.Count - 1 do
              FlattenInto(CanonNode(ANode[I]), nkMul, Items);
          end
          else
          begin
            { Rule 2: a / b becomes a * b^(-1). }
            FlattenInto(CanonNode(ANode[0]), nkMul, Items);
            FlattenInto(BuildPow(CanonNode(ANode[1]), TAstNode.Num(-1)),
                        nkMul, Items);
          end;
          Result := BuildMul(Items);
        finally
          Items.Free;
        end;
        Exit;
      end;

    nkPow:
      begin
        L := CanonNode(ANode[0]);
        R := CanonNode(ANode[1]);
        Exit(BuildPow(L, R));
      end;
  end;

  { Unreachable for well-formed trees, but a silent nil here would be far
    worse than a clone. }
  Result := ANode.Clone;
end;

{ ------------------------------------------------------------------- public }

function Canonicalise(ANode: TAstNode): TAstNode;
begin
  if ANode = nil then Exit(nil);
  Result := CanonNode(ANode);
end;

function CanonicalSignature(const AText: string): string;
var
  Raw, Canon: TAstNode;
  Err: string;
begin
  Result := '';
  if not TryParseRateLaw(AText, Raw, Err) then Exit;
  try
    Canon := Canonicalise(Raw);
    try
      Result := Signature(Canon);
    finally
      Canon.Free;
    end;
  finally
    Raw.Free;
  end;
end;

function CanonicallyEqual(const A, B: string): Boolean;
var
  SA, SB: string;
begin
  SA := CanonicalSignature(A);
  SB := CanonicalSignature(B);
  Result := (SA <> '') and (SA = SB);
end;

end.
