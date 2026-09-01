unit RateLaw.Ast;

{ The expression tree, and the two ways of printing it.

  A node owns its children and frees them, so a tree is freed by freeing its
  root. Canonicalisation never mutates its input -- it returns a new tree --
  because the pre-canonical tree has to survive alongside the canonical one.
  Some defects are visible only before normalisation (a missing parenthesis,
  since normalising is precisely what erases the difference) and some only
  after (a duplicated operand), so the static engine reads both.

  Two printers, for two different jobs:

    ToInfix    readable, minimally parenthesised. This is what a diagnostic
               quotes back to the user, so it must look like something they
               could have typed.

    Signature  a prefix form with every operand explicit. This is the
               canonical key: trees are compared and commutative operands
               sorted by it. It must be a total order and must not depend on
               hash iteration order, or two runs over the same model produce
               different trees and the diff is unstable. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections;

type
  TNodeKind = (
    nkNumber,   // literal
    nkIdent,    // a name
    nkAdd,      // n-ary after canonicalisation, binary as parsed
    nkSub,      // parsed only; canonicalisation rewrites to Add + (-1)*b
    nkMul,      // n-ary after canonicalisation, binary as parsed
    nkDiv,      // parsed only; canonicalisation rewrites to Mul + b^(-1)
    nkPow,      // base, exponent
    nkNeg,      // parsed only; canonicalisation rewrites to (-1)*a
    nkFunc      // Name(args...)
  );

  TAstNode = class
  private
    FKind:     TNodeKind;
    FValue:    Double;
    FName:     string;
    FChildren: TObjectList<TAstNode>;
    function  GetChild(AIndex: Integer): TAstNode;
    function  GetCount: Integer;
  public
    constructor Create(AKind: TNodeKind);
    destructor  Destroy; override;

    class function Num (AValue: Double): TAstNode; static;
    class function Ident(const AName: string): TAstNode; static;
    class function Op  (AKind: TNodeKind; const AChildren: array of TAstNode): TAstNode; static;
    class function Call(const AName: string; const AArgs: array of TAstNode): TAstNode; static;

    { Takes ownership. }
    procedure AddChild(ANode: TAstNode);
    { Hands ownership back to the caller and removes the slot. }
    function  ExtractChild(AIndex: Integer): TAstNode;
    procedure SortChildrenBySignature;

    function Clone: TAstNode;
    function IsNumber(out AValue: Double): Boolean; overload;
    function IsNumber: Boolean; overload;
    function IsNumberEqualTo(AValue: Double): Boolean;
    function IsCommutative: Boolean;

    property Kind:  TNodeKind read FKind;
    property Value: Double    read FValue write FValue;
    property Name:  string    read FName  write FName;
    property Count: Integer   read GetCount;
    property Children[AIndex: Integer]: TAstNode read GetChild; default;
  end;

{ Readable infix, parenthesised only where precedence requires it. }
function ToInfix(ANode: TAstNode): string;

{ The canonical key. Deterministic, total, and independent of any hash order. }
function Signature(ANode: TAstNode): string;

{ Structural equality, by signature. Two trees are equal when they would print
  the same key -- which after canonicalisation is exactly the comparison the
  static engine wants. }
function SameTree(A, B: TAstNode): Boolean;

{ Every identifier in the tree, sorted and de-duplicated. }
function IdentifiersIn(ANode: TAstNode): TArray<string>;

{ True when both trees use exactly the same identifiers the same number of
  times. Same ingredients, whatever the assembly. }
function SameIdentifierMultiset(A, B: TAstNode): Boolean;

{ True when every identifier in A also occurs in B. Multiplicity ignored:
  this asks whether A is built from B's vocabulary, not whether it uses it the
  same number of times. }
function IdentifiersSubsetOf(A, B: TAstNode): Boolean;

{ The signature of every subtree, including the root and every leaf. The
  multiset -- duplicates are kept, because a tree containing S twice is not
  the same shape as one containing it once. }
function SubtreeSignatures(ANode: TAstNode): TArray<string>;

{ How far apart two trees are, in [0, 1]: 0 identical, 1 nothing in common.

  A Dice coefficient over subtree signatures, each tagged with the DEPTH it
  occurs at, so that where a subtree sits counts as well as whether it occurs.

  The depth tag is not decoration. Without it the measure is a bag of parts
  and is blind to arrangement, which fails on exactly the comparison it is
  needed for. Vm*S^n/(K^n + K^n) contains the same parts as Hill repression
  (Vm*K^n/(K^n + S^n)) merely rearranged, and only one part different from
  Hill activation (Vm*S^n/(K^n + S^n)) -- so an untagged multiset called
  repression the closer law, when activation is one edit away and repression
  is two. Every finding was then described against a law the model never
  resembled.

  Still NOT a tree edit distance. Edit distance is the principled measure and
  is expensive on large expressions; this is cheap and monotone in the right
  direction. It decides which law to diff against, never what is wrong with
  it -- the static diff does that, and it is exact. }
function TreeDistance(A, B: TAstNode): Double;

{ A copy with identifiers renamed. Names absent from the map keep their own,
  which is what leaves an extraneous symbol visible instead of silently
  dropping it. }
function CloneRenamed(ANode: TAstNode;
                      const AMap: TDictionary<string, string>): TAstNode;

{ A copy with identifiers replaced by whole subtrees. The map's nodes are
  cloned, never adopted, so the caller keeps ownership of what it passed in.
  Used to substitute a user function's arguments into its body. }
function CloneSubstituted(ANode: TAstNode;
                          const AMap: TDictionary<string, TAstNode>): TAstNode;

{ A number formatted so that equal values always produce equal text.
  Round-trip precision, invariant separator, and no negative zero. }
function NumToKey(AValue: Double): string;

implementation

uses
  System.Generics.Defaults;

var
  { One invariant format settings record, built once. Using the thread's own
    settings would make the canonical key depend on the machine's locale --
    a comma decimal separator would silently change every signature. }
  GInv: TFormatSettings;

function NumToKey(AValue: Double): string;
begin
  if IsNan(AValue) then Exit('nan');
  if IsInfinite(AValue) then
    if AValue > 0 then Exit('inf') else Exit('-inf');
  { -0 and 0 are different bit patterns and the same number. Without this the
    same expression can canonicalise two ways depending on how a fold landed. }
  if AValue = 0 then AValue := 0;
  Result := FloatToStr(AValue, GInv);
end;

{ ------------------------------------------------------------------ TAstNode }

constructor TAstNode.Create(AKind: TNodeKind);
begin
  inherited Create;
  FKind := AKind;
  FChildren := TObjectList<TAstNode>.Create(True);
end;

destructor TAstNode.Destroy;
begin
  FChildren.Free;
  inherited;
end;

class function TAstNode.Num(AValue: Double): TAstNode;
begin
  Result := TAstNode.Create(nkNumber);
  Result.FValue := AValue;
end;

class function TAstNode.Ident(const AName: string): TAstNode;
begin
  Result := TAstNode.Create(nkIdent);
  Result.FName := AName;
end;

class function TAstNode.Op(AKind: TNodeKind;
  const AChildren: array of TAstNode): TAstNode;
var
  N: TAstNode;
begin
  Result := TAstNode.Create(AKind);
  for N in AChildren do
    Result.AddChild(N);
end;

class function TAstNode.Call(const AName: string;
  const AArgs: array of TAstNode): TAstNode;
var
  N: TAstNode;
begin
  Result := TAstNode.Create(nkFunc);
  Result.FName := AName;
  for N in AArgs do
    Result.AddChild(N);
end;

procedure TAstNode.AddChild(ANode: TAstNode);
begin
  FChildren.Add(ANode);
end;

function TAstNode.ExtractChild(AIndex: Integer): TAstNode;
begin
  Result := FChildren.Extract(FChildren[AIndex]);
end;

function TAstNode.GetChild(AIndex: Integer): TAstNode;
begin
  Result := FChildren[AIndex];
end;

function TAstNode.GetCount: Integer;
begin
  Result := FChildren.Count;
end;

function TAstNode.IsCommutative: Boolean;
begin
  Result := FKind in [nkAdd, nkMul];
end;

procedure TAstNode.SortChildrenBySignature;
var
  Keys: TDictionary<TAstNode, string>;
  I: Integer;
  Items: TArray<TAstNode>;
begin
  if FChildren.Count < 2 then Exit;

  { Signatures are computed once and cached, not recomputed inside the
    comparison. Signature is recursive, so sorting on it directly would be
    quadratic in the depth of the tree for no reason. }
  Keys := TDictionary<TAstNode, string>.Create;
  try
    SetLength(Items, FChildren.Count);
    for I := 0 to FChildren.Count - 1 do
    begin
      Items[I] := FChildren[I];
      Keys.Add(Items[I], Signature(Items[I]));
    end;

    TArray.Sort<TAstNode>(Items, TComparer<TAstNode>.Construct(
      function(const A, B: TAstNode): Integer
      begin
        Result := CompareStr(Keys[A], Keys[B]);
      end));

    { OwnsObjects is on, so the list must not be allowed to free anything
      while it is being reordered. Extract every node first, then re-add. }
    for I := FChildren.Count - 1 downto 0 do
      FChildren.Extract(FChildren[I]);
    for I := 0 to High(Items) do
      FChildren.Add(Items[I]);
  finally
    Keys.Free;
  end;
end;

function TAstNode.Clone: TAstNode;
var
  I: Integer;
begin
  Result := TAstNode.Create(FKind);
  Result.FValue := FValue;
  Result.FName  := FName;
  for I := 0 to FChildren.Count - 1 do
    Result.AddChild(FChildren[I].Clone);
end;

function TAstNode.IsNumber(out AValue: Double): Boolean;
begin
  Result := FKind = nkNumber;
  if Result then AValue := FValue else AValue := NaN;
end;

function TAstNode.IsNumber: Boolean;
begin
  Result := FKind = nkNumber;
end;

function TAstNode.IsNumberEqualTo(AValue: Double): Boolean;
begin
  Result := (FKind = nkNumber) and SameValue(FValue, AValue);
end;

{ ----------------------------------------------------------------- Signature }

function Signature(ANode: TAstNode): string;
var
  SB: TStringBuilder;
  I: Integer;
  Tag: string;
begin
  if ANode = nil then Exit('<nil>');

  case ANode.Kind of
    nkNumber: Exit('#' + NumToKey(ANode.Value));
    { Identifiers are prefixed so a name can never collide with an operator
      tag or a number. }
    nkIdent:  Exit('$' + ANode.Name);
    nkAdd: Tag := '+';
    nkSub: Tag := '-';
    nkMul: Tag := '*';
    nkDiv: Tag := '/';
    nkPow: Tag := '^';
    nkNeg: Tag := 'neg';
    nkFunc: Tag := 'fn:' + ANode.Name;
  end;

  SB := TStringBuilder.Create;
  try
    SB.Append(Tag).Append('(');
    for I := 0 to ANode.Count - 1 do
    begin
      if I > 0 then SB.Append(',');
      SB.Append(Signature(ANode[I]));
    end;
    SB.Append(')');
    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

function SameTree(A, B: TAstNode): Boolean;
begin
  Result := Signature(A) = Signature(B);
end;

{ ------------------------------------------------------------------- ToInfix }

function Precedence(AKind: TNodeKind): Integer;
begin
  case AKind of
    nkAdd, nkSub: Result := 1;
    nkMul, nkDiv: Result := 2;
    nkNeg:        Result := 3;
    nkPow:        Result := 4;
  else
    Result := 10;   // atoms and calls never need wrapping
  end;
end;

function ToInfix(ANode: TAstNode): string;

  function Wrap(AChild: TAstNode; AMinPrec: Integer): string;
  begin
    Result := ToInfix(AChild);
    if Precedence(AChild.Kind) < AMinPrec then
      Result := '(' + Result + ')';
  end;

var
  I: Integer;
  Sep: string;
  MyPrec: Integer;
begin
  if ANode = nil then Exit('');

  case ANode.Kind of
    nkNumber: Exit(NumToKey(ANode.Value));
    nkIdent:  Exit(ANode.Name);

    nkFunc:
      begin
        Result := ANode.Name + '(';
        for I := 0 to ANode.Count - 1 do
        begin
          if I > 0 then Result := Result + ', ';
          Result := Result + ToInfix(ANode[I]);
        end;
        Result := Result + ')';
        Exit;
      end;

    nkNeg:
      { Binds looser than ^, so -x^2 prints without parentheses and means
        -(x^2), which is what it parsed as. }
      Exit('-' + Wrap(ANode[0], Precedence(nkNeg)));

    nkPow:
      begin
        { Right-associative: the exponent may be a power without parentheses,
          the base may not. }
        Result := Wrap(ANode[0], Precedence(nkPow) + 1) + '^' +
                  Wrap(ANode[1], Precedence(nkPow));
        Exit;
      end;
  end;

  MyPrec := Precedence(ANode.Kind);
  case ANode.Kind of
    nkAdd: Sep := ' + ';
    nkSub: Sep := ' - ';
    nkMul: Sep := '*';
  else     Sep := '/';
  end;

  Result := '';
  for I := 0 to ANode.Count - 1 do
  begin
    if I > 0 then Result := Result + Sep;
    { EVERY operand after the first is wrapped one level higher, not just the
      right operand of - and /.

      These operators are left-associative, so a child of equal precedence in
      any position but the first has to be parenthesised or the text reparses
      into a different tree. a*(b/c) printed as a*b/c reads back as (a*b)/c,
      and a - (b - c) as a - b - c. Both are numerically equal and neither is
      the tree that was printed.

      That matters beyond tidiness: this text is what a diagnostic quotes back
      to the user, and the mutation harness reparses it. A printer that does
      not round-trip makes the engine analyse one expression and report
      another. }
    if I > 0 then
      Result := Result + Wrap(ANode[I], MyPrec + 1)
    else
      Result := Result + Wrap(ANode[I], MyPrec);
  end;
end;

{ ------------------------------------------------------------- IdentifiersIn }

procedure CollectIdents(ANode: TAstNode; AList: TStringList);
var
  I: Integer;
begin
  if ANode = nil then Exit;
  if ANode.Kind = nkIdent then
    AList.Add(ANode.Name);
  for I := 0 to ANode.Count - 1 do
    CollectIdents(ANode[I], AList);
end;

function IdentifiersIn(ANode: TAstNode): TArray<string>;
var
  L: TStringList;
  I: Integer;
begin
  L := TStringList.Create;
  try
    L.Sorted     := True;
    L.Duplicates := dupIgnore;
    CollectIdents(ANode, L);
    SetLength(Result, L.Count);
    for I := 0 to L.Count - 1 do
      Result[I] := L[I];
  finally
    L.Free;
  end;
end;

{ -------------------------------------------------------- subtree signatures }

procedure CollectSubtrees(ANode: TAstNode; AList: TStringList);
var
  I: Integer;
begin
  if ANode = nil then Exit;
  AList.Add(Signature(ANode));
  for I := 0 to ANode.Count - 1 do
    CollectSubtrees(ANode[I], AList);
end;

{ The same, with each signature tagged by the depth it occurs at. }
procedure CollectPositional(ANode: TAstNode; ADepth: Integer;
                            AList: TStringList);
var
  I: Integer;
begin
  if ANode = nil then Exit;
  AList.Add(IntToStr(ADepth) + '|' + Signature(ANode));
  for I := 0 to ANode.Count - 1 do
    CollectPositional(ANode[I], ADepth + 1, AList);
end;

function PositionalSignatures(ANode: TAstNode): TArray<string>;
var
  L: TStringList;
  I: Integer;
begin
  L := TStringList.Create;
  try
    CollectPositional(ANode, 0, L);
    L.Sort;
    SetLength(Result, L.Count);
    for I := 0 to L.Count - 1 do
      Result[I] := L[I];
  finally
    L.Free;
  end;
end;

function SubtreeSignatures(ANode: TAstNode): TArray<string>;
var
  L: TStringList;
  I: Integer;
begin
  L := TStringList.Create;
  try
    { Not Sorted with dupIgnore: this is a multiset. Collapsing duplicates
      would make Km + Km and Km + S look equally close to Km + S. }
    CollectSubtrees(ANode, L);
    L.Sort;
    SetLength(Result, L.Count);
    for I := 0 to L.Count - 1 do
      Result[I] := L[I];
  finally
    L.Free;
  end;
end;

function SameIdentifierMultiset(A, B: TAstNode): Boolean;

  function Bag(ANode: TAstNode): string;
  var
    L: TStringList;
    Sig: string;
  begin
    L := TStringList.Create;
    try
      for Sig in SubtreeSignatures(ANode) do
        if Sig.StartsWith('$') then L.Add(Sig);
      L.Sort;
      Result := L.Text;
    finally
      L.Free;
    end;
  end;

begin
  if (A = nil) or (B = nil) then Exit(False);
  Result := Bag(A) = Bag(B);
end;

function IdentifiersSubsetOf(A, B: TAstNode): Boolean;
var
  Name: string;
  Outer: TArray<string>;
  Found: Boolean;
  I: Integer;
begin
  if (A = nil) or (B = nil) then Exit(False);
  Outer := IdentifiersIn(B);
  for Name in IdentifiersIn(A) do
  begin
    Found := False;
    for I := 0 to High(Outer) do
      if Outer[I] = Name then begin Found := True; Break; end;
    if not Found then Exit(False);
  end;
  Result := True;
end;

function TreeDistance(A, B: TAstNode): Double;
var
  SA, SB: TArray<string>;
  I, J, Common: Integer;
  C: Integer;
begin
  if (A = nil) or (B = nil) then Exit(1);
  if Signature(A) = Signature(B) then Exit(0);

  SA := PositionalSignatures(A);
  SB := PositionalSignatures(B);
  if (Length(SA) = 0) or (Length(SB) = 0) then Exit(1);

  { Both arrays are sorted, so the multiset intersection is a merge. }
  Common := 0; I := 0; J := 0;
  while (I < Length(SA)) and (J < Length(SB)) do
  begin
    C := CompareStr(SA[I], SB[J]);
    if C = 0 then begin Inc(Common); Inc(I); Inc(J); end
    else if C < 0 then Inc(I)
    else Inc(J);
  end;

  Result := 1 - (2 * Common) / (Length(SA) + Length(SB));
  if Result < 0 then Result := 0;
end;

{ ------------------------------------------------------------- CloneRenamed }

function CloneRenamed(ANode: TAstNode;
  const AMap: TDictionary<string, string>): TAstNode;
var
  I: Integer;
  NewName: string;
begin
  if ANode = nil then Exit(nil);

  if ANode.Kind = nkIdent then
  begin
    if (AMap <> nil) and AMap.TryGetValue(ANode.Name, NewName) then
      Result := TAstNode.Ident(NewName)
    else
      Result := TAstNode.Ident(ANode.Name);
    Exit;
  end;

  if ANode.Kind = nkNumber then
    Exit(TAstNode.Num(ANode.Value));

  Result := TAstNode.Create(ANode.Kind);
  Result.Name := ANode.Name;   { function names are not renamed }
  for I := 0 to ANode.Count - 1 do
    Result.AddChild(CloneRenamed(ANode[I], AMap));
end;

function CloneSubstituted(ANode: TAstNode;
  const AMap: TDictionary<string, TAstNode>): TAstNode;
var
  I: Integer;
  Sub: TAstNode;
begin
  if ANode = nil then Exit(nil);

  if ANode.Kind = nkIdent then
  begin
    if (AMap <> nil) and AMap.TryGetValue(ANode.Name, Sub) then
      Result := Sub.Clone
    else
      Result := TAstNode.Ident(ANode.Name);
    Exit;
  end;

  if ANode.Kind = nkNumber then
    Exit(TAstNode.Num(ANode.Value));

  Result := TAstNode.Create(ANode.Kind);
  Result.Name := ANode.Name;
  for I := 0 to ANode.Count - 1 do
    Result.AddChild(CloneSubstituted(ANode[I], AMap));
end;

initialization
  GInv := TFormatSettings.Invariant;
  { Round-trip precision. The default 15 digits loses the distinction between
    numbers that differ only in the last bit, which would make two different
    literals share a signature. }
  GInv.DecimalSeparator := '.';

end.
