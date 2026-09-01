unit RateLaw.Parser;

{ Infix parser for Antimony-compatible rate law expressions.

  One parser, used for both sides of every comparison: the model's rate law
  text and the registry's canonical expression. That is deliberate. Feeding
  the two sides through different front-ends -- MathML for one, infix for the
  other -- would let them drift, and a structural diff between two trees built
  by different code is comparing the front-ends as much as the expressions.

  Precedence and associativity follow Antimony/SBML:

      + -            left
      * /            left
      unary -        binds looser than ^, so -x^2 is -(x^2)
      ^              RIGHT associative, so 2^3^2 is 2^(3^2)

  The tree produced is the *pre-canonical* one: subtraction is nkSub, division
  is nkDiv, unary minus is nkNeg, and n-ary operators are still binary and
  nested exactly as written. Canonicalisation rewrites all of that, and the
  static engine keeps both. }

interface

uses
  System.SysUtils, System.Classes, System.Character, System.Math,
  RateLaw.Ast;

type
  ERateLawParseError = class(Exception)
  private
    FPosition: Integer;
  public
    constructor Create(const AMessage: string; APosition: Integer);
    { 1-based character position in the source expression. }
    property Position: Integer read FPosition;
  end;

  TTokenKind = (tkEnd, tkNumber, tkIdent, tkPlus, tkMinus, tkStar, tkSlash,
                tkCaret, tkLParen, tkRParen, tkComma);

  TToken = record
    Kind:     TTokenKind;
    Text:     string;
    Value:    Double;
    Position: Integer;   // 1-based
  end;

  TRateLawLexer = class
  private
    FText: string;
    FPos:  Integer;
    procedure SkipSpace;
  public
    constructor Create(const AText: string);
    function Next: TToken;
    class function Tokenize(const AText: string): TArray<TToken>;
  end;

  TRateLawParser = class
  private
    FTokens:  TArray<TToken>;
    FIndex:   Integer;
    FSource:  string;
    function  Peek: TToken;
    function  Take: TToken;
    function  Accept(AKind: TTokenKind): Boolean;
    procedure Expect(AKind: TTokenKind; const AWhat: string);
    function  ParseExpression: TAstNode;
    function  ParseTerm: TAstNode;
    function  ParseUnary: TAstNode;
    function  ParsePower: TAstNode;
    function  ParsePrimary: TAstNode;
  public
    { Raises ERateLawParseError on malformed input. The caller owns the tree. }
    function Parse(const AText: string): TAstNode;
  end;

{ Convenience: parse and return the tree, or nil with AError set. Rate laws
  arrive from models that may be broken in any way at all, so most callers
  want to report a bad expression rather than catch an exception. }
function TryParseRateLaw(const AText: string; out ANode: TAstNode;
                         out AError: string): Boolean;

{ Raises on failure. For registry expressions and tests, where a malformed
  expression is a bug rather than a finding. }
function ParseRateLaw(const AText: string): TAstNode;

implementation

var
  GInv: TFormatSettings;

{ -------------------------------------------------------- ERateLawParseError }

constructor ERateLawParseError.Create(const AMessage: string; APosition: Integer);
begin
  inherited Create(AMessage);
  FPosition := APosition;
end;

{ -------------------------------------------------------------- TRateLawLexer }

constructor TRateLawLexer.Create(const AText: string);
begin
  inherited Create;
  FText := AText;
  FPos  := 1;
end;

procedure TRateLawLexer.SkipSpace;
begin
  while (FPos <= Length(FText)) and
        (FText[FPos].IsWhiteSpace) do
    Inc(FPos);
end;

function TRateLawLexer.Next: TToken;
var
  Start: Integer;
  S: string;

  function IsIdentStart(C: Char): Boolean;
  begin
    Result := C.IsLetter or (C = '_');
  end;

  function IsIdentPart(C: Char): Boolean;
  begin
    Result := C.IsLetterOrDigit or (C = '_');
  end;

begin
  SkipSpace;
  Result := Default(TToken);
  Result.Position := FPos;

  if FPos > Length(FText) then
  begin
    Result.Kind := tkEnd;
    Exit;
  end;

  case FText[FPos] of
    '+': begin Result.Kind := tkPlus;   Result.Text := '+'; Inc(FPos); Exit; end;
    '-': begin Result.Kind := tkMinus;  Result.Text := '-'; Inc(FPos); Exit; end;
    '*': begin Result.Kind := tkStar;   Result.Text := '*'; Inc(FPos); Exit; end;
    '/': begin Result.Kind := tkSlash;  Result.Text := '/'; Inc(FPos); Exit; end;
    '^': begin Result.Kind := tkCaret;  Result.Text := '^'; Inc(FPos); Exit; end;
    '(': begin Result.Kind := tkLParen; Result.Text := '('; Inc(FPos); Exit; end;
    ')': begin Result.Kind := tkRParen; Result.Text := ')'; Inc(FPos); Exit; end;
    ',': begin Result.Kind := tkComma;  Result.Text := ','; Inc(FPos); Exit; end;
  end;

  { A number. Leading '.' is accepted ('.5'), and an exponent only when it is
    actually followed by digits -- otherwise the 'e' in 'Km1e' would be eaten
    as an exponent marker and the identifier silently truncated. }
  if FText[FPos].IsDigit or
     ((FText[FPos] = '.') and (FPos < Length(FText)) and FText[FPos + 1].IsDigit) then
  begin
    Start := FPos;
    while (FPos <= Length(FText)) and FText[FPos].IsDigit do Inc(FPos);
    if (FPos <= Length(FText)) and (FText[FPos] = '.') then
    begin
      Inc(FPos);
      while (FPos <= Length(FText)) and FText[FPos].IsDigit do Inc(FPos);
    end;
    if (FPos <= Length(FText)) and CharInSet(FText[FPos], ['e', 'E']) then
    begin
      var Save := FPos;
      Inc(FPos);
      if (FPos <= Length(FText)) and CharInSet(FText[FPos], ['+', '-']) then
        Inc(FPos);
      if (FPos <= Length(FText)) and FText[FPos].IsDigit then
        while (FPos <= Length(FText)) and FText[FPos].IsDigit do Inc(FPos)
      else
        FPos := Save;
    end;

    S := Copy(FText, Start, FPos - Start);
    Result.Kind := tkNumber;
    Result.Text := S;
    { Invariant settings: a rate law is source text, not user input, so its
      decimal point is always '.' whatever the machine's locale says. }
    if not TryStrToFloat(S, Result.Value, GInv) then
      raise ERateLawParseError.Create('Malformed number "' + S + '"', Start);
    Exit;
  end;

  if IsIdentStart(FText[FPos]) then
  begin
    Start := FPos;
    while (FPos <= Length(FText)) and IsIdentPart(FText[FPos]) do Inc(FPos);
    Result.Kind := tkIdent;
    Result.Text := Copy(FText, Start, FPos - Start);
    Exit;
  end;

  raise ERateLawParseError.Create(
    Format('Unexpected character "%s"', [FText[FPos]]), FPos);
end;

class function TRateLawLexer.Tokenize(const AText: string): TArray<TToken>;
var
  Lex: TRateLawLexer;
  T: TToken;
  N: Integer;
begin
  Lex := TRateLawLexer.Create(AText);
  try
    SetLength(Result, 16);
    N := 0;
    repeat
      T := Lex.Next;
      if N = Length(Result) then
        SetLength(Result, N * 2);
      Result[N] := T;
      Inc(N);
    until T.Kind = tkEnd;
    SetLength(Result, N);
  finally
    Lex.Free;
  end;
end;

{ ------------------------------------------------------------- TRateLawParser }

function TRateLawParser.Peek: TToken;
begin
  Result := FTokens[FIndex];
end;

function TRateLawParser.Take: TToken;
begin
  Result := FTokens[FIndex];
  if Result.Kind <> tkEnd then Inc(FIndex);
end;

function TRateLawParser.Accept(AKind: TTokenKind): Boolean;
begin
  Result := FTokens[FIndex].Kind = AKind;
  if Result then Take;
end;

procedure TRateLawParser.Expect(AKind: TTokenKind; const AWhat: string);
begin
  if not Accept(AKind) then
    raise ERateLawParseError.Create(
      Format('Expected %s', [AWhat]), Peek.Position);
end;

function TRateLawParser.Parse(const AText: string): TAstNode;
begin
  FSource := AText;
  if Trim(AText) = '' then
    raise ERateLawParseError.Create('Empty expression', 1);

  FTokens := TRateLawLexer.Tokenize(AText);
  FIndex  := 0;

  Result := ParseExpression;
  try
    if Peek.Kind <> tkEnd then
      raise ERateLawParseError.Create(
        Format('Unexpected "%s" after the end of the expression', [Peek.Text]),
        Peek.Position);
  except
    Result.Free;
    raise;
  end;
end;

function TRateLawParser.ParseExpression: TAstNode;
var
  Rhs: TAstNode;
  K: TTokenKind;
begin
  Result := ParseTerm;
  try
    while Peek.Kind in [tkPlus, tkMinus] do
    begin
      K := Take.Kind;
      Rhs := ParseTerm;
      if K = tkPlus then
        Result := TAstNode.Op(nkAdd, [Result, Rhs])
      else
        Result := TAstNode.Op(nkSub, [Result, Rhs]);
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TRateLawParser.ParseTerm: TAstNode;
var
  Rhs: TAstNode;
  K: TTokenKind;
begin
  Result := ParseUnary;
  try
    while Peek.Kind in [tkStar, tkSlash] do
    begin
      K := Take.Kind;
      Rhs := ParseUnary;
      if K = tkStar then
        Result := TAstNode.Op(nkMul, [Result, Rhs])
      else
        Result := TAstNode.Op(nkDiv, [Result, Rhs]);
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TRateLawParser.ParseUnary: TAstNode;
begin
  if Accept(tkPlus) then
    { Unary plus is not represented: it changes nothing, and keeping a node
      for it would make '+x' and 'x' different trees. }
    Exit(ParseUnary);

  if Accept(tkMinus) then
    Exit(TAstNode.Op(nkNeg, [ParseUnary]));

  Result := ParsePower;
end;

function TRateLawParser.ParsePower: TAstNode;
var
  Exponent: TAstNode;
begin
  Result := ParsePrimary;
  if Peek.Kind = tkCaret then
  begin
    Take;
    try
      { The exponent goes through ParseUnary, not ParsePower, so that 2^-3
        parses and 2^3^2 associates to the right. }
      Exponent := ParseUnary;
    except
      Result.Free;
      raise;
    end;
    Result := TAstNode.Op(nkPow, [Result, Exponent]);
  end;
end;

function TRateLawParser.ParsePrimary: TAstNode;
var
  T: TToken;
  Args: TArray<TAstNode>;
  I: Integer;
begin
  T := Peek;

  case T.Kind of
    tkNumber:
      begin
        Take;
        Exit(TAstNode.Num(T.Value));
      end;

    tkIdent:
      begin
        Take;
        if Peek.Kind <> tkLParen then
          Exit(TAstNode.Ident(T.Text));

        { A call. }
        Take;
        Args := nil;
        try
          if Peek.Kind <> tkRParen then
            repeat
              Args := Args + [ParseExpression];
            until not Accept(tkComma);
          Expect(tkRParen, '")" to close the call to ' + T.Text);
        except
          for I := 0 to High(Args) do Args[I].Free;
          raise;
        end;
        Exit(TAstNode.Call(T.Text, Args));
      end;

    tkLParen:
      begin
        Take;
        Result := ParseExpression;
        try
          Expect(tkRParen, '")"');
        except
          Result.Free;
          raise;
        end;
        Exit;
      end;

    tkEnd:
      raise ERateLawParseError.Create('Expression ends unexpectedly', T.Position);
  end;

  raise ERateLawParseError.Create(
    Format('Unexpected "%s"', [T.Text]), T.Position);
end;

{ ------------------------------------------------------------------ helpers }

function ParseRateLaw(const AText: string): TAstNode;
var
  P: TRateLawParser;
begin
  P := TRateLawParser.Create;
  try
    Result := P.Parse(AText);
  finally
    P.Free;
  end;
end;

function TryParseRateLaw(const AText: string; out ANode: TAstNode;
  out AError: string): Boolean;
begin
  ANode  := nil;
  AError := '';
  try
    ANode  := ParseRateLaw(AText);
    Result := True;
  except
    on E: ERateLawParseError do
    begin
      AError := Format('%s (at character %d)', [E.Message, E.Position]);
      Result := False;
    end;
    on E: Exception do
    begin
      AError := E.Message;
      Result := False;
    end;
  end;
end;

initialization
  GInv := TFormatSettings.Invariant;
  GInv.DecimalSeparator := '.';

end.
