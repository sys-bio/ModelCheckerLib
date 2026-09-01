unit RateLaw.Report;

{ Turning a check result into something a person reads.

  In the library rather than in Iridium, because the same report has to serve
  the console harness, the GUI, and any future batch tool -- and because a
  report assembled separately in each of them would drift, so that the same
  model described itself differently depending on what ran the check.

  Two rules shape the layout.

  WHAT WAS CHECKED COMES FIRST. A report that lists only failures cannot be
  told apart from a report of a check that never ran. "No findings" and
  "nothing was examined" look identical unless the report says which laws
  participated and what each reaction was matched to, so it says that before
  it says anything else.

  SEVERITY ORDERS, REACTIONS GROUP. A user fixing a model works reaction by
  reaction, so the findings for one reaction stay together; within a reaction
  the errors come before the warnings before the notes, because that is the
  order they will be dealt with in.

  There are two renderings, AsText and AsMarkdown, and they carry the SAME
  CONTENT IN THE SAME ORDER. Only the presentation differs. That is the whole
  of the discipline here: the moment one of them decides to show a little
  more, or to lead with the summary because it looks better rendered, the same
  model describes itself differently depending on what ran the check, which is
  the thing this unit exists to prevent. A change to one is a change to both.

  AsText is for the console harness, where aligned columns beat rendered
  prose. AsMarkdown is for the GUI's report panel. }

interface

uses
  System.SysUtils, System.Classes, System.Generics.Collections,
  System.Generics.Defaults,
  RateLaw.Types, RateLaw.Registry;

type
  TReportOptions = record
    { Include the INFO-level notes. Off makes the report shorter and hides
      "no registered law matches", which on a model full of unregistered
      kinetics is most of the output. }
    IncludeNotes: Boolean;
    { The per-reaction association lines. }
    IncludeAssociations: Boolean;
    { The behavioural checks were run, so the report can say so -- otherwise
      "no findings" overstates what was looked at. }
    DynamicWasRun: Boolean;
    class function Default: TReportOptions; static;
  end;

{ The whole report. ARegistry may be nil; it is used only to say how many
  laws were available. }
function AsText(AResult: TCheckResult; ARegistry: TRateLawRegistry;
                AReactionCount: Integer;
                const AOptions: TReportOptions): string; overload;
function AsText(AResult: TCheckResult; ARegistry: TRateLawRegistry;
                AReactionCount: Integer): string; overload;

{ The same report as markdown, for a viewer that renders it.

  Everything the model wrote -- rate laws, subexpressions, identifiers -- goes
  through MdCode, and it is not a nicety. A rate law is made of exactly the
  characters markdown reserves: "Vm*S/(Km + S)" has a pair of asterisks in it
  and renders as "VmS/(Km + S)" with "S/(Km + " in italics, which is a report
  that quietly lies about what the model says. }
function AsMarkdown(AResult: TCheckResult; ARegistry: TRateLawRegistry;
                    AReactionCount: Integer;
                    const AOptions: TReportOptions): string; overload;
function AsMarkdown(AResult: TCheckResult; ARegistry: TRateLawRegistry;
                    AReactionCount: Integer): string; overload;

{ One line summarising the outcome, for a status bar or a caption. }
function AsSummary(AResult: TCheckResult): string;

implementation

class function TReportOptions.Default: TReportOptions;
begin
  Result.IncludeNotes        := True;
  Result.IncludeAssociations := True;
  Result.DynamicWasRun       := False;
end;

const
  { The association detail quotes a distance, and a bare number carries no
    scale. Stated once per report rather than per row, and identically in both
    renderings. }
  DistanceLegend =
    'Distance is how far a reaction''s expression sits from the law it was '
  + 'matched to: 0.000 is an identical shape, 1.000 nothing in common.';

{ True when at least one association actually quotes a distance -- an exact
  match does not, so a report of nothing but exact matches would otherwise
  explain a number it never shows. }
function MentionsDistance(AResult: TCheckResult): Boolean;
var
  A: TAssociation;
begin
  for A in AResult.Associations do
    if (A.LawId <> '') and (Pos('distance', A.Detail) > 0) then Exit(True);
  Result := False;
end;

function SeverityRank(ASeverity: TSeverity): Integer;
begin
  { Errors first. A user works down a report, and the things that stop the
    model being right belong at the top of it. }
  case ASeverity of
    sevError: Result := 0;
    sevWarn:  Result := 1;
  else        Result := 2;
  end;
end;

function AsSummary(AResult: TCheckResult): string;
var
  E, W: Integer;
begin
  if AResult = nil then Exit('The check did not run.');
  E := AResult.ErrorCount;
  W := AResult.WarningCount;
  if (E = 0) and (W = 0) then Exit('No problems found.');

  Result := '';
  if E > 0 then
    if E = 1 then Result := '1 error' else Result := Format('%d errors', [E]);
  if W > 0 then
  begin
    if Result <> '' then Result := Result + ', ';
    if W = 1 then Result := Result + '1 warning'
    else Result := Result + Format('%d warnings', [W]);
  end;
  Result := Result + '.';
end;

function AsText(AResult: TCheckResult; ARegistry: TRateLawRegistry;
  AReactionCount: Integer; const AOptions: TReportOptions): string;
var
  SB: TStringBuilder;
  Sorted: TArray<TRateLawDiagnostic>;
  D: TRateLawDiagnostic;
  A: TAssociation;
  I, Shown, Suppressed: Integer;
  LastRx: string;
  Head: string;
  ShowsDistance: Boolean;
begin
  SB := TStringBuilder.Create;
  try
    SB.AppendLine('Rate law check');
    SB.AppendLine('==============');
    SB.AppendLine;

    if AResult = nil then
    begin
      SB.AppendLine('The check did not run.');
      Exit(SB.ToString);
    end;

    { --- what was checked ------------------------------------------- }
    Head := Format('%d reaction(s)', [AReactionCount]);
    if ARegistry <> nil then
      Head := Head + Format(' against %d rate law(s)', [ARegistry.ActiveCount]);
    if AOptions.DynamicWasRun then
      Head := Head + ', structure and behaviour'
    else
      Head := Head + ', structure only';
    SB.AppendLine(Head + '.');
    SB.AppendLine;

    ShowsDistance := MentionsDistance(AResult);
    if AOptions.IncludeAssociations and (AResult.Associations.Count > 0) then
    begin
      for A in AResult.Associations do
        if A.LawId = '' then
          SB.AppendFormat('  %-16s  --', [A.ReactionId]).AppendLine
        else
          SB.AppendFormat('  %-16s  %s   (%s)',
            [A.ReactionId, A.LawId, A.Detail]).AppendLine;
      { Said once, here, rather than on every row: the number is meaningless
        without its scale, and the scale is the same for all of them. }
      if ShowsDistance then
      begin
        SB.AppendLine;
        SB.AppendLine('  ' + DistanceLegend);
      end;
      SB.AppendLine;
    end;

    { --- the findings ------------------------------------------------ }
    Sorted := AResult.Diagnostics.ToArray;
    TArray.Sort<TRateLawDiagnostic>(Sorted,
      TComparer<TRateLawDiagnostic>.Construct(
        function(const X, Y: TRateLawDiagnostic): Integer
        begin
          { Reaction, then severity, then code -- so one reaction's findings
            stay together and read worst-first inside that. }
          Result := CompareStr(X.ReactionId, Y.ReactionId);
          if Result <> 0 then Exit;
          Result := SeverityRank(X.Severity) - SeverityRank(Y.Severity);
          if Result <> 0 then Exit;
          Result := CompareStr(X.Code, Y.Code);
        end));

    Shown := 0;
    Suppressed := 0;
    LastRx := #1;
    for I := 0 to High(Sorted) do
    begin
      D := Sorted[I];
      if (D.Severity = sevInfo) and not AOptions.IncludeNotes then
      begin
        Inc(Suppressed);
        Continue;
      end;

      if D.ReactionId <> LastRx then
      begin
        SB.AppendLine;
        if D.SourceLine > 0 then
          SB.AppendFormat('%s  (line %d)',
                          [D.ReactionId, D.SourceLine]).AppendLine
        else if D.ReactionId <> '' then
          SB.AppendLine(D.ReactionId)
        else
          SB.AppendLine('(model)');
        LastRx := D.ReactionId;
      end;

      SB.Append('  ').AppendLine(D.ToString);
      Inc(Shown);
    end;

    SB.AppendLine;
    if Shown = 0 then
      SB.AppendLine('No problems found.')
    else
      SB.AppendLine(AsSummary(AResult));

    if Suppressed > 0 then
      SB.AppendFormat('%d note(s) hidden.', [Suppressed]).AppendLine;

    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

function AsText(AResult: TCheckResult; ARegistry: TRateLawRegistry;
  AReactionCount: Integer): string;
begin
  Result := AsText(AResult, ARegistry, AReactionCount,
                   TReportOptions.Default);
end;

{ ------------------------------------------------------------- markdown }

{ Model text as a code span, fenced with enough backticks to survive whatever
  is inside it. Antimony cannot produce a backtick today, but a report that
  breaks its own formatting on one character of input is not worth the saving
  of not checking. }
function MdCode(const AText: string): string;
var
  Run, Longest, I: Integer;
  Fence, Pad: string;
begin
  if AText = '' then Exit('');

  Longest := 0;
  Run     := 0;
  for I := 1 to Length(AText) do
    if AText[I] = '`' then
    begin
      Inc(Run);
      if Run > Longest then Longest := Run;
    end
    else
      Run := 0;

  Fence := StringOfChar('`', Longest + 1);
  { A span that starts or ends with a backtick needs padding spaces, which
    the renderer strips again. }
  if (AText[1] = '`') or (AText[Length(AText)] = '`') then Pad := ' '
  else Pad := '';
  Result := Fence + Pad + AText + Pad + Fence;
end;

{ Prose that came from the engine, made safe to render. Diagnostic messages
  quote model identifiers inline ("Km_1" plays the Km role), and an
  identifier with an underscore in it is ordinary in biology and italic in
  markdown. }
function MdText(const AText: string): string;
const
  { The inline set only. Escaping every character markdown has ever reserved
    turns "2 reaction(s), d=0.000" into "2 reaction\(s\), d=0\.000" -- and the
    backslashes SHOW, because a renderer strips an escape only where it was
    meaningful. Parentheses matter inside a link, a full stop after a leading
    digit, a hyphen at the start of a line; none of those arise in a
    diagnostic message, and escaping them just litters the page. }
  Reserved = ['\', '`', '*', '_', '[', ']', '<', '>', '|', '#'];
var
  I: Integer;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create;
  try
    for I := 1 to Length(AText) do
    begin
      if CharInSet(AText[I], Reserved) then SB.Append('\');
      SB.Append(AText[I]);
    end;
    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

{ A table cell must also not contain a raw newline. }
function MdCell(const AText: string): string;
begin
  Result := MdText(AText);
  Result := StringReplace(Result, #13#10, ' ', [rfReplaceAll]);
  Result := StringReplace(Result, #10, ' ', [rfReplaceAll]);
  Result := StringReplace(Result, #13, ' ', [rfReplaceAll]);
end;

function MdCodeCell(const AText: string): string;
begin
  { Inside a table a pipe ends the cell even within a code span, so it is the
    one character that still has to be escaped there. }
  Result := MdCode(StringReplace(AText, '|', '\|', [rfReplaceAll]));
end;

function AsMarkdown(AResult: TCheckResult; ARegistry: TRateLawRegistry;
  AReactionCount: Integer; const AOptions: TReportOptions): string;
var
  SB: TStringBuilder;
  Sorted: TArray<TRateLawDiagnostic>;
  D: TRateLawDiagnostic;
  A: TAssociation;
  I, Shown, Suppressed: Integer;
  LastRx, Head: string;
  ShowsDistance: Boolean;

  procedure Detail(const ALabel, AValue: string);
  begin
    if AValue = '' then Exit;
    SB.AppendFormat('- %s: %s', [ALabel, MdCode(AValue)]).AppendLine;
  end;

begin
  SB := TStringBuilder.Create;
  try
    SB.AppendLine('# Rate law check');
    SB.AppendLine;

    if AResult = nil then
    begin
      SB.AppendLine('The check did not run.');
      Exit(SB.ToString);
    end;

    { --- what was checked ------------------------------------------- }
    Head := Format('%d reaction(s)', [AReactionCount]);
    if ARegistry <> nil then
      Head := Head + Format(' against %d rate law(s)', [ARegistry.ActiveCount]);
    if AOptions.DynamicWasRun then
      Head := Head + ', structure and behaviour'
    else
      Head := Head + ', structure only';
    SB.AppendLine(MdText(Head) + '.');
    SB.AppendLine;

    ShowsDistance := MentionsDistance(AResult);
    if AOptions.IncludeAssociations and (AResult.Associations.Count > 0) then
    begin
      SB.AppendLine('## What was matched');
      SB.AppendLine;
      SB.AppendLine('| Reaction | Rate law | Why |');
      SB.AppendLine('| :--- | :--- | :--- |');
      for A in AResult.Associations do
        if A.LawId = '' then
          SB.AppendFormat('| %s | *none* | %s |',
            [MdCell(A.ReactionId), MdCell(A.Detail)]).AppendLine
        else
          SB.AppendFormat('| %s | %s | %s |',
            [MdCell(A.ReactionId), MdCodeCell(A.LawId),
             MdCell(A.Detail)]).AppendLine;
      SB.AppendLine;
      if ShowsDistance then
      begin
        SB.AppendLine(MdText(DistanceLegend));
        SB.AppendLine;
      end;
    end;

    { --- the findings ------------------------------------------------ }
    Sorted := AResult.Diagnostics.ToArray;
    TArray.Sort<TRateLawDiagnostic>(Sorted,
      TComparer<TRateLawDiagnostic>.Construct(
        function(const X, Y: TRateLawDiagnostic): Integer
        begin
          Result := CompareStr(X.ReactionId, Y.ReactionId);
          if Result <> 0 then Exit;
          Result := SeverityRank(X.Severity) - SeverityRank(Y.Severity);
          if Result <> 0 then Exit;
          Result := CompareStr(X.Code, Y.Code);
        end));

    Shown      := 0;
    Suppressed := 0;
    LastRx     := #1;
    for I := 0 to High(Sorted) do
    begin
      D := Sorted[I];
      if (D.Severity = sevInfo) and not AOptions.IncludeNotes then
      begin
        Inc(Suppressed);
        Continue;
      end;

      if Shown = 0 then
      begin
        SB.AppendLine('## Findings');
        SB.AppendLine;
      end;

      if D.ReactionId <> LastRx then
      begin
        if D.ReactionId = '' then
          SB.AppendLine('### (model)')
        else if D.SourceLine > 0 then
          SB.AppendFormat('### %s (line %d)',
                          [MdText(D.ReactionId), D.SourceLine]).AppendLine
        else
          SB.AppendLine('### ' + MdText(D.ReactionId));
        SB.AppendLine;
        LastRx := D.ReactionId;
      end;

      { The code and severity lead, in bold, so a reader scanning a rendered
        page finds the errors without reading the prose. }
      if D.LawId <> '' then
        SB.AppendFormat('**%s %s** (checked against %s)',
          [MdText(D.Code), MdText(SeverityName(D.Severity)),
           MdCode(D.LawId)]).AppendLine
      else
        SB.AppendFormat('**%s %s**',
          [MdText(D.Code), MdText(SeverityName(D.Severity))]).AppendLine;
      SB.AppendLine;
      SB.AppendLine(MdText(D.Message));
      SB.AppendLine;

      Detail('found', D.Found);
      Detail('expected', D.Expected);
      Detail('suggestion', D.Suggestion);
      Detail('seen at', D.Evidence);
      if (D.Found <> '') or (D.Expected <> '') or
         (D.Suggestion <> '') or (D.Evidence <> '') then
        SB.AppendLine;

      Inc(Shown);
    end;

    if Shown = 0 then
      SB.AppendLine('**No problems found.**')
    else
      SB.AppendLine('**' + MdText(AsSummary(AResult)) + '**');

    if Suppressed > 0 then
    begin
      SB.AppendLine;
      SB.AppendLine(MdText(Format('%d note(s) hidden.', [Suppressed])));
    end;

    Result := SB.ToString;
  finally
    SB.Free;
  end;
end;

function AsMarkdown(AResult: TCheckResult; ARegistry: TRateLawRegistry;
  AReactionCount: Integer): string;
begin
  Result := AsMarkdown(AResult, ARegistry, AReactionCount,
                       TReportOptions.Default);
end;

end.
