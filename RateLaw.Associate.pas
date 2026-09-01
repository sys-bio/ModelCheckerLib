unit RateLaw.Associate;

{ Deciding which law a reaction is supposed to be following.

  Everything downstream trusts this. A wrong association does not produce no
  report -- it produces a confident, detailed, entirely spurious one, because
  the diff will faithfully describe every way the reaction differs from a law
  it was never meant to be. That is worse than saying nothing, so the rules
  here are deliberately reluctant.

  Three modes, in priority order.

  1. ANNOTATION. The modeller said so, and that is the end of it. The law is
     applied whatever the distance, because the whole value of an annotation
     is the case where the reaction does NOT resemble what it claims: "you
     meant Michaelis-Menten and wrote something else entirely" is a sentence
     inference can never produce. Inference can only say "this resembles
     nothing I know", which is silent about exactly the interesting case.

  2. INFERENCE, with a floor and a margin. A candidate must be close enough in
     absolute terms AND clearly closer than its nearest rival. Both conditions
     matter and they fail differently:

       no candidate under the floor   -> S001, nothing registered fits
       two candidates within margin   -> S002, and NOTHING is checked

     The second is the one worth being strict about. Two laws that fit almost
     equally well usually means a typo has left the expression equidistant
     between two correct forms, and picking the nearer by a hair reports the
     defect against the wrong law.

  3. NOTHING. Informational, never an error. A model may legitimately use a
     law nobody has registered, and a checker that calls that a failure gets
     switched off. }

interface

uses
  System.SysUtils, System.Classes, System.Math, System.Generics.Collections,
  RateLaw.Types;

type
  { One law that bound successfully, as a candidate for this reaction. AIndex
    refers back to the caller's own list, so the caller keeps ownership of the
    bind results and this unit stays free of them. }
  TAssocCandidate = record
    LawId:    string;
    Distance: Double;
    Score:    Double;
    Index:    Integer;
    { The law would not apply here even though it bound -- reported only when
      the modeller ASSERTED this law, since otherwise it is simply not a
      candidate and there is nothing to say. }
    Applies:  Boolean;
    Why:      string;
    { The expression uses exactly this law's symbols, the same number of
      times. Admits a candidate the distance alone would reject. }
    { 0 when the law expresses no opinion and the registry-wide floor
      applies. }
    Floor:       Double;
    SameSymbols: Boolean;
    { Weaker: every symbol used belongs to this law. }
    SymbolsSubset: Boolean;
    { How much of the expression this law claims to account for -- its number
      of roles. Used only to break a near-tie, and it is what stops a loose
      law from drawing with a tight one. }
    Specificity: Integer;
  end;

  TAssocOutcome = (aoNone,          // nothing registered fits
                   aoInferred,      // one clear winner
                   aoAmbiguous,     // two within the margin; check nothing
                   aoAnnotated,     // the modeller said so
                   aoAnnotatedBad); // said so, and the law does not apply here

  TAssocDecision = record
    Outcome: TAssocOutcome;
    Chosen:  Integer;         // index into the caller's list, or -1
    LawId:   string;
    Detail:  string;
    Rivals:  TArray<string>;  // for aoAmbiguous
  end;

const
  { How far a binding may sit from a law and still be called a match.

    Calibrated against measured distances, and re-calibrated twice as the
    measure improved -- a number picked for tidiness would have quietly
    stopped admitting real defects each time it changed.

    Under the tree-edit cost, measured:

      correct law                   0.000
      duplicated operand            0.125
      operator substitution         0.125
      the wrong one of two Hills    0.143  (right one: 0.071)
      a law that does not fit       0.9 and up

    The separation is now wide enough that the exact value matters little,
    which is the point: it is the measure that was wrong before, not the
    threshold. }
  AssociationFloor = 0.55;

  { How much closer the winner must be than the runner-up.

    Rescaled when the measure became a tree-edit cost. Distances collapsed --
    a duplicated operand went from 0.500 to 0.125 -- so the old margin of 0.10
    swallowed differences that are now decisive: Hill activation at 0.071
    against Hill repression at 0.143 is a clear win, and calling it a tie
    suppressed the finding entirely.

    At this scale a genuine tie is a near-exact one. Two laws of the same
    shape both sit at 0.000. }
  AssociationMargin = 0.05;

  { How well two laws must ACTUALLY fit before their tie is worth reporting.

    A tie says "these two are equally good and I will not guess between them",
    and S002 then tells the reader to annotate the reaction to settle it. That
    advice is only sound if one of them is right. Two laws that fit equally
    BADLY are not a coin-toss, they are both wrong, and asking the modeller to
    pick one is asking them to pick a law their reaction does not follow.

    "Vm/(Km + A^n)" is the case that showed it: a perfectly ordinary saturable
    form, matched to neither Hill law at distance 0.522 each, and reported as
    though annotating would resolve it. Beyond this ceiling the honest answer
    is that nothing registered matches.

    Set well above the founding duplicated-operand defect at 0.125, which must
    still associate and be reported, and well below the 0.522 that provoked
    this. }
  AmbiguityFitCeiling = 0.25;

{ AAnnotated is '' when the reaction carries no annotation. ACandidates need
  not be sorted. }
function DecideAssociation(const ACandidates: TArray<TAssocCandidate>;
                           const AAnnotated: string): TAssocDecision;

function AssocOutcomeName(AOutcome: TAssocOutcome): string;

implementation

function AssocOutcomeName(AOutcome: TAssocOutcome): string;
begin
  case AOutcome of
    aoInferred:     Result := 'inferred';
    aoAmbiguous:    Result := 'ambiguous';
    aoAnnotated:    Result := 'annotated';
    aoAnnotatedBad: Result := 'annotated but inapplicable';
  else              Result := 'none';
  end;
end;

{ The law's own ceiling where it declares one, the registry's otherwise. }
function FloorFor(const AC: TAssocCandidate): Double;
begin
  if AC.Floor > 0 then Result := AC.Floor else Result := AssociationFloor;
end;

{ How this reaction came to be matched with this law, in words.

  It replaces a bare "d=0.000, near". Both halves of that were jargon: "d" was
  never defined anywhere the reader could see, and "near" named the internal
  admission the candidate came through rather than telling them anything --
  worse, it said nothing at all on the common path, since a distance of 0.000
  is self-evidently near.

  What a reader actually needs is whether the SHAPE matched. Two of these
  three phrasings say it did; the third says it did not, and that the law was
  applied on shared vocabulary alone. That last case is the one worth
  noticing, because it is where a finding is most likely to be describing a
  law the modeller never had in mind. }
function FitPhrase(const AC: TAssocCandidate): string;
begin
  if AC.Distance <= 0 then
    Exit('an exact structural match');

  if AC.Distance <= FloorFor(AC) then
    Exit(Format('a close structural match, distance %.3f', [AC.Distance]));

  { Admitted despite the distance, because the expression is built from this
    law's symbols and no others. }
  if AC.SameSymbols then
    Exit(Format('the same symbols as this law but a different shape, '
              + 'distance %.3f', [AC.Distance]));

  Result := Format('distance %.3f', [AC.Distance]);
end;

function DecideAssociation(const ACandidates: TArray<TAssocCandidate>;
  const AAnnotated: string): TAssocDecision;
var
  I, BestI, SecondI: Integer;
  Sorted: TArray<TAssocCandidate>;
begin
  Result := Default(TAssocDecision);
  Result.Chosen := -1;

  { --- 1. the modeller said so ---------------------------------------- }
  if AAnnotated <> '' then
  begin
    for I := 0 to High(ACandidates) do
      if SameText(ACandidates[I].LawId, AAnnotated) then
      begin
        Result.Chosen := ACandidates[I].Index;
        Result.LawId  := ACandidates[I].LawId;
        if ACandidates[I].Applies then
        begin
          Result.Outcome := aoAnnotated;
          Result.Detail  := 'declared by annotation; '
                            + FitPhrase(ACandidates[I]);
        end
        else
        begin
          { Applied anyway. The mismatch between what was declared and what
            was written is the finding, and refusing to check would hide it. }
          Result.Outcome := aoAnnotatedBad;
          Result.Detail  := ACandidates[I].Why;
        end;
        Exit;
      end;

    { Named a law that is not registered, or is disabled, or could not bind
      here at all. Reported by the caller; there is nothing to check against. }
    Result.Outcome := aoAnnotatedBad;
    Result.LawId   := AAnnotated;
    Result.Detail  := 'the annotation names a law that is not available here';
    Exit;
  end;

  { --- 2. inference ---------------------------------------------------- }
  { Close enough, and ONLY close enough.

    Two further admissions used to stand here, both on the same reasoning:
    a damaged law can sit at maximum structural distance from the very law it
    is a defective copy of -- a misplaced parenthesis rearranges the whole
    tree while changing no symbol, a dropped term removes symbols altogether
    -- so sharing the law's vocabulary was taken as evidence enough to
    associate and report against it.

    The BioModels corpus refuted that. Measured over 1013 curated models,
    every association admitted on vocabulary rather than distance produced a
    finding, and since the corpus is curated every one of those findings was
    wrong:

        admission                 clean   reported
        near (d <= floor)         12101       1987     14%
        a subset of its symbols       0        659    100%
        same symbols, rearranged      0        116    100%

    Not "mostly wrong" -- wrong every time, 775 for 775. The reasoning was
    sound about what a damaged law looks like and silent about what an
    UNRELATED law looks like, and the two are indistinguishable by vocabulary
    alone: real models are full of expressions built from nothing but some
    law's symbols that are not that law at all.

    The SUBSET admission is therefore gone. It was the weaker of the two by
    far and did the bulk of the damage -- 659 of the 775 -- and it is easy to
    see why once the numbers are in front of you: a strict subset of a law's
    vocabulary is a very weak claim to be that law. Short expressions are a
    subset of almost everything.

    SAME SYMBOLS is kept, and it is a materially stronger statement: the
    expression's vocabulary is the law's exactly, nothing missing and nothing
    extra, differing only in arrangement. That is what a misplaced
    parenthesis leaves behind, it is the one defect class visible by no other
    means, and dropping it too costs the corpus case that founded the whole
    check ('mm-missing-parens': "Vm*S/Km + S", which no annotation declares).
    It is left in on those grounds and on the understanding that it is still
    the weakest admission here -- 116 findings over the corpus, none of them
    right -- so if it is ever tightened further, tighten this.

    What is NOT abandoned either way is the damaged-law case in general: it
    moves to the evidence that can carry it, the modeller's own annotation,
    which is checked at any distance in part 1 above and is the only thing
    that can say "you meant Michaelis-Menten and wrote something else
    entirely". }
  { A law that declares its own ceiling is declaring itself GREEDY, and the
    same-symbols admission is the greediest path there is -- it ignores
    distance entirely. Honouring the declaration on the distance branch and
    not on this one let catalytic mass action back in at d=0.889 and d=1.000
    on expressions built from its vocabulary and nothing else like it:
    "alpha1/(1 + V^3)" is Hill repression, and it was claimed and reported
    against as though it were k*V. 189 S010 findings came in that way.

    So a declared ceiling gates both. A law that declares none keeps the old
    behaviour, which is what mm-missing-parens depends on: a misplaced
    parenthesis sits at maximum distance from the law it is a copy of, and
    Michaelis-Menten declares no ceiling precisely because it has that defect
    class to catch. }
  Sorted := nil;
  for I := 0 to High(ACandidates) do
    if ACandidates[I].Applies and
       ((ACandidates[I].Distance <= FloorFor(ACandidates[I])) or
        (ACandidates[I].SameSymbols and (ACandidates[I].Floor <= 0))) then
      Sorted := Sorted + [ACandidates[I]];

  if Length(Sorted) = 0 then
  begin
    Result.Outcome := aoNone;
    Result.Detail  := 'no registered law matches';
    Exit;
  end;

  BestI := 0;
  for I := 1 to High(Sorted) do
    if Sorted[I].Score < Sorted[BestI].Score then BestI := I;

  SecondI := -1;
  for I := 0 to High(Sorted) do
    if I <> BestI then
      if (SecondI < 0) or (Sorted[I].Score < Sorted[SecondI].Score) then
        SecondI := I;

  if (SecondI >= 0) and
     (Sorted[SecondI].Score - Sorted[BestI].Score < AssociationMargin) then
  begin
    { A near-tie is broken by SPECIFICITY before it is called ambiguous.

      Mass action is the reason. Instantiated for one substrate it is k*S --
      two roles, and loose enough to sit near almost anything, so it draws
      with a tight law on every reaction that has a single reactant. Calling
      that a tie and checking nothing would suppress real findings on a whole
      class of ordinary models: Vm*S/(Km*S) is plainly defective Michaelis-
      Menten, and reporting only "could be either" helps nobody.

      A law with more roles accounts for more of the expression, so when two
      fit equally well the more specific one is the better explanation. Only
      when they are equally specific as well as equally close is the choice
      genuinely a coin-toss -- Hill activation against Hill repression, which
      differ by which power sits in the numerator and nothing else. }
    if Sorted[BestI].Specificity <> Sorted[SecondI].Specificity then
    begin
      if Sorted[SecondI].Specificity > Sorted[BestI].Specificity then
        BestI := SecondI;
      Result.Outcome := aoInferred;
      Result.Chosen  := Sorted[BestI].Index;
      Result.LawId   := Sorted[BestI].LawId;
      Result.Detail  := FitPhrase(Sorted[BestI])
        + ', and the more specific of two laws that fit equally well';
      Exit;
    end;

    { Equally poor is not a tie. Neither law describes this reaction, and
      saying so is more use than inviting the reader to choose between two
      that do not fit. }
    if Sorted[BestI].Distance > AmbiguityFitCeiling then
    begin
      Result.Outcome := aoNone;
      Result.Chosen  := -1;
      Result.LawId   := '';
      Result.Detail  := 'no registered law matches';
      Exit;
    end;

    { Deliberately checks NOTHING. Reporting against the nearer of two laws
      that fit equally well is how a defect gets described in terms of a law
      the modeller never had in mind. }
    Result.Outcome := aoAmbiguous;
    Result.Chosen  := -1;
    Result.LawId   := '';
    Result.Detail  := Format('%s and %s fit equally well '
      + '(distance %.3f and %.3f)',
      [Sorted[BestI].LawId, Sorted[SecondI].LawId,
       Sorted[BestI].Distance, Sorted[SecondI].Distance]);
    for I := 0 to High(Sorted) do
      if (Sorted[I].Score - Sorted[BestI].Score < AssociationMargin) and
         (Sorted[I].Specificity = Sorted[BestI].Specificity) then
        Result.Rivals := Result.Rivals + [Sorted[I].LawId];
    Exit;
  end;

  Result.Outcome := aoInferred;
  Result.Chosen  := Sorted[BestI].Index;
  Result.LawId   := Sorted[BestI].LawId;
  Result.Detail  := FitPhrase(Sorted[BestI]);
end;

end.
