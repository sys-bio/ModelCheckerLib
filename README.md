# ModelCheckerLib

**A static and behavioural checker for the equations inside a systems-biology model.**
Written in Delphi, RTL-only, with no GUI and no native dependencies.

A model can parse, load and simulate perfectly while computing the wrong thing. The founding
case of this project is a rate law written

```
Vm * S / (Km + Km)
```

— a Michaelis–Menten form with `S` mistyped as `Km` in the denominator. It is valid Antimony,
valid SBML, and it simulates. It is also not Michaelis–Menten, and nothing in the usual
toolchain will say so. This library says so.

Rate laws are the first thing it checks and currently the only one; the library is named for
what it is becoming rather than what it covers today.

> **Authoring a rate law is documented separately.** `RATE_LAW_MANUAL.md` in this folder is
> the user manual — the JSON schema, the invariant types, worked examples, and what each
> rejection code means. This README is the *developer* manual: how the engine works inside,
> and what you must not break while changing it. If you only want to add a law, you want the
> manual, not this file.

---

## The one idea

**The set of laws checked is data, not code.** A law is a registry entry giving a canonical
expression, the roles of its symbols, and the behavioural invariants it guarantees. Every
defect class is stated in terms of *tree shape*, never in terms of a particular law.

This has a falsification test, and it is meant seriously:

> If a defect class ever has to ask **which** law it is looking at, that is a failure of the
> design. If a new law cannot be added without an engine change, that is a defect in the
> engine — record it as one rather than quietly absorbing it.

It has been falsified at least once already, and the record is instructive. The generative
instantiator used to build "the one scalar parameter × the product of the reactants" directly,
which made *reversible* mass action — one of the commonest rate laws there is — not merely
unregistered but inexpressible. That was logged as an engine defect and the instantiator was
made template-driven. Nothing in `RateLaw.Generative` now knows what mass action looks like.

---

## Quick start

The library sees a model only through `IModelSource`. Implement that over whatever you have,
then hand it to `CheckModel`:

```pascal
uses
  RateLaw.Types, RateLaw.Registry, RateLaw.Static, RateLaw.Report;

var
  Reg:   TRateLawRegistry;
  Res:   TCheckResult;
  Model: IModelSource;   // your adapter
begin
  Reg := TRateLawRegistry.Create;
  try
    Reg.LoadDefaults(UserLawDir, ProjectLawDir);   // built-ins, then user, then project

    Res := CheckModel(Reg, Model, {ADynamic:=} False);
    try
      Writeln(AsText(Res, Reg, Model.ReactionCount));
      if Res.ErrorCount > 0 then ExitCode := 1;
    finally
      Res.Free;
    end;
  finally
    Reg.Free;
  end;
end;
```

`ADynamic` turns on the behavioural half. It is off by default because it is orders of
magnitude more work — thousands of evaluations per reaction per law — and a caller checking
while the user types wants neither the cost nor the extra findings.

---

## Architecture

```
  model text ──► Parser ──► Ast ──► Canonical ─┐
                             │                 │
       registry JSON ──► Registry ──► Generative
                                  │            │
                                  ▼            ▼
                              Associate ──► Bind ──► Diff
                                                      │
                                          ┌───────────┴───────────┐
                                       Static                  Dynamic
                                     (structure)              (behaviour)
                                          └───────────┬───────────┘
                                                   Report
```

| Unit | Role |
|---|---|
| `RateLaw.Types` | `IModelSource`, diagnostics, `TCheckResult`. The vocabulary everything else speaks. |
| `RateLaw.Ast` | The expression tree, and its two printers — readable infix, and the canonical signature. |
| `RateLaw.Parser` | One infix parser, used for *both* the model's rate law and the registry's expression. |
| `RateLaw.Canonical` | Normalisation. Returns a new tree; never mutates its input. |
| `RateLaw.Registry` | Law storage, three layers, self-validating at load. |
| `RateLaw.BuiltInLaws` | The laws that ship compiled in, as JSON string constants. |
| `RateLaw.Generative` | Instantiates a *family* law (mass action of arbitrary order) for one reaction. |
| `RateLaw.Diff` | Structural difference between two trees, and its cost. |
| `RateLaw.Associate` | Decides which law a reaction is supposed to be following. |
| `RateLaw.Bind` | Decides which model identifier plays which role. |
| `RateLaw.Static` | Structural comparison and defect classification. |
| `RateLaw.Eval` | Total numeric evaluation of a tree — never raises. |
| `RateLaw.Dynamic` | Behavioural checking against declared invariants. |
| `RateLaw.Report` | `AsText` and `AsMarkdown`, same content, same order. |
| `RateLaw.TestCorpus` | Fixture `IModelSource` built from literal data, plus the corpus. |
| `RateLaw.Mutate` | Programmatic mutation of a correct law, for coverage measurement. |
| `RateLaw.HardLaws` | Laws complex enough to be a real test, loaded as a user layer. |

### RTL-only, and why it matters

Nothing here may reference FMX, libantimony or libRoadRunner. That single constraint is what
lets the engine be driven by a GUI, by this project's console harness, and later by a
bifurcation tool or a batch checker — and it is why the corpus runs with no DLL and no GUI.
`IModelSource` is the whole of the boundary.

It is also why the evaluator is ours rather than the simulator's. Probing one invariant means
sampling a law over a grid — 64 × 6 × 6 is 2304 evaluations for *one* reaction against *one*
law. Driving that through a live engine would mutate the user's loaded model thousands of
times per check, and would make behavioural checking unavailable on a model that does not
simulate — which is exactly the model a checker is most needed for.

---

## The model boundary

```pascal
IModelSource = interface
  function ReactionCount: Integer;
  function ReactionId   (AIndex: Integer): string;
  function RateLawText  (AIndex: Integer): string;
  function Reactants    (AIndex: Integer): TSpeciesRefs;
  function Products     (AIndex: Integer): TSpeciesRefs;
  function Modifiers    (AIndex: Integer): TModifierRefs;

  function SymbolKind    (const AName: string): TSymbolKind;
  function HasValue      (const AName: string): Boolean;
  function ValueOf       (const AName: string): Double;
  function AssignmentRule(const AName: string): string;
  ...
```

Three rules for an implementation:

**Never raise.** A malformed model is precisely the case this library exists for, so refusing
to describe a broken model defeats the purpose. An out-of-range index returns empty; an
unanswerable question reports "I cannot say".

**Distinguish "unknown" from "cannot say".** `skUnknown` covers both *the model has never heard
of this name* (defect `S014`) and *the source could not tell you* (a check that could not be
performed). Conflating them invents findings. `KnowsSymbolKinds` settles it once rather than
at every call site.

**Snapshot; do not query lazily.** If your backing library has one current model per process —
libantimony does — an adapter that calls through on each method answers about whatever was
loaded most recently, not the model you were given. Load, copy everything out, release, and
never touch the library again. Iridium's `uRateLawModelSource.pas` is the worked example.

Stoichiometry is carried twice on purpose: `Value` is NaN when a model writes a stoichiometry
as a symbol (`S1 + n S2 => S3`), and `Text` holds the symbol's name. Generative laws
instantiate their exponents from this, so dropping the symbolic form would silently turn `n`
into "not a number".

---

## The pipeline, in order

### 1. Associate — which law is this reaction meant to follow?

Everything downstream trusts this, and a wrong association does not produce *no* report: it
produces a confident, detailed, entirely spurious one. So the rules are deliberately reluctant.

| Mode | Behaviour |
|---|---|
| **Annotation** | The modeller said so. Applied whatever the distance — the whole value of an annotation is the case where the reaction does *not* resemble what it claims. |
| **Inference** | Needs a candidate under the floor **and** clearly closer than its nearest rival. No candidate → `S001`. Two within margin → `S002`, and **nothing is checked**. |
| **Nothing** | Informational, never an error. A model may legitimately use a law nobody registered, and a checker that calls that a failure gets switched off. |

A law may declare its own `association_floor`. Looseness is a property of the law, not of the
registry: "k times some species" sits near a great deal, so the catalytic entries declare a
tight ceiling and claim only near-exact matches.

### 2. Bind — which identifier plays which role?

Two sources of evidence, not equally trustworthy:

- **Species roles bind from reaction structure.** A substrate role binds to a reactant, an
  inhibitor role to a declared inhibitor. The modeller stated it; it is not negotiable.
- **Parameter roles bind from shape, then names.** Every permutation is scored by how well the
  resulting expression matches the law, and **the name only breaks ties**.

That ordering is the whole design. Binding `Km` to the `Km` role first cannot detect a
transposition, because that binding is exactly what undoes it. A binding whose best fit
required an unnatural name assignment is *recorded* — it is stronger evidence of a role swap
than the structural difference it produces.

### 3. Diff and classify

One measure, shared by the binder and the static engine. This matters: association and
classification used to answer the same question with two different measures — an approximate
Dice coefficient chose the law, an exact diff explained it — and they disagreed. A bag of parts
cannot tell `Vm*S^n/(K^n + K^n)` from Hill repression, which contains the same parts
rearranged. Now the distance *is* the cost of the diff that will be performed, so the law
chosen is by construction the law with least to explain.

Classification is a local question about the node that differs:

| Shape | Defect |
|---|---|
| same operands, different operator | substitution (`S003`) |
| different operands | regrouping (`S010`) |
| an operand repeated among siblings | duplication (`S004`) |

### 4. Two trees, always

Both the pre- and post-canonical trees are kept, and neither is redundant. A misplaced
parenthesis is visible **only before** normalising — normalising is precisely what erases it. A
duplicated operand is visible **only after**.

The pre-canonical pass runs *only* when the canonical pass finds nothing to say. It must not
run otherwise: every commutative reordering (`S*Vm` where the law says `Vm*S`) is a
pre-canonical difference and no defect at all, and a checker that reports those is unusable on
correct models.

---

## Canonicalisation: what it deliberately does *not* do

`Canonicalise` normalises **writing**, not algebra. Flattening, `a-b → a+(-1)*b`,
`a/b → a*b^-1`, constant folding, sorting commutative operands, collecting equal bases.

Two rules are refused, and both refusals are load-bearing:

- **Like terms in a sum are not collected.** `Km + Km` stays a sum of two identical operands
  rather than becoming `2*Km`. That is the founding defect of the project, and leaving the
  duplication literally visible is what lets the engine name it as a duplicated operand rather
  than as "a coefficient where none was expected". The cost — `x + x` and `2*x` do not compare
  equal — is accepted knowingly.
- **Products are not distributed over sums.** `(x+y)*z` stays as written. Distribution would
  let a genuine parenthesisation error normalise into the correct form and disappear.

Powers *are* collected. The asymmetry between sums and products is the point, not an oversight.

Every rule you might add trades a false positive for stylistic variation against a false
negative for a real defect. Make that trade consciously.

---

## The registry

Three layers, later overriding earlier **by id**:

1. **Built-in** — compiled in (`RateLaw.BuiltInLaws`), so a fresh install works with no files
   on disk at all. Nothing to install, nothing to lose, nothing to get out of step with the binary.
2. **User** — a directory of `.json` files.
3. **Project** — a directory beside the model, so a model repository can carry its own law set
   in version control.

A built-in is never deleted, only disabled or shadowed, which is what makes a bad edit
recoverable by deleting one file.

**Every entry is validated as it loads, and an invalid entry does not participate.** This is
not tidiness: a bad entry produces false positives on *every* model checked afterwards, and the
user has no way to tell the tool is wrong rather than their model. Load time is the only point
at which the blame is still legible. Structural validation lives in `RateLaw.Registry`;
checking that a law's expression actually satisfies its own declared invariants needs the
evaluator, so `RateLaw.Dynamic` installs itself via `SetInvariantValidator`. A generative entry
is exempt from the second half — a shape cannot be evaluated until a reaction instantiates it.

Storage is JSON rather than the YAML the original spec proposed: there is no YAML parser in the
Delphi RTL. Field names are kept exactly as the YAML draft had them, so the two stay
mechanically interconvertible.

---

## Diagnostics

Three code families:

| Prefix | Meaning | Emitted by |
|---|---|---|
| `S###` | Static — structure, association, symbols | `RateLaw.Static`, `RateLaw.Associate` |
| `D###` | Dynamic — behavioural invariant violations | `RateLaw.Dynamic` |
| `R###` | Registry — a law was rejected at load | `RateLaw.Registry` |

**Every dynamic finding carries a witness** — the actual parameter and concentration values at
which the property broke. A dynamic finding without one cannot be told apart from a bug in the
checker, and the user cannot reproduce it. The witness is built into the reporting path rather
than added where convenient.

`TCheckResult` carries `Diagnostics`, `Associations` **and** `LawsApplied`. That last one is
not decoration: an empty report with an empty `LawsApplied` means the registry was empty or
everything was disabled — a very different report from a clean model. *"Nothing was checked"
and "nothing was wrong" must never look alike.*

`RateLaw.Report` offers `AsText` (console, aligned columns), `AsMarkdown` (GUI panel) and
`AsSummary` (one line, for a status bar). The first two carry the **same content in the same
order** — a change to one is a change to both, because the moment one shows a little more, the
same model describes itself differently depending on what ran the check.

In `AsMarkdown`, everything the model wrote goes through `MdCode`, and that is not a nicety: a
rate law is made of exactly the characters markdown reserves. `Vm*S/(Km + S)` renders as
`VmS/(Km + S)` with part of it in italics — a report that quietly lies about what the model says.

---

## Invariants you must not break

Hard-won, each from a real regression:

1. **Names bind last, not first.** (See Bind, above.)
2. **Keep both trees.** Pre- and post-canonical; neither is redundant.
3. **Don't collect like terms; don't distribute.**
4. **A correct model reporting anything is worse than a defect being missed.** That is the
   failure that gets a checker switched off.
5. **Don't normalise a lumped rate constant.** `IXa*VIIIa/r26_c` is mass action with
   `k = 1/r26_c`, and collapsing constant factors so a role can bind to it was implemented and
   removed — it hides the defects that consist of matching the wrong law. Three variants were
   tried; the worst took mutation detection from 57 to 35.
6. **`Signature` must be a total order independent of hash iteration order.** Otherwise two
   runs over the same model build different trees and the diff is unstable.
7. **Evaluation is total.** `RateLaw.Eval` never raises. Unknown symbol, division by zero,
   negative base under a fractional power, overflow — all come back as a *status*, because
   those failures are findings rather than accidents. A check whose purpose is to discover that
   a rate law blows up cannot itself blow up.
8. **Four things every SBML model contains** were each, at some point, treated as an ordinary
   identifier and bound to a kinetic role: the compartment volume factor, `EmptySet`,
   `time`/`pi`, and a clamped species. Before adding a check, ask what it does with those four.
9. **Modifiers must be inferred, not trusted.** Antimony records a modifier only where the
   modeller drew an interaction arrow, and `sbmlToAntimony` does not create arrows from SBML's
   `listOfModifiers` — so real models mostly declare none. Use `EffectiveModifiers` in
   `RateLaw.Generative`, which infers them. It lives in the engine rather than in a host's
   adapter on purpose: in the adapter, fixtures and real models would behave differently.

---

## Building and testing

Delphi 13 / RAD Studio 37.0. From this folder, after sourcing `rsvars.bat`:

```
dcc64 -B -NUdcu ModelCheckerLib_Project.dpr
```

**`-NUdcu` is not optional.** Without it `dcc64` writes its DCUs beside the sources, and that
directory is on the unit search path of hosts that consume this library as source — so the next
host build finds compiled units there and uses them instead of recompiling the `.pas`. The
symptom is an IDE that silently ignores your changes: edit a law, rebuild, and yesterday's
registry is still what runs. If that happens, delete `*.dcu` here and in the host's DCU output,
then rebuild.

### The harness

```
ModelCheckerLib_Project              the whole suite
ModelCheckerLib_Project -coverage    the mutation matrix, per law
ModelCheckerLib_Project -laws        every registered law and whether it validates
ModelCheckerLib_Project -registry    registry loading and layering
ModelCheckerLib_Project -list        the model corpus and why each case exists
ModelCheckerLib_Project -show NAME   render one case through IModelSource
ModelCheckerLib_Project -check NAME  one corpus case, in full
ModelCheckerLib_Project -bind NAME   which law each candidate binds to, and how far off
ModelCheckerLib_Project -canon       canonicalisation pairs only
ModelCheckerLib_Project -expr EXPR   parse one expression, dump both trees
ModelCheckerLib_Project -stress      stress cases
```

Cases compare diagnostic **codes**, not message text, so wording can keep improving without
breaking tests. Extra codes not listed fail the case, so a rule cannot quietly gain a
diagnostic without someone noticing.

### Mutation coverage

`-coverage` takes each law's own canonical expression, breaks it in a known way, and asks
whether the engine names the break correctly. **The mutation kind *is* the expected defect
class**, which makes the measurement objective — nobody gets to decide after the fact that
whatever came out was close enough. The mutations are the ones a person makes: a slipped
operator, a copied-and-not-edited operand, a parenthesis in the wrong place, two identifiers
transposed, an exponent left off.

### Do not read the synthetic corpus as evidence of readiness

It stayed green through a series of fixes that made the *real* numbers worse. Its cases are
expressions written as laws; real models are SBML, and the two disagree about what a rate law
looks like. Re-run the corpus after any engine change, but measure on real models before
believing anything.

Iridium ships `CheckAntFile.dpr`, a console tool that runs this engine over `.ant` and `.xml`
files and over the 1013-model curated BioModels corpus. That is where the false-positive rate
is actually measured.

---

## Extending

| You want to… | Do this |
|---|---|
| Add a rate law | Write a JSON entry. **See `RATE_LAW_MANUAL.md`** — no engine change should be needed, and if one is, that is a defect worth recording. |
| Add a behavioural invariant type | Implement it once, generically, in `RateLaw.Dynamic`. It must read its claim from the registry and know nothing about any particular law. |
| Add a structural defect class | State it in terms of tree shape in `RateLaw.Static`. If it needs to know which law it is looking at, stop — see *The one idea*. |
| Support a new model backend | Implement `IModelSource`. Snapshot; never raise; distinguish unknown from cannot-say. |
| Check something other than rate laws | New unit prefix — see below. |

### Naming

The folder is `ModelCheckerLib`, the units are `RateLaw.*`, and that is deliberate rather than
a missed rename. The library is named for what it will become; the units are named for what
they check. `RateLaw.*.pas` checks rate laws, so that is what it is called, and it keeps that
name. Checks of other kinds get their own prefix — `Model.*` — as they arrive. Do not flatten
`RateLaw.*` into `ModelChecker.*` for consistency with the folder: the prefix names the subject
of the check, the folder names the library.

---

## Status and known limits

- **18 laws ship built in**, all self-validating; the suite reports **53/53 model cases** and
  every correct form left clean.
- Mutation coverage: **69/83 detected at all, 57/83 classified exactly right**.
- **Mutation detection is 57/62 rather than 61/61 on purpose.** The subset
  admission that caught a dropped term by inference is gone: it accused a correct model every
  single time it fired — 659 findings, none right. The case still fires when the reaction is
  annotated. **Do not restore it to make the number go back up.**
- Most remaining misses are `S002` between laws differing in one place, where refusing to guess
  is the right answer. The exact-classification rate will keep falling as laws are added, and
  that is expected.
- Open: a defect-code reference and a worked walkthrough; Layer 3 simulation checks
  (`D101`–`D106`, partially landed); and the association-floor question — no global threshold
  separates the two largest remaining static codes from the founding defect.

The full status table, measured figures, and — more usefully — the deviations and findings,
including every place the design had to give, live in `specification_rate_law_checker_iridium.md`
in the Iridium repository. Read its §18 before changing engine behaviour.

---

## See also

- `RATE_LAW_MANUAL.md` — the user manual: authoring laws, the schema, the invariant types.
- `specification_rate_law_checker.md` — the general specification.
- `specification_rate_law_checker_iridium.md` — the Iridium-specific specification, milestones,
  and §18's findings and deviations.
