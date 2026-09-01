unit RateLaw.BuiltInLaws;

{ The laws that ship compiled in.

  A fresh install must be useful with no files on disk at all -- that is the
  whole reason these are string constants rather than a shipped directory.
  Nothing to install, nothing to lose, nothing to get out of step with the
  binary. The pattern is Iridium's own uBuiltInModels.

  A built-in can be disabled, or shadowed by a user entry with the same id,
  but never deleted: the user's registry layer overrides this one rather than
  editing it, so a bad edit is always one file deletion away from being undone.

  These are also the standing test of the claim the whole design rests on --
  that coverage grows by adding registry entries and not by writing code. Every
  law below was authored as data alone. If one ever needs an engine change to
  work, that is a defect in the generality of the engine and belongs in the
  specification's deviations list, not quietly absorbed here. }

interface

type
  TBuiltInLaw = record
    Id:   string;
    Json: string;
  end;

function BuiltInLaws: TArray<TBuiltInLaw>;

implementation

const
  { ---------------------------------------------------------------------
    Irreversible Michaelis-Menten.

    The reference entry. Every defect class in the static engine is first
    demonstrated against this law, and the founding case of the whole
    project -- Vm*S/(Km + Km) -- is a mutation of it.
    --------------------------------------------------------------------- }
  MichaelisMentenIrrev =
    '{' +
    '  "id": "michaelis_menten_irrev",' +
    '  "name": "Irreversible Michaelis-Menten",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm * S / (Km + S)",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate", "cardinality": "1"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate",        "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax", "V_max", "vmax", "Vf"],' +
    '    "Km": ["Km", "KM", "K_m", "km", "Ks"],' +
    '    "S":  ["S", "s", "Sub", "A"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",     "point": {"S": "0"}},' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "increasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "Vm"},' +
    '    {"type": "value_at",    "point": {"S": "Km"}, "equals": "Vm/2"}' +
    '  ],' +
    '  "sampling": {' +
    '    "S":  {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "Vm": {"scale": "log", "range": ["1e-2", "1e2"], "n": 6},' +
    '    "Km": {"scale": "log", "range": ["1e-2", "1e2"], "n": 6}' +
    '  },' +
    '  "notes": "The saturating form. Km is the substrate concentration at ' +
    'half the maximal rate, which is what the value_at invariant asserts."' +
    '}';

  { ---------------------------------------------------------------------
    Reversible Michaelis-Menten.

    Deliberately declares NO non-negativity: a reversible rate runs backwards
    when the product is in excess, and that is the whole point of it. An
    invariant that is merely usually true would reject this law at load.
    --------------------------------------------------------------------- }
  ReversibleMM =
    '{' +
    '  "id": "reversible_mm",' +
    '  "name": "Reversible Michaelis-Menten",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "(Vf*S/Ks - Vr*P/Kp)/(1 + S/Ks + P/Kp)",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "P":  {"kind": "species",   "position": "product"},' +
    '    "Vf": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Vr": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Ks": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Kp": {"kind": "parameter", "semantics": "half_saturation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vf": ["Vf", "Vmaxf", "Vfwd"], "Vr": ["Vr", "Vmaxr", "Vrev"],' +
    '    "Ks": ["Ks", "Kms", "KmS"],    "Kp": ["Kp", "Kmp", "KmP"]' +
    '  },' +
    { Scoped deliberately. The limit is true for ANY positive parameters, but
      how far S must run before it shows depends on the ratio Vr*P/Kp to
      Vf/Ks -- and the default grid reaches combinations where even S = 1e10
      is still ten per cent short. Sampling is how a law says over what range
      its claims are meant to be judged; without it this law would be
      rejected for being correct. }
    '  "sampling": {' +
    '    "S":  {"scale": "log", "range": ["1e-3", "1e3"], "n": 48},' +
    '    "P":  {"scale": "log", "range": ["1e-3", "1e1"], "n": 4},' +
    '    "Ks": {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Kp": {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Vf": {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Vr": {"scale": "log", "range": ["1e-1", "1e1"], "n": 3}' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": "1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",   "point": {"S": "0", "P": "0"}},' +
    '    {"type": "monotonic", "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic", "var": "P", "direction": "decreasing"},' +
    '    {"type": "limit",     "var": "S", "to": "inf", "equals": "Vf"}' +
    '  ],' +
    '  "notes": "Runs backwards when the product is in excess, so it declares ' +
    'no non-negativity."' +
    '}';

  { ---------------------------------------------------------------------
    Hill activation and repression.

    Present from the start on purpose: the pair proves the engine is generic.
    They differ only in which power sits in the numerator, which makes them
    the sternest test of association -- a defective copy of one sits very
    close to the other.
    --------------------------------------------------------------------- }
  HillActivation =
    '{' +
    '  "id": "hill_activation",' +
    '  "name": "Hill activation",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm * S^n / (K^n + S^n)",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate", "cardinality": "1"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate",        "positive": true},' +
    '    "K":  {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "n":  {"kind": "parameter", "semantics": "cooperativity",   "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax", "V_max", "vmax"],' +
    '    "K":  ["K", "Kd", "K_half", "Ka", "Km"],' +
    '    "n":  ["n", "h", "nH", "coop"]' +
    '  },' +
    { A Hill coefficient below 1 is not a Hill coefficient. Without this the
      default parameter grid samples n down to 0.01, where S^n grows so slowly
      that the rate is still half its ceiling at S = 1e10, and the limit
      invariant -- which is perfectly true -- fails the probe. Sampling is how
      a law says where its claims are meant to hold. }
    '  "sampling": {' +
    '    "S": {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "n": {"scale": "linear", "range": ["1", "4"], "n": 4}' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",     "point": {"S": "0"}},' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "increasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "Vm"},' +
    '    {"type": "value_at",    "point": {"S": "K"}, "equals": "Vm/2"}' +
    '  ],' +
    '  "notes": "Reduces to Michaelis-Menten at n = 1, so association between ' +
    'the two is legitimately ambiguous there and should report S002 rather ' +
    'than guessing."' +
    '}';

  HillRepression =
    '{' +
    '  "id": "hill_repression",' +
    '  "name": "Hill repression",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm*K^n/(K^n + S^n)",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "K":  {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "n":  {"kind": "parameter", "semantics": "cooperativity", "positive": true}' +
    '  },' +
    '  "naming_conventions": {"n": ["n", "h", "nH"], "K": ["K", "Kd", "Ki"]},' +
    { A Hill coefficient below 1 is not a Hill coefficient. Without this the
      default parameter grid samples n down to 0.01, where S^n grows so slowly
      that the rate is still half its ceiling at S = 1e10, and the limit
      invariant -- which is perfectly true -- fails the probe. Sampling is how
      a law says where its claims are meant to hold. }
    '  "sampling": {' +
    '    "S": {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "n": {"scale": "linear", "range": ["1", "4"], "n": 4}' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "decreasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "0"},' +
    '    {"type": "value_at",    "point": {"S": "K"}, "equals": "Vm/2"}' +
    '  ],' +
    '  "notes": "Falls with the repressor rather than rising with it."' +
    '}';

  { ---------------------------------------------------------------------
    The three classical inhibition patterns.

    They differ only in WHERE the inhibition term multiplies -- the Km, the S,
    or the whole denominator -- which is exactly the kind of distinction the
    checker exists to police, and exactly the kind a reader skims past.
    --------------------------------------------------------------------- }
  CompetitiveInhibition =
    '{' +
    '  "id": "competitive_inhibition",' +
    '  "name": "Competitive inhibition",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm*S/(Km*(1 + I/Ki) + S)",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "I":  {"kind": "species",   "position": "inhibitor"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Ki": {"kind": "parameter", "semantics": "dissociation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax"], "Km": ["Km", "KM"], "Ki": ["Ki", "KI", "Kic"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",     "point": {"S": "0"}},' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic",   "var": "I", "direction": "decreasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "Vm"}' +
    '  ],' +
    '  "notes": "The inhibitor raises the apparent Km and leaves Vm alone, ' +
    'which is what the limit invariant pins down."' +
    '}';

  UncompetitiveInhibition =
    '{' +
    '  "id": "uncompetitive_inhibition",' +
    '  "name": "Uncompetitive inhibition",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm*S/(Km + S*(1 + I/Ki))",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "I":  {"kind": "species",   "position": "inhibitor"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Ki": {"kind": "parameter", "semantics": "dissociation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax"], "Km": ["Km", "KM"], "Ki": ["Ki", "KI", "Kiu"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",     "point": {"S": "0"}},' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic",   "var": "I", "direction": "decreasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "Vm/(1 + I/Ki)"}' +
    '  ],' +
    '  "notes": "The inhibition term multiplies S rather than Km, so it lowers ' +
    'the ceiling instead of raising the half-saturation point. The limit ' +
    'invariant is what separates it from the competitive form."' +
    '}';

  NonCompetitiveInhibition =
    '{' +
    '  "id": "noncompetitive_inhibition",' +
    '  "name": "Non-competitive inhibition",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm*S/((Km + S)*(1 + I/Ki))",' +
    '  "roles": {' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "I":  {"kind": "species",   "position": "inhibitor"},' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Ki": {"kind": "parameter", "semantics": "dissociation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax"], "Km": ["Km", "KM"], "Ki": ["Ki", "KI", "Kin"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",     "point": {"S": "0"}},' +
    '    {"type": "nonnegative", "domain": {"S": ["0", "inf"]}},' +
    '    {"type": "monotonic",   "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic",   "var": "I", "direction": "decreasing"},' +
    '    {"type": "limit",       "var": "S", "to": "inf", "equals": "Vm/(1 + I/Ki)"},' +
    '    {"type": "value_at",    "point": {"S": "Km"}, "equals": "Vm/(2*(1 + I/Ki))"}' +
    '  ],' +
    '  "notes": "The inhibition term multiplies the whole denominator, so the ' +
    'half-saturation point stays at Km while the ceiling falls -- which is ' +
    'what tells it apart from the uncompetitive form."' +
    '}';

  { ---------------------------------------------------------------------
    Ordered bi-bi. Four additive denominator terms and two substrates the
    binder has to tell apart with no naming help.
    --------------------------------------------------------------------- }
  OrderedBiBi =
    '{' +
    '  "id": "ordered_bi_bi",' +
    '  "name": "Ordered bi-bi",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm*A*B/(KiA*KmB + KmB*A + KmA*B + A*B)",' +
    '  "roles": {' +
    '    "A":   {"kind": "species",   "position": "substrate"},' +
    '    "B":   {"kind": "species",   "position": "substrate"},' +
    '    "Vm":  {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "KiA": {"kind": "parameter", "semantics": "dissociation", "positive": true},' +
    '    "KmA": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "KmB": {"kind": "parameter", "semantics": "half_saturation", "positive": true}' +
    '  },' +
    '  "applicability": {"reactants": "2", "products": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at_any_zero", "vars": ["A", "B"]},' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["A", "B"], "direction": "increasing"}' +
    '  ],' +
    '  "notes": "Two substrates binding in a fixed order."' +
    '}';

  { ---------------------------------------------------------------------
    Convenience kinetics (uni-uni), after Liebermeister and Klipp.

    Reversible Michaelis-Menten with an explicit enzyme concentration. Close
    enough to reversible_mm to be a fair test of whether association can hold
    two similar laws apart, which is why it is worth shipping.
    --------------------------------------------------------------------- }
  ConvenienceKinetics =
    '{' +
    '  "id": "convenience_uni_uni",' +
    '  "name": "Convenience kinetics (one substrate, one product)",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "E*(kf*S/Ks - kr*P/Kp)/(1 + S/Ks + P/Kp)",' +
    '  "roles": {' +
    '    "E":  {"kind": "species",   "position": "modifier"},' +
    '    "S":  {"kind": "species",   "position": "substrate"},' +
    '    "P":  {"kind": "species",   "position": "product"},' +
    '    "kf": {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "kr": {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "Ks": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Kp": {"kind": "parameter", "semantics": "half_saturation", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "E":  ["E", "Et", "Enz"],' +
    '    "kf": ["kf", "kcatF", "kcat_f"], "kr": ["kr", "kcatR", "kcat_r"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": "1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at",   "point": {"E": "0"}},' +
    '    {"type": "zero_at",   "point": {"S": "0", "P": "0"}},' +
    '    {"type": "monotonic", "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic", "var": "P", "direction": "decreasing"}' +
    '  ],' +
    '  "notes": "Scales linearly with the enzyme, which is what the zero_at E ' +
    'invariant pins down and what separates it from reversible_mm."' +
    '}';

  { ---------------------------------------------------------------------
    Reversible Michaelis-Menten, Haldane form.

    The commoner way to write a reversible step: an equilibrium constant in
    place of a reverse maximal velocity. The two forms are the same law under
    the Haldane relation, Keq = (Vf*Kp)/(Vr*Ks), but they are written
    differently and a model uses one or the other, so both are registered.

    WHICH WRITING IS REGISTERED MATTERS. Canonicalisation normalises writing,
    not algebra, and deliberately does not distribute a product over a sum --
    that non-distribution is what protects the misplaced-parenthesis signal.
    So (Vf/Ks)*(S - P/Keq)/(1 + S/Ks + P/Kp) and the algebraically identical
    Vf*(S - P/Keq)/(Ks*(1 + S/Ks + P/Kp)) are DIFFERENT TREES. The first is
    registered because it is the conventional setting-out; a model using the
    second is reported as a regrouping rather than matched silently.

    Its characteristic invariant is the zero_at S = P/Keq. That is what Keq
    MEANS -- the rate vanishes exactly at equilibrium -- and it is the direct
    counterpart of value_at S = Km giving half the maximal rate. A model that
    writes this shape with Keq somewhere it does not belong is structurally
    fine and caught by that one line.
    --------------------------------------------------------------------- }
  ReversibleMMHaldane =
    '{' +
    '  "id": "reversible_mm_keq",' +
    '  "name": "Reversible Michaelis-Menten (Haldane, with Keq)",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "(Vf/Ks)*(S - P/Keq)/(1 + S/Ks + P/Kp)",' +
    '  "roles": {' +
    '    "S":   {"kind": "species",   "position": "substrate"},' +
    '    "P":   {"kind": "species",   "position": "product"},' +
    '    "Vf":  {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Ks":  {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Kp":  {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "Keq": {"kind": "parameter", "semantics": "equilibrium_constant", "positive": true}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vf":  ["Vf", "Vmax", "Vmaxf", "V"],' +
    '    "Ks":  ["Ks", "Kms", "KmS", "Km", "Ka"],' +
    '    "Kp":  ["Kp", "Kmp", "KmP"],' +
    '    "Keq": ["Keq", "keq", "Ke", "K_eq"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": "1"},' +
    '  "sampling": {' +
    '    "S":   {"scale": "log", "range": ["1e-3", "1e3"], "n": 48},' +
    '    "P":   {"scale": "log", "range": ["1e-3", "1e1"], "n": 4},' +
    '    "Ks":  {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Kp":  {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Vf":  {"scale": "log", "range": ["1e-1", "1e1"], "n": 3},' +
    '    "Keq": {"scale": "log", "range": ["1e-1", "1e1"], "n": 3}' +
    '  },' +
    '  "invariants": [' +
    '    {"type": "zero_at",   "point": {"S": "0", "P": "0"}},' +
    '    {"type": "zero_at",   "point": {"S": "P/Keq"}},' +
    '    {"type": "monotonic", "var": "S", "direction": "increasing"},' +
    '    {"type": "monotonic", "var": "P", "direction": "decreasing"},' +
    '    {"type": "limit",     "var": "S", "to": "inf", "equals": "Vf"}' +
    '  ],' +
    '  "notes": "The rate is zero exactly at S = P/Keq, which is what the ' +
    'equilibrium constant means and what the second invariant pins down. ' +
    'Written with Ks in the numerator prefactor, which is how the form is ' +
    'conventionally set out; Vf*(S - P/Keq)/(Ks*(1 + S/Ks + P/Kp)) is the ' +
    'same rate but a different tree, and is reported as a regrouping."' +
    '}';

  { ---------------------------------------------------------------------
    Irreversible mass action, any order.

    A generative law: the expression is a family, instantiated per reaction
    from that reaction''s stoichiometry. Without this, mass action needs one
    entry per order and the "coverage grows by adding registry entries"
    claim fails on the commonest law in biology.

    The "exponent" field on a cardinality-n role names the per-instance
    exponent symbol. Without it the validator has no way to know that "ai" in
    the expression is legitimate rather than an undeclared identifier.
    --------------------------------------------------------------------- }
  MassActionIrrev =
    '{' +
    '  "id": "mass_action_irrev",' +
    '  "name": "Irreversible mass action",' +
    '  "version": 1, "enabled": true,' +
    '  "generative": true,' +
    '  "expression": "k * prod(Si^ai)",' +
    '  "roles": {' +
    '    "k":  {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "Si": {"kind": "species",   "position": "substrate", "cardinality": "n",' +
    '           "exponent": "ai"}' +
    '  },' +
    '  "naming_conventions": {"k": ["k", "k1", "kf", "K"]},' +
    '  "applicability": {"exponents_from": "stoichiometry"},' +
    '  "invariants": [' +
    '    {"type": "zero_at_any_zero", "vars": ["Si"]},' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["Si"], "direction": "increasing"}' +
    '  ],' +
    '  "notes": "Exponents come from the reaction stoichiometry, not from the ' +
    'registry, so one entry checks first-, second- and third-order reactions."' +
    '}';

  { ---------------------------------------------------------------------
    Reversible mass action.

    The second generative family, and the one that showed the instantiator
    was not general. It needs two scalar rate constants and a product over
    the PRODUCTS, both of which the old instantiator refused by
    construction -- so this entry could not have been added as a registry
    entry alone, which is a finding about the engine and is recorded in
    section 18.7 rather than smoothed over.

    Not nonnegative and not zero-at-any-zero: the rate is negative whenever
    the reverse term dominates, and setting one substrate to zero leaves the
    reverse term running. Monotonic each way is what actually holds.
    --------------------------------------------------------------------- }
  MassActionRev =
    '{' +
    '  "id": "mass_action_rev",' +
    '  "name": "Reversible mass action",' +
    '  "version": 1, "enabled": true,' +
    '  "generative": true,' +
    '  "expression": "kf * prod(Si^ai) - kr * prod(Pj^bj)",' +
    '  "roles": {' +
    '    "kf": {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "kr": {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "Si": {"kind": "species",   "position": "substrate", "cardinality": "n",' +
    '           "exponent": "ai"},' +
    '    "Pj": {"kind": "species",   "position": "product",   "cardinality": "n",' +
    '           "exponent": "bj"}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "kf": ["kf", "kon", "kplus", "kforward"],' +
    '    "kr": ["kr", "koff", "kminus", "kreverse"]' +
    '  },' +
    { A reverse term needs something to run backwards from. With no products
      the product over Pj is the empty product, 1, and the law degenerates to
      "kf*S - kr" -- which is not reversible mass action and which then fits
      irreversible reactions loosely enough to report defects against them.
      328 of the corpus errors were that. The schema already had the field;
      the entry simply had not said so. }
    '  "applicability": {"reactants": ">=1", "products": ">=1",' +
    '                    "exponents_from": "stoichiometry"},' +
    '  "invariants": [' +
    '    {"type": "monotonic", "vars": ["Si"], "direction": "increasing"},' +
    '    {"type": "monotonic", "vars": ["Pj"], "direction": "decreasing"}' +
    '  ],' +
    '  "notes": "Exponents come from the reaction stoichiometry on both ' +
    'sides, so one entry checks A <-> B, A + B <-> C and 2A <-> B alike. ' +
    'k1 and k2 are deliberately NOT listed as direction conventions: a ' +
    'numeric suffix is a reaction index at least as often as a direction, ' +
    'and listing them made every model that writes k2 for the forward ' +
    'constant of reaction 2 report a transposition it had not made."' +
    '}';

  { ---------------------------------------------------------------------
    Catalytic mass action.

    A rate proportional to a species the reaction neither consumes nor
    produces: transcription proportional to its gene, translation to its
    mRNA, a conversion proportional to the enzyme. Written "k*E" when the
    reaction has no substrate to speak of, "k*E*S" when it has.

    This was the single largest gap the BioModels corpus exposed once
    association had been fixed. 416 of the 798 erroring reactions traced --
    52% -- were reactions whose rate law depends on a MODIFIER, and every one
    of them was being dragged onto ordinary mass action, which takes its
    species from stoichiometry alone and therefore instantiated k*<substrate>
    and reported the modifier as a substrate swap. 255 S007 findings came
    from that one mismatch.

    The modifiers constraint is what keeps it distinct from mass action. With
    no modifiers this law instantiates to k*prod(Si), which IS mass action,
    and the two would tie on every ordinary reaction and cancel each other
    out -- exactly the ambiguity S002 exists to refuse.
    --------------------------------------------------------------------- }
  CatalyticMassAction =
    '{' +
    '  "id": "catalytic_mass_action",' +
    '  "association_floor": 0.08,' +
    '  "name": "Catalytic mass action",' +
    '  "version": 1, "enabled": true,' +
    '  "generative": true,' +
    '  "expression": "k * prod(Ej) * prod(Si^ai)",' +
    '  "roles": {' +
    '    "k":  {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "Ej": {"kind": "species",   "position": "modifier",  "cardinality": "n"},' +
    '    "Si": {"kind": "species",   "position": "substrate", "cardinality": "n",' +
    '           "exponent": "ai"}' +
    '  },' +
    '  "naming_conventions": {"k": ["k", "kcat", "ks", "V", "v", "kf"]},' +
    '  "applicability": {"modifiers": ">=1", "exponents_from": "stoichiometry"},' +
    '  "invariants": [' +
    '    {"type": "zero_at_any_zero", "vars": ["Ej"]},' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["Ej"], "direction": "increasing"}' +
    '  ],' +
    '  "notes": "The modifiers constraint is load-bearing: with no modifier ' +
    'this instantiates to plain mass action and the two laws would tie on ' +
    'every ordinary reaction."' +
    '}';

  { ---------------------------------------------------------------------
    Modifier-proportional, zero order in the substrate.

    A reaction that consumes something at a rate which does not depend on how
    much of it there is: saturated transport, a supply step, a conversion
    limited entirely by its enzyme. "FH2f -> FH4; kter*FH2b" is the corpus's
    own example -- the substrate is consumed and appears nowhere in the rate.

    Distinct from catalytic mass action, which multiplies the substrates in.
    Adding the catalytic form alone moved BioModels errors the WRONG way,
    16.6% to 21.3%, because every reaction of this shape then matched a law
    that insisted on a substrate term it did not have and got S005 and S010
    for it. The two together are what the corpus actually contains.

    reactants >= 1 is what keeps them apart. With no substrates catalytic
    mass action already instantiates to k*prod(Ej), which is this law
    exactly, and the pair would tie on every synthesis reaction.

    Nothing here says the omission is fine: S017 still reports that a
    consumed species is absent from its own rate law, which is the honest
    observation and a warning rather than an error. What this law changes is
    that the reaction is no longer ALSO accused of being a broken version of
    a law it was never following.
    --------------------------------------------------------------------- }
  ModifierProportional =
    '{' +
    '  "id": "modifier_proportional",' +
    '  "association_floor": 0.08,' +
    '  "name": "Modifier-proportional (zero order in substrate)",' +
    '  "version": 1, "enabled": true,' +
    '  "generative": true,' +
    '  "expression": "k * prod(Ej)",' +
    '  "roles": {' +
    '    "k":  {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "Ej": {"kind": "species",   "position": "modifier", "cardinality": "n"}' +
    '  },' +
    '  "naming_conventions": {"k": ["k", "kcat", "ks", "V", "v", "kf"]},' +
    '  "applicability": {"reactants": ">=1", "modifiers": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "zero_at_any_zero", "vars": ["Ej"]},' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["Ej"], "direction": "increasing"}' +
    '  ],' +
    '  "notes": "reactants >= 1 is load-bearing: with no substrate this is ' +
    'catalytic mass action exactly, and the two would tie on every ' +
    'synthesis reaction."' +
    '}';

  { ---------------------------------------------------------------------
    Zero order -- a constant rate.

    "A -> B; k1" is a real rate law: a step running at a fixed rate, which is
    what a saturated enzyme or a controlled infusion looks like. Without an
    entry for it the report said "no registered rate law matches", which is
    both wrong and unhelpful -- the reader is told the checker has nothing to
    say when in fact the reaction is textbook zero order.

    It is also, far more often, a substrate that was left out by mistake. The
    report says BOTH: this law names what was written, and S017 goes on
    warning that A is consumed and does not appear. Naming the law does not
    excuse the omission, and the two lines together are the honest reading --
    "this is zero order, and here is why you might not have meant it".

    reactants >= 1 keeps it apart from mass action, whose empty product for a
    source reaction ("-> B; k") already instantiates to exactly k. Without it
    the two tie on every source term and neither is applied.

    The tight association_floor is not tuning. Zero order has no structure at
    all, so "close to zero order" is not a meaningful idea: either the rate
    law is a constant or it is not. Anything else that matched loosely would
    be a law this one has no business claiming.
    --------------------------------------------------------------------- }
  ZeroOrder =
    '{' +
    '  "id": "zero_order",' +
    '  "name": "Zero order (constant rate)",' +
    '  "version": 1, "enabled": true,' +
    '  "association_floor": 0.02,' +
    '  "expression": "k",' +
    '  "roles": {' +
    '    "k": {"kind": "parameter", "semantics": "rate_constant", "positive": true}' +
    '  },' +
    '  "naming_conventions": {"k": ["k", "k1", "v", "V", "kf", "vmax"]},' +
    '  "applicability": {"reactants": ">=1"},' +
    '  "invariants": [' +
    '    {"type": "nonnegative"}' +
    '  ],' +
    '  "notes": "A step running at a fixed rate -- a saturated enzyme, a ' +
    'controlled infusion. Often it is instead a substrate left out of the ' +
    'rate law by mistake, which is why S017 still reports the reactant that ' +
    'does not appear."' +
    '}';

  { ---------------------------------------------------------------------
    Hill, with the half-saturation constant already raised to n.

    The registered Hill laws write the denominator as K^n + S^n, where K is a
    concentration. It is at least as common to write Km + S^n, where Km is a
    single constant standing for the whole of K^n -- it is what a modeller
    fits, and what most papers tabulate.

    The two are the same function and a long way apart structurally. Without
    these entries "Vm/(Km + A^n)" matched neither Hill law, sat 0.522 from
    both, and was reported as an ambiguity the modeller was invited to settle
    by annotation -- between two laws that did not describe it.

    The repression form has no S in the numerator at all, which is what makes
    it decreasing; the activation form keeps S^n there.
    --------------------------------------------------------------------- }
  HillActivationLumped =
    '{' +
    '  "id": "hill_activation_lumped",' +
    '  "name": "Hill activation (lumped half-saturation)",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm * S^n / (Km + S^n)",' +
    '  "roles": {' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "n":  {"kind": "parameter", "semantics": "cooperativity", "positive": true},' +
    '    "S":  {"kind": "species",   "position": "substrate"}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax", "V_max", "VM"],' +
    '    "Km": ["Km", "K", "Kd", "Ka", "K_half"],' +
    '    "n":  ["n", "h", "nH", "p"]' +
    '  },' +
    '  "applicability": {"reactants": "1"},' +
    '  "sampling": {' +
    '    "S": {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "n": {"scale": "linear", "range": ["1", "4"], "n": 4}' +
    '  },' +
    '  "invariants": [' +
    '    {"type": "zero_at_any_zero", "vars": ["S"]},' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["S"], "direction": "increasing"},' +
    '    {"type": "limit", "var": "S", "to": "inf", "equals": "Vm"}' +
    '  ],' +
    '  "notes": "Km stands for the whole of K^n, which is what is usually ' +
    'fitted and tabulated. Same function as hill_activation, written the way ' +
    'most papers write it."' +
    '}';

  HillRepressionLumped =
    '{' +
    '  "id": "hill_repression_lumped",' +
    '  "name": "Hill repression (lumped half-saturation)",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm / (Km + S^n)",' +
    '  "roles": {' +
    '    "Vm": {"kind": "parameter", "semantics": "max_rate", "positive": true},' +
    '    "Km": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "n":  {"kind": "parameter", "semantics": "cooperativity", "positive": true},' +
    '    "S":  {"kind": "species",   "position": "substrate"}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax", "V_max", "VM", "alpha"],' +
    '    "Km": ["Km", "K", "Kd", "Ki", "K_half"],' +
    '    "n":  ["n", "h", "nH", "p"]' +
    '  },' +
    '  "sampling": {' +
    '    "S": {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "n": {"scale": "linear", "range": ["1", "4"], "n": 4}' +
    '  },' +
    '  "invariants": [' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["S"], "direction": "decreasing"},' +
    '    {"type": "limit", "var": "S", "to": "inf", "equals": "0"}' +
    '  ],' +
    '  "notes": "No S in the numerator, which is what makes it decreasing. ' +
    'Km stands for the whole of K^n."' +
    '}';

  { ---------------------------------------------------------------------
    Hill repression with a constant numerator.

    The third of the three ways this function gets written, and the last one
    needed. The numerator is a single rate constant rather than Vm*K^n, while
    the denominator still carries K^n:

        Vm*K^n / (K^n + S^n)   hill_repression
        Vm     / (Km  + S^n)   hill_repression_lumped
        k      / (K^n + S^n)   this one

    They are the same function three ways round, differing in which constants
    the modeller folded together before writing it down. The activation side
    needs no equivalent: its numerator is always Vm*S^n, so the two entries
    already cover it.

    Until this existed, "k1/(Km^n + A^n)" sat close to BOTH Hill laws --
    the denominator matches hill_repression exactly and only the numerator
    differs -- and was reported as an ambiguity to be settled by annotating
    it as a law it was not.
    --------------------------------------------------------------------- }
  HillRepressionConst =
    '{' +
    '  "id": "hill_repression_const",' +
    '  "name": "Hill repression (constant numerator)",' +
    '  "version": 1, "enabled": true,' +
    '  "expression": "Vm / (K^n + S^n)",' +
    '  "roles": {' +
    '    "Vm": {"kind": "parameter", "semantics": "rate_constant", "positive": true},' +
    '    "K": {"kind": "parameter", "semantics": "half_saturation", "positive": true},' +
    '    "n": {"kind": "parameter", "semantics": "cooperativity", "positive": true},' +
    '    "S": {"kind": "species",   "position": "substrate"}' +
    '  },' +
    '  "naming_conventions": {' +
    '    "Vm": ["Vm", "Vmax", "k", "k1", "alpha"],' +
    '    "K": ["K", "Km", "Kd", "Ki", "K_half"],' +
    '    "n": ["n", "h", "nH", "p"]' +
    '  },' +
    '  "sampling": {' +
    '    "S": {"scale": "log", "range": ["1e-3", "1e3"], "n": 64},' +
    '    "n": {"scale": "linear", "range": ["1", "4"], "n": 4}' +
    '  },' +
    '  "invariants": [' +
    '    {"type": "nonnegative"},' +
    '    {"type": "monotonic", "vars": ["S"], "direction": "decreasing"},' +
    '    {"type": "limit", "var": "S", "to": "inf", "equals": "0"}' +
    '  ],' +
    '  "notes": "The numerator is a single rate constant, the denominator ' +
    'still carries K^n. Same function as hill_repression with Vm*K^n folded ' +
    'into one constant, which is how it is usually written when K was ' +
    'measured as a concentration."' +
    '}';

function BuiltInLaws: TArray<TBuiltInLaw>;

  function L(const AId, AJson: string): TBuiltInLaw;
  begin
    Result.Id := AId; Result.Json := AJson;
  end;

begin
  Result := [
    L('michaelis_menten_irrev',    MichaelisMentenIrrev),
    L('reversible_mm',             ReversibleMM),
    L('hill_activation',           HillActivation),
    L('hill_repression',           HillRepression),
    L('competitive_inhibition',    CompetitiveInhibition),
    L('uncompetitive_inhibition',  UncompetitiveInhibition),
    L('noncompetitive_inhibition', NonCompetitiveInhibition),
    L('ordered_bi_bi',             OrderedBiBi),
    L('reversible_mm_keq',         ReversibleMMHaldane),
    L('convenience_uni_uni',       ConvenienceKinetics),
    L('mass_action_irrev',         MassActionIrrev),
    L('mass_action_rev',           MassActionRev),
    L('catalytic_mass_action',     CatalyticMassAction),
    L('modifier_proportional',     ModifierProportional),
    L('zero_order',                ZeroOrder),
    L('hill_activation_lumped',    HillActivationLumped),
    L('hill_repression_lumped',    HillRepressionLumped),
    L('hill_repression_const',     HillRepressionConst)
  ];
end;

end.
