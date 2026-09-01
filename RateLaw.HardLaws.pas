unit RateLaw.HardLaws;

{ Laws complicated enough to be a real test.

  Michaelis-Menten has two operators and three symbols. Almost nothing can go
  wrong in it that is not immediately obvious, so an engine that handles it
  proves very little. These are the shapes that actually occur in models and
  that a checker has to survive:

    competitive_inhibition   a nested sum inside a product inside a sum, and
                             a modifier that is neither reactant nor product

    reversible_mm            a difference in the numerator, so the sign
                             matters, and the same symbols occur on both
                             sides of it

    ordered_bi_bi            four additive terms in the denominator, two
                             substrates that the binder must tell apart with
                             no naming help, and identifiers repeated four
                             and five times over

    hill_repression          a power whose base repeats, where a duplicated
                             operand is a whole subtree rather than a leaf

  They are loaded as a user layer rather than compiled in, which also
  exercises the registry's layering. }

interface

function HardLaws: TArray<string>;

implementation

const
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
    '  "applicability": {"reactants": "1", "products": ">=1"}' +
    '}';

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
    '    "Vf": ["Vf", "Vmaxf"], "Vr": ["Vr", "Vmaxr"],' +
    '    "Ks": ["Ks", "Kms"], "Kp": ["Kp", "Kmp"]' +
    '  },' +
    '  "applicability": {"reactants": "1", "products": "1"}' +
    '}';

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
    '  "applicability": {"reactants": "2", "products": ">=1"}' +
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
    '  "naming_conventions": {"n": ["n", "h", "nH"]},' +
    '  "applicability": {"reactants": "1", "products": ">=1"}' +
    '}';

function HardLaws: TArray<string>;
begin
  { Empty. Every law this unit used to hold now ships in
    RateLaw.BuiltInLaws, so keeping copies here would only let the two
    drift. The unit stays as the hook for a law worth TESTING against but
    not worth shipping. }
  Result := nil;
end;

end.
