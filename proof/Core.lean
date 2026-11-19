/-
  Foundation skeleton for the canonical model.

  This file carries no definition of the model and no
  theorem of the program. The claims of the
  specification are proposed semantics, listed in its
  claims section, and none is stated here yet. The
  single fact below exists only so the family gate has
  a compiled development with a printed audit to check;
  it is a fact of the logic, not of the model.
-/

/-- The seed fact: two propositions joined by a two way
    implication are equal, by the logic's own rule. -/
theorem seed (left right : Prop) (step : left ↔ right) : left = right :=
  propext step

#print axioms seed
