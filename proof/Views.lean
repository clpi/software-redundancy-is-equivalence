import Core

/-! # Derived views

    Section 12 of the spec: everything beyond the one
    graph is a derived view — reproducible from the
    graph, labeled as derived wherever it is produced,
    and never a second source of truth. A dependency
    graph is a projection of the derived steps below;
    an incidence view is the membership reading of the
    edges by inspection; neither is a structure of the
    model. This file carries the one derived layer the
    spec obliges: recorded steps and derivability.

    A step — a premise list and a conclusion — is a
    derived object whose terms are members of edges of
    the one graph, recorded as a color or as a level's
    content under the scheme that owns it, never as an
    edge of the graph. Derivability is the closure
    reading over such steps. Its standing facts are
    restated and proved here: monotone in the
    collected terms, monotone in the recorded steps,
    and the elimination fact — adjoining a term
    already derivable changes the derivable reading
    not at all. -/

variable {Sym : Type}

/-- A derived step: a premise list and a conclusion.
    A step is a derived object, never an edge. -/
structure Step (Sym : Type) where
  /-- The premises of the step. -/
  given : List (Term Sym)
  /-- The conclusion of the step. -/
  goal : Term Sym
deriving DecidableEq

/-- Derivability: the closure reading over a list of
    derived steps and a store of collected terms. A
    term is derivable when it stands in the store, or
    when some recorded step's premises are all
    derivable and it is that step's conclusion. -/
inductive Deriv [DecidableEq Sym] (steps : List (Step Sym)) :
    List (Term Sym) → Term Sym → Prop where
  /-- A collected term is derivable. -/
  | base : ∀ {store term}, term ∈ store →
      Deriv steps store term
  /-- A step whose premises are all derivable yields
      its conclusion. -/
  | step : ∀ {store step}, step ∈ steps →
      (∀ p ∈ step.given, Deriv steps store p) →
      Deriv steps store step.goal

/-- Monotone in the collected terms: a derivation
    from a smaller store is a derivation from any
    larger store. -/
theorem derivstore [DecidableEq Sym]
    {steps : List (Step Sym)}
    {store store' : List (Term Sym)}
    {term : Term Sym}
    (hsub : ∀ t ∈ store, t ∈ store') :
    Deriv steps store term → Deriv steps store' term := by
  intro h
  induction h with
  | base hmem => exact Deriv.base (hsub _ hmem)
  | step hmem _ ih => exact Deriv.step hmem ih

/-- Monotone in the recorded steps: a derivation
    over fewer steps is a derivation over any larger
    step list. -/
theorem derivsteps [DecidableEq Sym]
    {steps steps' : List (Step Sym)}
    {store : List (Term Sym)} {term : Term Sym}
    (hsub : ∀ s ∈ steps, s ∈ steps') :
    Deriv steps store term → Deriv steps' store term := by
  intro h
  induction h with
  | base hmem => exact Deriv.base hmem
  | step hmem _ ih => exact Deriv.step (hsub _ hmem) ih

/-- Elimination: adjoining a term already derivable
    to the store changes the derivable reading not at
    all — every derivation from the enlarged store is
    a derivation from the store, and the converse is
    monotonicity. -/
theorem derivelim [DecidableEq Sym]
    {steps : List (Step Sym)}
    {store : List (Term Sym)} {extra term : Term Sym}
    (hder : Deriv steps store extra) :
    Deriv steps (store ++ [extra]) term ↔
      Deriv steps store term := by
  constructor
  · intro h
    induction h with
    | base hmem =>
        cases List.mem_append.mp hmem with
        | inl h => exact Deriv.base h
        | inr h =>
            rw [List.mem_singleton] at h
            exact h ▸ hder
    | step hmem _ ih => exact Deriv.step hmem ih
  · intro h
    exact derivstore (fun t ht =>
      List.mem_append_left _ ht) h
