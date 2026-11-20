import Claims
import Registry

/-! # Standing controls

    The five standing controls of section 13, each a
    proved statement over concrete data, kept in the
    tree. Each refutes the named false claim by
    exhibiting the concrete fact: zero refutes the
    universal redundancy claim; split refutes the
    claim that redundancy can be split away by
    growth; free refutes appearance without a cross
    join; order refutes silent identification of
    spellings; filter refutes the conflation of the
    two filters. -/

/-- Concrete symbols for the controls. -/
inductive Tok where
  /-- First letter. -/
  | a
  /-- Second letter. -/
  | b
  /-- Third letter. -/
  | c
  /-- Fourth letter. -/
  | d
  /-- Fifth letter. -/
  | e
  /-- Sixth letter. -/
  | f
  /-- Seventh letter. -/
  | g
  /-- Eighth letter. -/
  | h
deriving DecidableEq

/-- The concrete kind symbols. -/
def kTok : Kinds Tok :=
  ⟨Tok.a, Tok.b, Tok.c, Tok.d, Tok.e, by decide⟩

/-- The singleton edge of one concrete term. -/
def sing (t : Term Tok) : Edge Tok :=
  { terms := [t], colors := [] }

namespace Control

/-- Control zero: a valid graph with excess zero and
    at least one edge exists — here two singleton
    edges. No universal redundancy claim is stated
    anywhere; this exhibits the zero case. -/
theorem zero :
    ∃ g : Graph Tok, Valid kTok g ∧ g.edges ≠ [] ∧
      excess g = 0 ∧
      ∀ e ∈ g.edges, e.terms.length = 1 := by
  let g : Graph Tok :=
    enter kTok (enter kTok empty (Term.atom Tok.a)
      Tok.a Tok.a) (Term.atom Tok.b) Tok.a Tok.a
  have hvalid : Valid kTok g :=
    entervalid kTok _ (entervalid kTok _ (emptyvalid
      kTok) (Term.atom Tok.a) Tok.a Tok.a)
      (Term.atom Tok.b) Tok.a Tok.a
  have hedges : g.edges =
      [sing (Term.atom Tok.a), sing (Term.atom Tok.b)] := by
    decide
  refine ⟨g, hvalid, ?_, ?_, ?_⟩
  · intro hnil
    rw [hedges] at hnil
    cases hnil
  · decide
  · intro e he
    rw [hedges] at he
    cases List.mem_cons.mp he with
    | inl h => rw [h]; rfl
    | inr h =>
        cases List.mem_cons.mp h with
        | inl h => rw [h]; rfl
        | inr h => cases h

/-- Control split: growth from a witnessed redundant
    graph is witnessed redundant, on the concrete
    instance — one join of two singleton edges gives
    excess one, and every ready run from it keeps
    excess at least one. The false claim refuted: an
    operation sequence from a redundant graph to a
    grown graph of smaller excess. -/
theorem split :
    ∃ g : Graph Tok, excess g = 1 ∧
      same g (Term.atom Tok.a) (Term.atom Tok.b) ∧
      ∀ ops, Ready kTok g ops →
        1 ≤ excess (run kTok g ops) := by
  let g : Graph Tok :=
    join kTok (enter kTok (enter kTok empty
      (Term.atom Tok.a) Tok.a Tok.a) (Term.atom Tok.b)
      Tok.a Tok.a) (Term.atom Tok.a) (Term.atom Tok.b)
      Tok.a Tok.a
  have hex : excess g = 1 := by decide
  refine ⟨g, hex, ?_, ?_⟩
  · have hvalid : Valid kTok (enter kTok
        (enter kTok empty (Term.atom Tok.a) Tok.a
          Tok.a) (Term.atom Tok.b) Tok.a Tok.a) :=
      entervalid kTok _ (entervalid kTok _
        (emptyvalid kTok) (Term.atom Tok.a) Tok.a
        Tok.a) (Term.atom Tok.b) Tok.a Tok.a
    exact joinsame kTok _ hvalid (Term.atom Tok.a)
      (Term.atom Tok.b) Tok.a Tok.a
  · intro ops hready
    have h := excessrun kTok hready
    omega

/-- The first append of control free: one entry of
    the first term. -/
def left : List (Op Tok) :=
  [Op.enter (Term.atom Tok.a) Tok.a Tok.a]

/-- The second append of control free: one entry of
    the second term. -/
def right : List (Op Tok) :=
  [Op.enter (Term.atom Tok.b) Tok.a Tok.a]

/-- Control free: two appends with no cross join and
    no shared term do not produce appearance — the
    separateness premise of claim three holds on this
    instance by computation, the combined excess is
    exactly the two alone deltas over the common
    excess, and the two terms do not stand together. -/
theorem free :
    alone kTok empty left right ∧
    excess (run kTok empty (left ++ right)) =
      excess (empty : Graph Tok) +
        joins kTok empty left +
        joins kTok empty right ∧
    ¬ same (run kTok empty (left ++ right))
      (Term.atom Tok.a) (Term.atom Tok.b) := by
  refine ⟨by unfold alone; decide, by decide, ?_⟩
  have hedges : (run kTok empty
      (left ++ right)).edges =
      [sing (Term.atom Tok.a), sing (Term.atom Tok.b)] := by
    decide
  intro hs
  obtain ⟨e, he, ha, hb⟩ := hs
  rw [hedges] at he
  cases List.mem_cons.mp he with
  | inl h =>
      rw [h] at hb
      cases List.mem_singleton.mp hb
  | inr h =>
      cases List.mem_cons.mp h with
      | inl h =>
          rw [h] at ha
          cases List.mem_singleton.mp ha
      | inr h => cases h

/-- The first spelling of control order. -/
def one : Term Tok :=
  Term.form (Term.atom Tok.a)
    [Term.atom Tok.b, Term.atom Tok.c]

/-- The second spelling of control order: the same
    form with its arguments exchanged. -/
def two : Term Tok :=
  Term.form (Term.atom Tok.a)
    [Term.atom Tok.c, Term.atom Tok.b]

/-- Control order: two spellings differing only in
    argument order stand in distinct edges in a
    concrete graph until an equivalence joins them —
    the model does not silently identify them. -/
theorem order :
    one ≠ two ∧
    ¬ same (enter kTok (enter kTok empty one Tok.a
        Tok.a) two Tok.a Tok.a) one two ∧
    same (join kTok (enter kTok (enter kTok empty one
        Tok.a Tok.a) two Tok.a Tok.a) one two Tok.a
        Tok.a) one two := by
  refine ⟨by decide, ?_, ?_⟩
  · have hedges : (enter kTok (enter kTok empty one
        Tok.a Tok.a) two Tok.a Tok.a).edges =
        [sing one, sing two] := by
      decide
    intro hs
    obtain ⟨e, he, ha, hb⟩ := hs
    rw [hedges] at he
    cases List.mem_cons.mp he with
    | inl h =>
        rw [h] at hb
        cases List.mem_singleton.mp hb
    | inr h =>
        cases List.mem_cons.mp h with
        | inl h =>
            rw [h] at ha
            cases List.mem_singleton.mp ha
        | inr h => cases h
  · have hvalid : Valid kTok (enter kTok
        (enter kTok empty one Tok.a Tok.a) two Tok.a
          Tok.a) :=
      entervalid kTok _ (entervalid kTok _
        (emptyvalid kTok) one Tok.a Tok.a) two Tok.a
        Tok.a
    exact joinsame kTok _ hvalid one two Tok.a Tok.a

/-- Control filter: on concrete edges, an edge
    painted observed only carries no intended mark,
    and an edge painted wanted only carries none
    either — the derived mark of the painter is the
    intended mark in neither case, by the two-filter
    theorem. -/
theorem filter :
    let q : Qual Tok :=
      ⟨Tok.a, Tok.b, Tok.c, Tok.d, Tok.e, Tok.f,
        Tok.g, by decide⟩
    let seenedge : Edge Tok :=
      { terms := [Term.atom Tok.a],
        colors := [{ who := Tok.a, kind := Tok.a, mark := Tok.a, epoch := 0 }] }
    let wantededge : Edge Tok :=
      { terms := [Term.atom Tok.a],
        colors := [{ who := Tok.a, kind := Tok.b, mark := Tok.a, epoch := 0 }] }
    derived q Tok.a seenedge ≠ q.intended ∧
      derived q Tok.a wantededge ≠ q.intended := by
  constructor
  · intro h
    have hboth := (derivedintended
      ⟨Tok.a, Tok.b, Tok.c, Tok.d, Tok.e, Tok.f,
        Tok.g, by decide⟩ Tok.a
      { terms := [Term.atom Tok.a],
        colors := [{ who := Tok.a, kind := Tok.a, mark := Tok.a, epoch := 0 }] }).mp h
    obtain ⟨c, hc, -, hkind⟩ := hboth.2
    cases List.mem_cons.mp hc with
    | inl h => rw [h] at hkind; cases hkind
    | inr h => cases h
  · intro h
    have hboth := (derivedintended
      ⟨Tok.a, Tok.b, Tok.c, Tok.d, Tok.e, Tok.f,
        Tok.g, by decide⟩ Tok.a
      { terms := [Term.atom Tok.a],
        colors := [{ who := Tok.a, kind := Tok.b, mark := Tok.a, epoch := 0 }] }).mp h
    obtain ⟨c, hc, -, hkind⟩ := hboth.1
    cases List.mem_cons.mp hc with
    | inl h => rw [h] at hkind; cases hkind
    | inr h => cases h

end Control
