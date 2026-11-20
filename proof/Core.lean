/-
  The canonical model: one hypergraph of equivalent terms.

  This file implements sections 2 to 7 and section 10 of
  the specification in this repository: symbols and terms,
  the three scopes, the one lattice of states, the one
  hypergraph with its validity predicate, equivalence,
  levels, the finite resolved upper bound and the view,
  and redundancy as excess. The growth operations of
  section 8 live in the next file; they are the only way
  a graph of this program is built.

  Four states are kept distinct in every comment here:
  settled intent, proposed semantics, implemented
  behavior, verified behavior. What this file states is
  implemented behavior; what the family gate checks at
  the landed pin is verified behavior.
-/

/-- A term is a symbolic expression: an atom term is one
    symbol standing alone, a form term is a head term
    applied to a finite list of argument terms, in list
    order. The symbol type is a parameter with decidable
    equality and nothing else fixed about it: a symbol
    is never a number and never an identifier. -/
inductive Term (Sym : Type) where
  | atom : Sym → Term Sym
  | form : Term Sym → List (Term Sym) → Term Sym

namespace Term

variable {Sym : Type} [DecidableEq Sym]

/- Spelling equality of terms, as a boolean, computed by
   one recursion over both spellings at once. -/
mutual
def teq : Term Sym → Term Sym → Bool
  | .atom a, .atom b => decide (a = b)
  | .form h1 a1, .form h2 a2 => teq h1 h2 && leq a1 a2
  | _, _ => false
def leq : List (Term Sym) → List (Term Sym) → Bool
  | [], [] => true
  | x :: xs, y :: ys => teq x y && leq xs ys
  | _, _ => false
end

/-- The boolean spelling test decides spelling equality:
    it answers true exactly on equal terms, and the list
    form answers true exactly on equal lists. -/
theorem teqiff : ∀ (a b : Term Sym), teq a b = true ↔ a = b :=
  fun a =>
    Term.rec (motive_1 := fun a => ∀ b, teq a b = true ↔ a = b)
      (motive_2 := fun l => ∀ l2, leq l l2 = true ↔ l = l2)
      (fun s b => by
        cases b with
        | atom s2 => simp only [teq, decide_eq_true_eq, Term.atom.injEq]
        | form h args =>
            simp only [teq, Bool.false_eq_true, false_iff]
            intro h
            cases h)
      (fun head args ih ihs b => by
        cases b with
        | atom s2 =>
            simp only [teq, Bool.false_eq_true, false_iff]
            intro h
            cases h
        | form head2 args2 =>
            simp only [teq, Bool.and_eq_true, ih, ihs, Term.form.injEq])
      (fun l2 => by
        cases l2 with
        | nil => simp only [leq]
        | cons y ys =>
            simp only [leq, Bool.false_eq_true, false_iff]
            intro h
            cases h)
      (fun x xs ihx ihxs l2 => by
        cases l2 with
        | nil =>
            simp only [leq, Bool.false_eq_true, false_iff]
            intro h
            cases h
        | cons y ys =>
            simp only [leq, Bool.and_eq_true, ihx, ihxs, List.cons.injEq])
      a

/-- Spelling equality of terms is decidable, from
    decidable equality of symbols alone. -/
instance : DecidableEq (Term Sym) := fun a b =>
  if h : teq a b = true then
    .isTrue ((teqiff a b).mp h)
  else
    .isFalse (fun he => h (by rw [teqiff]; exact he))

/-- The parts of a term: the head and the arguments of a
    form, and nothing for an atom. A function of the
    grammar alone. -/
def parts : Term Sym → List (Term Sym)
  | .atom _ => []
  | .form head args => head :: args

/-- The symbols of a term, as an occurrence list with
    multiplicity: the reading of the term at the minimum
    resolution, where the symbol is the finest grain. -/
def symbols : Term Sym → List Sym
  | .atom name => [name]
  | .form head args => symbols head ++ (args.map symbols).flatten

/-- The trivial scope: an atom, or a form whose head is
    an atom and whose every argument is an atom. -/
def trivial : Term Sym → Bool
  | .atom _ => true
  | .form (.atom _) args =>
      args.all (fun arg => match arg with
        | .atom _ => true
        | _ => false)
  | _ => false

/-- The first order scope: an atom, or a form whose head
    is an atom and whose arguments are first order. The
    recursion over the argument list is spelled through
    the list map and the list test, the form the equation
    compiler takes for a nested recursion; the unfolding
    lemma `firstform` below states the scope in the
    specification's own reading, and the two spellings
    agree on every term. -/
def first : Term Sym → Bool
  | .atom _ => true
  | .form (.atom _) args => (args.map first).all id
  | _ => false

/- The first order scope, unfolded: a form with an atom
   head is first order exactly when every argument is
   first order. -/
omit [DecidableEq Sym] in
theorem firstform (s : Sym) (args : List (Term Sym)) :
    first (form (atom s) args) = true ↔ ∀ x ∈ args, first x = true := by
  simp only [first, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h x hx
    exact h (first x) ⟨x, hx, rfl⟩
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy]
    exact h x hx

/-- The full scope: every term. -/
def full : Term Sym → Bool
  | _ => true

/- Scope nesting, first half: every trivial term is a
   first order term. -/
omit [DecidableEq Sym] in
theorem nest : ∀ t : Term Sym, trivial t = true → first t = true :=
  fun t =>
    Term.rec (motive_1 := fun t => trivial t = true → first t = true)
      (motive_2 := fun l => ∀ x ∈ l, trivial x = true → first x = true)
      (fun s _ => by simp only [first])
      (fun head args ih ihs h => by
        cases head with
        | atom s =>
            rw [firstform]
            intro x hx
            have h2 : args.all (fun arg => match arg with
                | .atom _ => true
                | _ => false) = true := by
              have hh := h
              simp only [trivial] at hh
              exact hh
            have hx2 := (List.all_eq_true.mp h2) x hx
            cases x with
            | atom s2 => simp only [first]
            | form h3 a3 =>
                dsimp only at hx2
                cases hx2
        | form h2 a2 =>
            have hf : trivial (form (form h2 a2) args) = false := by
              simp only [trivial]
            rw [hf] at h
            cases h)
      (fun x hx _ => by cases hx)
      (fun x xs ihx ihxs y hy h => by
        cases hy with
        | head _ => exact ihx h
        | tail _ hm => exact ihxs y hm h)
      t

/- Scope nesting, second half: every first order term
   is in the full scope, which holds of every term. -/
omit [DecidableEq Sym] in
theorem nestfull (t : Term Sym) : full t = true := rfl

end Term

/- ## The one lattice of states (section 4) -/

/-- A state is a finite collection of terms, carried as
    a list and read up to membership. This is the only
    state notion of the model. -/
abbrev State (Sym : Type) := List (Term Sym)

namespace State

variable {Sym : Type}

/-- Two states are the same state when every term of
    each is a member of the other. -/
def same (left right : State Sym) : Prop :=
  ∀ t, t ∈ left ↔ t ∈ right

/-- One state is below another when every term of the
    first is a member of the second. -/
def below (left right : State Sym) : Prop :=
  ∀ t, t ∈ left → t ∈ right

/-- The join of two states is their append, read up to
    membership. The bottom state is the empty list. -/
def join (left right : State Sym) : State Sym := left ++ right

/-- Join is commutative up to state sameness. -/
theorem joincomm (left right : State Sym) :
    same (join left right) (join right left) := by
  intro t
  simp only [join, List.mem_append, or_comm]

/-- Join is associative up to state sameness. -/
theorem joinassoc (one two three : State Sym) :
    same (join (join one two) three) (join one (join two three)) := by
  intro t
  simp only [join, List.mem_append, or_assoc]

/-- Join is idempotent up to state sameness. -/
theorem joinidem (state : State Sym) :
    same (join state state) state := by
  intro t
  simp only [join, List.mem_append, or_self]

/-- Join extends its left part. -/
theorem joinleft (left right : State Sym) :
    below left (join left right) := by
  intro t ht
  exact List.mem_append_left right ht

/-- Join extends its right part. -/
theorem joinright (left right : State Sym) :
    below right (join left right) := by
  intro t ht
  exact List.mem_append_right left ht

/-- Join is the least state above both parts: any state
    above both parts is above the join. -/
theorem joinleast (left right upper : State Sym) :
    below left upper → below right upper →
    below (join left right) upper := by
  intro h1 h2 t ht
  cases List.mem_append.mp ht with
  | inl h => exact h1 t h
  | inr h => exact h2 t h

/-- The bottom state is below every state. -/
theorem bottom (state : State Sym) : below ([] : State Sym) state := by
  intro t ht
  cases ht

end State

/- ## Colors, levels, entries, edges, the graph
      (sections 5, 7, 8, 9) -/

/-- A color is one painted fact on an edge: the painter,
    the kind of coloring scheme, the mark, and the epoch
    at which it was painted. Equality of colors is
    equality of all four fields. -/
structure Color (Sym : Type) where
  who : Sym
  kind : Sym
  mark : Sym
  epoch : Nat
deriving DecidableEq

/-- A level is a named, finite resolved set, with the
    scope it was resolved under. The name is a symbol:
    levels are named inside the model, at symbol grain.
    A level is a value, not a graph. -/
structure Level (Sym : Type) where
  name : Sym
  terms : List (Term Sym)
  scope : Term Sym → Bool

/-- An entry of the log: one resolved fact, appended
    once. The kind names what was resolved, the terms
    are the terms the fact is about, the level is the
    name of the level at which it was resolved, and the
    witness names the ground. -/
structure Entry (Sym : Type) where
  kind : Sym
  terms : List (Term Sym)
  level : Sym
  witness : Sym
deriving DecidableEq

/-- An edge is a finite set of terms, the terms of one
    equivalence class, together with its colors. An edge
    is not a pair and not a transition. -/
structure Edge (Sym : Type) where
  terms : List (Term Sym)
  colors : List (Color Sym)
deriving DecidableEq

/-- The one hypergraph: its edges, its levels, and its
    log. The three fields are the whole graph; there is
    no node list and no separate edge list of pairs. -/
structure Graph (Sym : Type) where
  edges : List (Edge Sym)
  levels : List (Level Sym)
  log : List (Entry Sym)

/-- The four kind symbols of the log and the level free
    name, fixed once by the development and then frozen,
    as section 8.1 directs. The four kinds are pairwise
    distinct; a fifth kind is added only by a change to
    the specification. -/
structure Kinds (Sym : Type) where
  enter : Sym
  join : Sym
  record : Sym
  paint : Sym
  free : Sym
  distinct : enter ≠ join ∧ enter ≠ record ∧ enter ≠ paint ∧
    join ≠ record ∧ join ≠ paint ∧ record ≠ paint

variable {Sym : Type}

/-- A term is collected in a graph when it is a member
    of some edge's term list. -/
def collected (graph : Graph Sym) (term : Term Sym) : Prop :=
  ∃ edge ∈ graph.edges, term ∈ edge.terms

/-- Equivalence: two terms are equivalent in a graph
    exactly when they stand in one edge together. It is
    defined by the graph and by nothing else. -/
def same (graph : Graph Sym) (left right : Term Sym) : Prop :=
  ∃ edge ∈ graph.edges, left ∈ edge.terms ∧ right ∈ edge.terms

/-- One step of a chain: an equivalence entry of the log
    whose terms hold both terms. -/
def step (kinds : Kinds Sym) (log : List (Entry Sym))
    (left right : Term Sym) : Prop :=
  ∃ entry ∈ log, entry.kind = kinds.join ∧
    left ∈ entry.terms ∧ right ∈ entry.terms

/-- A chain of equivalence entries: the transitive
    closure of the step relation over the log. A chain
    has at least one entry; two terms in one edge are
    joined by a chain or are one term, and that pair of
    readings is the exactness invariant below. -/
inductive Chain (kinds : Kinds Sym) (log : List (Entry Sym)) :
    Term Sym → Term Sym → Prop where
  | step : step kinds log left right → Chain kinds log left right
  | trans : Chain kinds log left mid → Chain kinds log mid right →
      Chain kinds log left right

/-- Reachability in the log: joined by a chain of
    equivalence entries, or one and the same term. -/
def reach (kinds : Kinds Sym) (log : List (Entry Sym))
    (left right : Term Sym) : Prop :=
  left = right ∨ Chain kinds log left right

/-- Validity: the invariants of section 5.2, carried as
    a predicate. A value violating one is not a graph of
    this program. Exactness is the two directions of
    invariant 6 stated separately: every pair in one
    edge is joined by a chain or is one term, and every
    pair joined by a chain stands in one edge. -/
structure Valid (kinds : Kinds Sym) (graph : Graph Sym) : Prop where
  nonempty : ∀ edge ∈ graph.edges, edge.terms ≠ []
  nodup : ∀ edge ∈ graph.edges, edge.terms.Nodup
  disjoint : ∀ one ∈ graph.edges, ∀ two ∈ graph.edges,
    ∀ term, term ∈ one.terms → term ∈ two.terms → one = two
  cnodup : ∀ edge ∈ graph.edges, edge.colors.Nodup
  levels : ∀ level ∈ graph.levels, level.terms.Nodup ∧
    ∀ term ∈ level.terms, collected graph term ∧ level.scope term = true
  exactone : ∀ left right, same graph left right →
    reach kinds graph.log left right
  exacttwo : ∀ left right, Chain kinds graph.log left right →
    same graph left right
  edgenodup : graph.edges.Nodup

/-- The empty graph: no edges, no levels, an empty log.
    The start of every construction. -/
def empty : Graph Sym where
  edges := []
  levels := []
  log := []

/-- No chain runs over an empty log: a chain has at
    least one entry, and the empty log has none. -/
theorem chainempty (kinds : Kinds Sym) {left right : Term Sym} :
    ¬ Chain kinds ([] : List (Entry Sym)) left right := by
  intro h
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, _⟩ := hstep
      cases hentry
  | trans _ _ ih1 _ => exact ih1

/-- The empty graph is valid. -/
theorem emptyvalid (kinds : Kinds Sym) : Valid kinds (empty : Graph Sym) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro edge hedge
    cases hedge
  · intro edge hedge
    cases hedge
  · intro one hone
    cases hone
  · intro edge hedge
    cases hedge
  · intro level hlevel
    cases hlevel
  · intro left right h
    obtain ⟨edge, hedge, _⟩ := h
    cases hedge
  · intro left right h
    exact (chainempty kinds h).elim
  · exact List.nodup_nil

/-- Equivalence is reflexive on collected terms. -/
theorem samerefl (graph : Graph Sym) (term : Term Sym) :
    collected graph term → same graph term term := by
  intro h
  obtain ⟨edge, hedge, hterm⟩ := h
  exact ⟨edge, hedge, hterm, hterm⟩

/-- Equivalence is symmetric. -/
theorem samesymm (graph : Graph Sym) {left right : Term Sym} :
    same graph left right → same graph right left := by
  intro h
  obtain ⟨edge, hedge, h1, h2⟩ := h
  exact ⟨edge, hedge, h2, h1⟩

/-- Equivalence is transitive on a valid graph:
    transitivity is the partition invariant read the
    other way, since a term shared by two edges would
    break the partition. -/
theorem sametrans (kinds : Kinds Sym) (graph : Graph Sym)
    (valid : Valid kinds graph) {one two three : Term Sym} :
    same graph one two → same graph two three →
    same graph one three := by
  intro h1 h2
  obtain ⟨e1, he1, h1a, h1b⟩ := h1
  obtain ⟨e2, he2, h2a, h2b⟩ := h2
  have heq := valid.disjoint e1 he1 e2 he2 two h1b h2a
  exact ⟨e1, he1, h1a, heq ▸ h2b⟩

/-- Edges are maximal: a term equivalent to a member of
    an edge is in that edge. The class is the whole
    edge, not a sample of it. -/
theorem samemax (kinds : Kinds Sym) (graph : Graph Sym)
    (valid : Valid kinds graph) {term other : Term Sym}
    (edge : Edge Sym) (hedge : edge ∈ graph.edges) :
    same graph term other → other ∈ edge.terms → term ∈ edge.terms := by
  intro h hother
  obtain ⟨e1, he1, h1, h2⟩ := h
  have heq := valid.disjoint e1 he1 edge hedge other h2 hother
  exact heq ▸ h1

/- ## List facts the development proves for itself -/

namespace Aux

variable {α : Type}

/-- The sum of a list of natural numbers splits over
    append. -/
theorem sumappend (one two : List Nat) :
    (one ++ two).sum = one.sum + two.sum := by
  induction one with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.sum_cons, ih, Nat.add_assoc]

/-- The sum of lengths over an appended edge list, and
    in general of any mapped count, splits over append. -/
theorem mapsumappend (f : α → Nat) (one two : List α) :
    ((one ++ two).map f).sum = (one.map f).sum + (two.map f).sum := by
  rw [List.map_append, sumappend]

/-- A list with no repeated member, read by spelling,
    has length at most the length of any list holding
    all its members. -/
theorem lengthle : ∀ (one two : List α), one.Nodup →
    (∀ x ∈ one, x ∈ two) → one.length ≤ two.length := by
  intro one
  induction one with
  | nil => intro two _ _; exact Nat.zero_le _
  | cons a rest ih =>
      intro two hnodup hsub
      rw [List.nodup_cons] at hnodup
      obtain ⟨ha, hrest⟩ := hnodup
      have ha2 : a ∈ two := hsub a (by simp)
      obtain ⟨s, t, rfl⟩ := List.append_of_mem ha2
      have hsub2 : ∀ x ∈ rest, x ∈ s ++ t := by
        intro x hx
        have hx2 := hsub x (List.mem_cons_of_mem a hx)
        cases List.mem_append.mp hx2 with
        | inl h => exact List.mem_append_left t h
        | inr h =>
            cases List.mem_cons.mp h with
            | inl h =>
                rw [h] at hx
                exact absurd hx ha
            | inr h => exact List.mem_append_right s h
      have hle := ih (s ++ t) hrest hsub2
      simp only [List.length_cons, List.length_append] at hle ⊢
      omega

/-- Two lists with no repeated member and the same
    members have the same length. -/
theorem lengtheq (one two : List α) (h1 : one.Nodup) (h2 : two.Nodup)
    (h : ∀ x, x ∈ one ↔ x ∈ two) : one.length = two.length := by
  apply Nat.le_antisymm
  · exact lengthle one two h1 (fun x hx => (h x).mp hx)
  · exact lengthle two one h2 (fun x hx => (h x).mpr hx)

/-- A list with no repeated member holding two distinct
    members has length at least two. -/
theorem twole : ∀ (list : List α), list.Nodup →
    ∀ a b : α, a ∈ list → b ∈ list → a ≠ b → 2 ≤ list.length := by
  intro list
  induction list with
  | nil => intro _ a b ha _ _; cases ha
  | cons x xs ih =>
      intro hnodup a b ha hb hab
      rw [List.nodup_cons] at hnodup
      obtain ⟨hx, hxs⟩ := hnodup
      cases List.mem_cons.mp ha with
      | inl h =>
          cases List.mem_cons.mp hb with
          | inl h2 => exact absurd (h.trans h2.symm) hab
          | inr h2 =>
              have : 1 ≤ xs.length := by
                cases xs with
                | nil => cases h2
                | cons y ys => simp
              simp only [List.length_cons]
              omega
      | inr h =>
          cases List.mem_cons.mp hb with
          | inl h2 =>
              have : 1 ≤ xs.length := by
                cases xs with
                | nil => cases h
                | cons y ys => simp
              simp only [List.length_cons]
              omega
          | inr h2 =>
              have := ih hxs a b h h2 hab
              simp only [List.length_cons] at this ⊢
              omega

/-- No repeated member in an append, in both
    directions. -/
theorem nodupappend {one two : List α} :
    (one ++ two).Nodup ↔ one.Nodup ∧ two.Nodup ∧
      ∀ x ∈ one, x ∉ two := by
  induction one with
  | nil =>
      simp only [List.nil_append, List.nodup_nil, true_and]
      constructor
      · intro h
        exact ⟨h, fun x hx => by cases hx⟩
      · intro h
        exact h.1
  | cons a rest ih =>
      simp only [List.cons_append, List.nodup_cons, List.mem_append,
        List.mem_cons]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨g1, g2, g3⟩ := ih.mp h2
        refine ⟨⟨?_, g1⟩, g2, ?_⟩
        · intro hcon
          exact h1 (Or.inl hcon)
        · intro x hx hor
          cases hx with
          | inl h =>
              rw [h] at hor
              exact h1 (Or.inr hor)
          | inr hm =>
              exact g3 x hm hor
      · intro h
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        refine ⟨?_, ih.mpr ⟨h2, h3, ?_⟩⟩
        · intro hcon
          cases hcon with
          | inl hc => exact h1 hc
          | inr hc => exact h4 a (by simp) hc
        · intro x hx
          exact h4 x (by simp [hx])

/-- A list that is not empty has length at least one. -/
theorem lengthpos {list : List α} (h : list ≠ []) :
    1 ≤ list.length := by
  cases list with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- When every count is at least one, the total count
    is at least the number of items. -/
theorem sumge (f : α → Nat) : ∀ (list : List α),
    (∀ x ∈ list, 1 ≤ f x) → list.length ≤ (list.map f).sum := by
  intro list
  induction list with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      have h1 := h x (by simp)
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- When every count is exactly one, the total count is
    the number of items. -/
theorem sumone (f : α → Nat) : ∀ (list : List α),
    (∀ x ∈ list, f x = 1) → (list.map f).sum = list.length := by
  intro list
  induction list with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      have h1 := h x (by simp)
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons, h1, h2]
      omega

/-- The sum of a sublist of natural numbers is at most
    the sum of the list. -/
theorem sumsub : ∀ {one two : List Nat},
    one.Sublist two → one.sum ≤ two.sum := by
  intro one two h
  induction h with
  | slnil => simp
  | cons _ _ ih => simp only [List.sum_cons]; omega
  | cons₂ _ _ ih => simp only [List.sum_cons]; omega

/-- Filtering a list never raises the total of a count
    of natural numbers. -/
theorem mapsumfilterle (f : α → Nat) (p : α → Bool)
    (list : List α) :
    ((list.filter p).map f).sum ≤ (list.map f).sum :=
  sumsub (List.Sublist.map f List.filter_sublist)

end Aux

/- ## Redundancy (section 10) -/

/-- The excess of a graph: the count of collected terms
    minus the count of edges, the sum over edges of the
    edge's size minus one. Defined from the graph alone,
    with no list order in it beyond the counts. -/
def excess (graph : Graph Sym) : Nat :=
  (graph.edges.map (fun edge => edge.terms.length)).sum -
    graph.edges.length

/-- A term is redundant in a graph when its edge holds
    at least one other term, distinct from it by
    spelling. Repeat collection of one spelling is
    provenance, not redundancy. -/
def redundant (graph : Graph Sym) (term : Term Sym) : Prop :=
  ∃ other, other ≠ term ∧ same graph term other

/-- The witness form of redundancy: on a valid graph,
    the excess is at least one exactly when some edge
    holds two distinct terms. An explicit pair of
    distinct equivalent expressions is the witness, and
    every witness is such a pair. -/
theorem witness (kinds : Kinds Sym) (graph : Graph Sym)
    (valid : Valid kinds graph) :
    1 ≤ excess graph ↔
      ∃ edge ∈ graph.edges, ∃ one ∈ edge.terms,
        ∃ two ∈ edge.terms, one ≠ two := by
  constructor
  · intro h
    by_cases hcon : ∃ edge ∈ graph.edges, ∃ one ∈ edge.terms,
        ∃ two ∈ edge.terms, one ≠ two
    · exact hcon
    · exfalso
      have hlen : ∀ edge ∈ graph.edges, edge.terms.length = 1 := by
        intro edge hedge
        have hne := valid.nonempty edge hedge
        have hnd := valid.nodup edge hedge
        apply Nat.le_antisymm
        · by_cases hgt : edge.terms.length ≤ 1
          · exact hgt
          · exfalso
            have h2 : 2 ≤ edge.terms.length := by omega
            obtain ⟨x, y, rest, hsplit⟩ : ∃ x y rest,
                edge.terms = x :: y :: rest := by
              cases hterms : edge.terms with
              | nil =>
                  rw [hterms] at hne
                  exact absurd rfl hne
              | cons x xs =>
                  cases hxs : xs with
                  | nil =>
                      rw [hterms, hxs] at h2
                      simp at h2
                  | cons y ys =>
                      exact ⟨x, y, ys, rfl⟩
            have hx : x ∈ edge.terms := by rw [hsplit]; simp
            have hy : y ∈ edge.terms := by rw [hsplit]; simp
            have hxy : x ≠ y := by
              rw [hsplit] at hnd
              rw [List.nodup_cons] at hnd
              intro heq
              apply hnd.1
              rw [heq]
              simp
            exact hcon ⟨edge, hedge, x, hx, y, hy, hxy⟩
        · exact Aux.lengthpos hne
      have hsum := Aux.sumone (fun edge => edge.terms.length)
        graph.edges hlen
      simp only [excess, hsum] at h
      omega
  · intro h
    obtain ⟨edge, hedge, one, hone, two, htwo, hne⟩ := h
    have h2 := Aux.twole edge.terms (valid.nodup edge hedge)
      one two hone htwo hne
    have hge := Aux.sumge (fun e => e.terms.length) graph.edges
      (fun x hx => Aux.lengthpos (valid.nonempty x hx))
    obtain ⟨s, t, hsplit⟩ := List.append_of_mem hedge
    have hsum : (graph.edges.map (fun e => e.terms.length)).sum =
        (s.map (fun e => e.terms.length)).sum + edge.terms.length +
          (t.map (fun e => e.terms.length)).sum := by
      rw [hsplit]
      simp only [List.map_append, List.map_cons, Aux.sumappend,
        List.sum_cons]
      omega
    have hs := Aux.sumge (fun e => e.terms.length) s
      (fun x hx => Aux.lengthpos (valid.nonempty x
        (hsplit ▸ List.mem_append_left (edge :: t) hx)))
    have ht := Aux.sumge (fun e => e.terms.length) t
      (fun x hx => Aux.lengthpos (valid.nonempty x
        (hsplit ▸ List.mem_append_right s
          (List.mem_cons_of_mem edge hx))))
    have hlen2 : graph.edges.length = s.length + 1 + t.length := by
      rw [hsplit]
      simp only [List.length_append, List.length_cons]
      omega
    simp only [excess, hsum, hlen2]
    omega

/- ## The bound and the view (section 7) -/

/-- The finite resolved upper bound of a level in a
    graph: the state of all terms equivalent in the
    graph to a member of the level's state, read as the
    union, in list form, of the edges the level's terms
    stand in. A bound is a lattice join of singletons,
    saturated under the graph's equivalence, or it is
    not a bound of this model. -/
def bound [DecidableEq Sym] (graph : Graph Sym) (level : Level Sym) :
    List (Term Sym) :=
  (graph.edges.filter (fun edge =>
    edge.terms.any (fun term => decide (term ∈ level.terms))))
    |>.flatMap (fun edge => edge.terms)

/-- The view of a graph at a level: the list of the
    graph's edges that meet the level's bound, each edge
    whole. A view is a derived value, never a graph, and
    is determined by the graph and the level alone. -/
def view [DecidableEq Sym] (graph : Graph Sym) (level : Level Sym) :
    List (Edge Sym) :=
  graph.edges.filter (fun edge =>
    edge.terms.any (fun term => decide (term ∈ bound graph level)))

/-- A state is saturated under a graph's equivalence
    when it holds every term equivalent to one of its
    members. -/
def saturated (graph : Graph Sym) (state : List (Term Sym)) : Prop :=
  ∀ one ∈ state, ∀ two, same graph one two → two ∈ state

/-- The level's state is below its bound, in the lattice
    order, whenever the level's terms are collected:
    every term of the level stands in an edge that meets
    the level, namely its own. -/
theorem boundabove [DecidableEq Sym] (graph : Graph Sym)
    (level : Level Sym) :
    ∀ term ∈ level.terms, collected graph term →
      term ∈ bound graph level := by
  intro term hterm hcol
  obtain ⟨edge, hedge, hinte⟩ := hcol
  simp only [bound, List.mem_flatMap, List.mem_filter]
  refine ⟨edge, ⟨hedge, ?_⟩, hinte⟩
  simp only [List.any_eq_true]
  exact ⟨term, hinte, by simp [hterm]⟩

/-- The bound is saturated: it is closed under the
    graph's equivalence, on a valid graph, where the
    partition puts every term equivalent to a member of
    a bound edge in that same edge. -/
theorem boundsat (kinds : Kinds Sym) [DecidableEq Sym]
    (graph : Graph Sym) (valid : Valid kinds graph)
    (level : Level Sym) :
    saturated graph (bound graph level) := by
  intro one hone two hsame
  simp only [bound, List.mem_flatMap, List.mem_filter] at hone
  obtain ⟨e1, he1f, h1⟩ := hone
  obtain ⟨e2, he2, h2a, h2b⟩ := hsame
  have heq := valid.disjoint e1 he1f.1 e2 he2 one h1 h2a
  simp only [bound, List.mem_flatMap, List.mem_filter]
  exact ⟨e1, ⟨he1f.1, he1f.2⟩, heq ▸ h2b⟩

/-- The bound is the least saturated state above the
    level's state: any saturated state holding the
    level's terms holds the bound. -/
theorem boundleast [DecidableEq Sym] (graph : Graph Sym)
    (level : Level Sym) (state : List (Term Sym))
    (hsat : saturated graph state)
    (habove : ∀ term ∈ level.terms, term ∈ state) :
    ∀ term ∈ bound graph level, term ∈ state := by
  intro term hterm
  simp only [bound, List.mem_flatMap, List.mem_filter] at hterm
  obtain ⟨edge, hedgef, hinte⟩ := hterm
  rw [List.any_eq_true] at hedgef
  obtain ⟨other, hother, hdec⟩ := hedgef.2
  have hother2 : other ∈ level.terms := by
    have := of_decide_eq_true hdec
    exact this
  exact hsat other (habove other hother2) term
    ⟨edge, hedgef.1, hother, hinte⟩

/-- The bound is finite, with its size bounded by the
    total size of the graph's edges: finiteness is a
    conclusion of what a level and a graph are, a finite
    list of finite lists, and is stated nowhere as a
    hypothesis. -/
theorem boundfin [DecidableEq Sym] (graph : Graph Sym)
    (level : Level Sym) :
    (bound graph level).length ≤
      (graph.edges.map (fun edge => edge.terms.length)).sum := by
  simp only [bound, List.length_flatMap]
  exact Aux.mapsumfilterle (α := Edge Sym)
    (fun edge => edge.terms.length) _ _

/- ## Color union (section 9) -/

/-- The union of two color lists, up to membership: the
    composition of colorings on an edge. -/
def union [DecidableEq Sym] (one two : List (Color Sym)) :
    List (Color Sym) :=
  one ++ two.filter (fun color => !(decide (color ∈ one)))

/-- Membership in a color union is membership in one of
    the two lists. -/
theorem memunion [DecidableEq Sym] (one two : List (Color Sym))
    (color : Color Sym) :
    color ∈ union one two ↔ color ∈ one ∨ color ∈ two := by
  simp only [union, List.mem_append, List.mem_filter]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
        obtain ⟨h1, h2⟩ := h
        exact Or.inr h1
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
        by_cases hc : color ∈ one
        · exact Or.inl hc
        · exact Or.inr ⟨h, by simp [hc]⟩

/-- A union of two lists with no repeated member has no
    repeated member. -/
theorem unionnodup [DecidableEq Sym] (one two : List (Color Sym))
    (h1 : one.Nodup) (h2 : two.Nodup) :
    (union one two).Nodup := by
  simp only [union, Aux.nodupappend]
  refine ⟨h1, List.Sublist.nodup List.filter_sublist h2, ?_⟩
  intro x hx hcon
  rw [List.mem_filter] at hcon
  obtain ⟨_, hdec⟩ := hcon
  have hdec2 : (!(decide (x ∈ one))) = true := hdec
  have hd : decide (x ∈ one) = true := decide_eq_true_iff.mpr hx
  rw [hd] at hdec2
  exact Bool.noConfusion hdec2
