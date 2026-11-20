import Core

/-! # Registry

    Section 11 of the spec: the registry that
    accompanies the one graph. A configuration is a
    view — a list of edges — taken up to the
    configuration equivalence: same edges up to
    membership, edge by edge the same terms and the
    same colors up to membership. The registry is an
    append only list of entries, one per unique
    witnessed configuration, each holding its
    provenance and its colors as epoch and score
    pairs. The coloring is deterministic: the score
    is a weighted sum over five fixed content
    measures, a function of content alone. Epochs are
    appended schemes; reweighting is only an epoch
    append. -/

variable {Sym : Type}

/- ## The distinct list

    The distinct members of a list, keeping one copy
    of each: membership is the list's membership, and
    the result is repeat free. -/

/-- The distinct members of a list. -/
def distinct [DecidableEq Sym] : List Sym → List Sym
  | [] => []
  | s :: ss => if s ∈ distinct ss then distinct ss
    else s :: distinct ss

/-- Membership in the distinct list is membership in
    the list. -/
theorem memdistinct [DecidableEq Sym] (x : Sym) :
    ∀ (l : List Sym), x ∈ distinct l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons a as ih =>
      by_cases h : a ∈ distinct as
      · have hdef : distinct (a :: as) = distinct as := by
          simp only [distinct, h, ↓reduceIte]
        rw [hdef]
        constructor
        · intro hx
          exact List.mem_cons_of_mem a (ih.mp hx)
        · intro hx
          cases List.mem_cons.mp hx with
          | inl hx => subst hx; exact h
          | inr hx => exact ih.mpr hx
      · have hdef : distinct (a :: as) =
            a :: distinct as := by
          simp only [distinct, h, ↓reduceIte]
        rw [hdef]
        simp only [List.mem_cons, ih]

/-- The distinct list is repeat free. -/
theorem nodupdistinct [DecidableEq Sym] :
    ∀ (l : List Sym), (distinct l).Nodup := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons a as ih =>
      by_cases h : a ∈ distinct as
      · simp only [distinct, h, ↓reduceIte]
        exact ih
      · simp only [distinct, h, ↓reduceIte]
        exact List.nodup_cons.mpr ⟨h, ih⟩

/- ## The five measures

    Fixed by the spec: term count, edge count,
    excess, colored edge count, distinct symbol
    count — each a natural read off the view's
    content alone. -/

/-- The term count of a configuration. -/
def mterms (c : List (Edge Sym)) : Nat :=
  (c.map (fun e => e.terms.length)).sum

/-- The edge count of a configuration. -/
def medges (c : List (Edge Sym)) : Nat := c.length

/-- The excess of a configuration: its terms minus
    its edges, the section ten reading of the view's
    edges as a graph fragment. -/
def mexcess (c : List (Edge Sym)) : Nat :=
  mterms c - medges c

/-- The colored edge count: edges holding at least
    one color. -/
def mcolored [DecidableEq Sym] (c : List (Edge Sym)) : Nat :=
  (c.map (fun e => if e.colors = [] then 0 else 1)).sum

/-- The distinct symbol count: the symbols of the
    view's terms, up to membership. -/
def msymbols [DecidableEq Sym] (c : List (Edge Sym)) :
    Nat :=
  (distinct (c.flatMap
    (fun e => e.terms.flatMap Term.symbols))).length

/-- The fixed measure names. -/
inductive Mname where
  /-- The term count. -/
  | terms
  /-- The edge count. -/
  | edges
  /-- The excess. -/
  | excess
  /-- The colored edge count. -/
  | colored
  /-- The distinct symbol count. -/
  | symbols
deriving DecidableEq

/-- A measure by its name. -/
def measureof [DecidableEq Sym] (name : Mname)
    (c : List (Edge Sym)) : Nat :=
  match name with
  | .terms => mterms c
  | .edges => medges c
  | .excess => mexcess c
  | .colored => mcolored c
  | .symbols => msymbols c

/-- A coloring scheme: a weights record over the
    fixed measure list. -/
abbrev Scheme := List (Mname × Nat)

/-- The score of a configuration under a scheme: the
    sum over the scheme of weight times measure. The
    color of the configuration under the scheme is
    this score. -/
def score [DecidableEq Sym] (scheme : Scheme)
    (c : List (Edge Sym)) : Nat :=
  (scheme.map (fun p => p.2 * measureof p.1 c)).sum

/- ## Configuration equivalence

    Two edges are the same edge of a configuration
    when their terms agree up to membership and their
    colors agree up to membership. Two configurations
    are equivalent when their edges match both ways. -/

/-- Edge sameness up to membership, terms and
    colors. -/
def sameedge (e₁ e₂ : Edge Sym) : Prop :=
  (∀ t ∈ e₁.terms, t ∈ e₂.terms) ∧
    (∀ t ∈ e₂.terms, t ∈ e₁.terms) ∧
    (∀ c ∈ e₁.colors, c ∈ e₂.colors) ∧
    (∀ c ∈ e₂.colors, c ∈ e₁.colors)

/-- Edge sameness, as a boolean test. -/
def sameb [DecidableEq Sym] (e₁ e₂ : Edge Sym) : Bool :=
  (e₁.terms.all (fun t => decide (t ∈ e₂.terms))) &&
    (e₂.terms.all (fun t => decide (t ∈ e₁.terms))) &&
    (e₁.colors.all (fun c => decide (c ∈ e₂.colors))) &&
    (e₂.colors.all (fun c => decide (c ∈ e₁.colors)))

/-- The boolean test reads edge sameness. -/
theorem samebiff [DecidableEq Sym] (e₁ e₂ : Edge Sym) :
    sameb e₁ e₂ = true ↔ sameedge e₁ e₂ := by
  simp only [sameb, sameedge, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-- Configuration equivalence: edges match both
    ways, edge by edge the same up to membership. -/
def ceq (c₁ c₂ : List (Edge Sym)) : Prop :=
  (∀ e ∈ c₁, ∃ e' ∈ c₂, sameedge e e') ∧
    (∀ e ∈ c₂, ∃ e' ∈ c₁, sameedge e e')

/-- Configuration equivalence, as a boolean test. -/
def ceqb [DecidableEq Sym] (c₁ c₂ : List (Edge Sym)) :
    Bool :=
  (c₁.all (fun e => c₂.any (fun e' => sameb e e'))) &&
    (c₂.all (fun e => c₁.any (fun e' => sameb e e')))

/-- The boolean test reads configuration
    equivalence. -/
theorem ceqbiff [DecidableEq Sym]
    (c₁ c₂ : List (Edge Sym)) :
    ceqb c₁ c₂ = true ↔ ceq c₁ c₂ := by
  simp only [ceqb, ceq, List.all_eq_true,
    List.any_eq_true, Bool.and_eq_true, samebiff]

/-- Edge sameness is reflexive. -/
theorem sameedgerefl (e : Edge Sym) : sameedge e e :=
  ⟨fun _ ht => ht, fun _ ht => ht, fun _ hc => hc,
    fun _ hc => hc⟩

/-- Configuration equivalence is reflexive. -/
theorem ceqrefl (c : List (Edge Sym)) : ceq c c :=
  ⟨fun e he => ⟨e, he, sameedgerefl e⟩,
    fun e he => ⟨e, he, sameedgerefl e⟩⟩

/-- Edge sameness is symmetric. -/
theorem sameedgesymm {e₁ e₂ : Edge Sym}
    (h : sameedge e₁ e₂) : sameedge e₂ e₁ :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- Configuration equivalence is symmetric. -/
theorem ceqsymm {c₁ c₂ : List (Edge Sym)}
    (h : ceq c₁ c₂) : ceq c₂ c₁ :=
  ⟨h.2, h.1⟩

/-- Edge sameness is transitive. -/
theorem sameedgetrans {e₁ e₂ e₃ : Edge Sym}
    (h₁ : sameedge e₁ e₂) (h₂ : sameedge e₂ e₃) :
    sameedge e₁ e₃ :=
  ⟨fun t ht => h₂.1 t (h₁.1 t ht),
    fun t ht => h₁.2.1 t (h₂.2.1 t ht),
    fun c hc => h₂.2.2.1 c (h₁.2.2.1 c hc),
    fun c hc => h₁.2.2.2 c (h₂.2.2.2 c hc)⟩

/-- Configuration equivalence is transitive. -/
theorem ceqtrans {c₁ c₂ c₃ : List (Edge Sym)}
    (h₁ : ceq c₁ c₂) (h₂ : ceq c₂ c₃) : ceq c₁ c₃ :=
  ⟨fun e he => by
    obtain ⟨e', he', hs⟩ := h₁.1 e he
    obtain ⟨e'', he'', hs'⟩ := h₂.1 e' he'
    exact ⟨e'', he'', sameedgetrans hs hs'⟩,
    fun e he => by
    obtain ⟨e', he', hs⟩ := h₂.2 e he
    obtain ⟨e'', he'', hs'⟩ := h₁.2 e' he'
    exact ⟨e'', he'', sameedgetrans hs hs'⟩⟩

/-- A configuration is well formed when its edges are
    nonempty, repeat free in terms and colors, the
    edge list is repeat free, and its edges are
    pairwise disjoint in terms — the section five
    invariants of the view's edges. -/
def wellformed (c : List (Edge Sym)) : Prop :=
  (∀ e ∈ c, e.terms ≠ [] ∧ e.terms.Nodup ∧
    e.colors.Nodup) ∧ c.Nodup ∧
    (∀ e₁ ∈ c, ∀ e₂ ∈ c, ∀ t ∈ e₁.terms,
      t ∈ e₂.terms → e₁ = e₂)

/- ## Matching lemmas

    Counting over matched lists: when every member of
    one repeat free list is matched in the other, and
    matches are unique, the first list is no longer;
    and sums of class functions over matched lists
    agree. -/

/-- Length under a unique matching. -/
theorem matchle {α β : Type} (R : α → β → Prop) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.Nodup →
      (∀ x ∈ l₁, ∃ y ∈ l₂, R x y) →
      (∀ y ∈ l₂, ∀ x₁ ∈ l₁, ∀ x₂ ∈ l₁,
        R x₁ y → R x₂ y → x₁ = x₂) →
      l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _ _; exact Nat.zero_le _
  | cons x xs ih =>
      intro l₂ hnodup hforth huniq
      obtain ⟨y, hy, hR⟩ := hforth x (by simp)
      obtain ⟨l₂₁, l₂₂, hl₂⟩ := List.append_of_mem hy
      have hlen : l₂.length = (l₂₁ ++ l₂₂).length + 1 := by
        rw [hl₂]
        simp only [List.length_append, List.length_cons]
        omega
      have hxs : xs.Nodup := (List.nodup_cons.mp
        hnodup).2
      have hxnot : x ∉ xs := (List.nodup_cons.mp
        hnodup).1
      have hmemrest : ∀ y' ∈ l₂₁ ++ l₂₂, y' ∈ l₂ := by
        intro y' hy'
        rw [hl₂]
        cases List.mem_append.mp hy' with
        | inl h => exact List.mem_append_left _ h
        | inr h => exact List.mem_append_right _ (List.mem_cons_of_mem y h)
      have hle := ih (l₂₁ ++ l₂₂) hxs
        (fun x' hx' => by
          obtain ⟨y', hy', hR'⟩ := hforth x'
            (List.mem_cons_of_mem x hx')
          have hyne : y' ≠ y := by
            intro heq
            apply hxnot
            have hxx : x = x' := huniq y hy x (by simp)
              x' (List.mem_cons_of_mem x hx') hR
              (heq ▸ hR')
            rw [← hxx] at hx'
            exact hx'
          refine ⟨y', ?_, hR'⟩
          rw [hl₂] at hy'
          cases List.mem_append.mp hy' with
          | inl h => exact List.mem_append_left _ h
          | inr h =>
              cases List.mem_cons.mp h with
              | inl h => exact absurd h hyne
              | inr h => exact List.mem_append_right _ h)
        (fun y' hy' x₁ hx₁ x₂ hx₂ h1 h2 => huniq y'
          (hmemrest y' hy')
          x₁ (List.mem_cons_of_mem x hx₁)
          x₂ (List.mem_cons_of_mem x hx₂) h1 h2)
      rw [List.length_cons]
      omega

/-- Sums under a two way unique matching, of
    functions agreeing on matched pairs. -/
theorem summatch {α β : Type} (R : α → β → Prop)
    (f : α → Nat) (g : β → Nat) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.Nodup →
      l₂.Nodup →
      (∀ x ∈ l₁, ∃ y ∈ l₂, R x y) →
      (∀ y ∈ l₂, ∃ x ∈ l₁, R x y) →
      (∀ y ∈ l₂, ∀ x₁ ∈ l₁, ∀ x₂ ∈ l₁,
        R x₁ y → R x₂ y → x₁ = x₂) →
      (∀ x ∈ l₁, ∀ y₁ ∈ l₂, ∀ y₂ ∈ l₂,
        R x y₁ → R x y₂ → y₁ = y₂) →
      (∀ x ∈ l₁, ∀ y ∈ l₂, R x y → f x = g y) →
      (l₁.map f).sum = (l₂.map g).sum := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ _ hback _ _ _
      cases l₂ with
      | nil => rfl
      | cons y ys =>
          obtain ⟨x, hx, -⟩ := hback y (by simp)
          cases hx
  | cons x xs ih =>
      intro l₂ hnodup hnodup2 hforth hback huniq huniq2
        hfg
      obtain ⟨y, hy, hR⟩ := hforth x (by simp)
      obtain ⟨l₂₁, l₂₂, hl₂⟩ := List.append_of_mem hy
      have hfy : f x = g y := hfg x (by simp) y hy hR
      have hsum : (l₂.map g).sum =
          ((l₂₁ ++ l₂₂).map g).sum + g y := by
        rw [hl₂]
        simp only [List.map_append, Aux.sumappend,
          List.map_cons, List.sum_cons]
        omega
      have hxs : xs.Nodup := (List.nodup_cons.mp
        hnodup).2
      have hxnot : x ∉ xs := (List.nodup_cons.mp
        hnodup).1
      have hnoduprest : (l₂₁ ++ l₂₂).Nodup := by
        have h : (l₂₁ ++ y :: l₂₂).Nodup := hl₂ ▸ hnodup2
        obtain ⟨h₁, h₂, hdis⟩ := Aux.nodupappend.mp h
        rw [List.nodup_cons] at h₂
        apply Aux.nodupappend.mpr
        refine ⟨h₁, h₂.2, fun x hx hxl => ?_⟩
        exact hdis x hx (List.mem_cons_of_mem y hxl)
      have hmemrest : ∀ y' ∈ l₂₁ ++ l₂₂, y' ∈ l₂ := by
        intro y' hy'
        rw [hl₂]
        cases List.mem_append.mp hy' with
        | inl h => exact List.mem_append_left _ h
        | inr h => exact List.mem_append_right _ (List.mem_cons_of_mem y h)
      have hrest := ih (l₂₁ ++ l₂₂) hxs hnoduprest
        (fun x' hx' => by
          obtain ⟨y', hy', hR'⟩ := hforth x'
            (List.mem_cons_of_mem x hx')
          have hyne : y' ≠ y := by
            intro heq
            apply hxnot
            have hxx : x = x' := huniq y hy x (by simp)
              x' (List.mem_cons_of_mem x hx') hR
              (heq ▸ hR')
            rw [← hxx] at hx'
            exact hx'
          refine ⟨y', ?_, hR'⟩
          rw [hl₂] at hy'
          cases List.mem_append.mp hy' with
          | inl h => exact List.mem_append_left _ h
          | inr h =>
              cases List.mem_cons.mp h with
              | inl h => exact absurd h hyne
              | inr h => exact List.mem_append_right _ h)
        (fun y' hy' => by
          have hy'2 : y' ∈ l₂ := hmemrest y' hy'
          obtain ⟨x', hx', hR'⟩ := hback y' hy'2
          have hxne : x' ≠ x := by
            intro heq
            have hyyeq : y' = y := huniq2 x (by simp) y'
              hy'2 y hy (heq ▸ hR') hR
            have hthis : y ∈ l₂₁ ++ l₂₂ := hyyeq ▸ hy'
            have hdis : y ∉ l₂₁ ++ l₂₂ := by
              have h : (l₂₁ ++ y :: l₂₂).Nodup :=
                hl₂ ▸ hnodup2
              obtain ⟨h₁, h₂, hdis0⟩ :=
                Aux.nodupappend.mp h
              rw [List.nodup_cons] at h₂
              intro hmem
              cases List.mem_append.mp hmem with
              | inl hm => exact hdis0 y hm (by simp)
              | inr hm => exact h₂.1 hm
            exact hdis hthis
          cases List.mem_cons.mp hx' with
          | inl h => exact absurd h hxne
          | inr h => exact ⟨x', h, hR'⟩)
        (fun y' hy' x₁ hx₁ x₂ hx₂ h1 h2 => huniq y'
          (hmemrest y' hy')
          x₁ (List.mem_cons_of_mem x hx₁)
          x₂ (List.mem_cons_of_mem x hx₂) h1 h2)
        (fun x' hx' y₁ hy₁ y₂ hy₂ h1 h2 => huniq2 x'
          (List.mem_cons_of_mem x hx')
          y₁ (hmemrest y₁ hy₁)
          y₂ (hmemrest y₂ hy₂) h1 h2)
        (fun x' hx' y' hy' hR' => hfg x'
          (List.mem_cons_of_mem x hx') y'
          (hmemrest y' hy') hR')
      rw [List.map_cons, List.sum_cons, hfy, hsum,
        hrest]
      omega

/- ## Determinism

    The measures are functions of content alone: on
    well formed configurations, equivalent
    configurations have all five measures equal, so
    every scheme gives them the same score. -/

/-- The matching uniqueness facts for edges of well
    formed configurations: an edge of one is matched
    by at most one edge of the other, because matched
    edges share the first edge's terms and the other
    configuration is disjoint. -/
theorem edgeuniq {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (y : Edge Sym) (hy : y ∈ c₂)
    (x₁ : Edge Sym) (hx₁ : x₁ ∈ c₁)
    (x₂ : Edge Sym) (hx₂ : x₂ ∈ c₁)
    (h₁ : sameedge x₁ y) (h₂ : sameedge x₂ y) :
    x₁ = x₂ := by
  obtain ⟨hne, -, -⟩ := hw₂.1 y hy
  obtain ⟨t, ht⟩ : ∃ t, t ∈ y.terms := by
    cases hterms : y.terms with
    | nil => exact absurd hterms hne
    | cons t ts => exact ⟨t, by simp [hterms]⟩
  exact hw₁.2.2 x₁ hx₁ x₂ hx₂ t (h₁.2.1 t ht)
    (h₂.2.1 t ht)

/-- Determinism, edge count. -/
theorem medgeseq {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (h : ceq c₁ c₂) : medges c₁ = medges c₂ := by
  show c₁.length = c₂.length
  have h1 : c₁.length ≤ c₂.length :=
    matchle sameedge c₁ c₂ hw₁.2.1 h.1
      (fun y hy x₁ hx₁ x₂ hx₂ h₁ h₂ =>
        edgeuniq hw₁ hw₂ y hy x₁ hx₁ x₂ hx₂ h₁ h₂)
  have h2 : c₂.length ≤ c₁.length :=
    matchle sameedge c₂ c₁ hw₂.2.1 h.2
      (fun y hy x₁ hx₁ x₂ hx₂ h₁ h₂ =>
        edgeuniq hw₂ hw₁ y hy x₁ hx₁ x₂ hx₂ h₁ h₂)
  omega

/-- Determinism, term count. -/
theorem mtermseq {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (h : ceq c₁ c₂) : mterms c₁ = mterms c₂ := by
  apply summatch sameedge (fun e => e.terms.length)
    (fun e => e.terms.length) c₁ c₂ hw₁.2.1 hw₂.2.1
    h.1 (fun e he => by
      obtain ⟨e', he', hs⟩ := h.2 e he
      exact ⟨e', he', sameedgesymm hs⟩)
  · exact fun y hy x₁ hx₁ x₂ hx₂ h₁ h₂ =>
      edgeuniq hw₁ hw₂ y hy x₁ hx₁ x₂ hx₂ h₁ h₂
  · exact fun x hx y₁ hy₁ y₂ hy₂ h₁ h₂ =>
      edgeuniq hw₂ hw₁ x hx y₁ hy₁ y₂ hy₂
        (sameedgesymm h₁) (sameedgesymm h₂)
  · intro x hx y hy hxy
    exact Aux.lengtheq _ _ (hw₁.1 x hx).2.1
      (hw₂.1 y hy).2.1
      (fun t => ⟨fun ht => hxy.1 t ht,
        fun ht => hxy.2.1 t ht⟩)

/-- Determinism, colored edge count. -/
theorem mcoloredeq [DecidableEq Sym] {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (h : ceq c₁ c₂) : mcolored c₁ = mcolored c₂ := by
  apply summatch sameedge
    (fun e => if e.colors = [] then 0 else 1)
    (fun e => if e.colors = [] then 0 else 1)
    c₁ c₂ hw₁.2.1 hw₂.2.1
    h.1 (fun e he => by
      obtain ⟨e', he', hs⟩ := h.2 e he
      exact ⟨e', he', sameedgesymm hs⟩)
  · exact fun y hy x₁ hx₁ x₂ hx₂ h₁ h₂ =>
      edgeuniq hw₁ hw₂ y hy x₁ hx₁ x₂ hx₂ h₁ h₂
  · exact fun x hx y₁ hy₁ y₂ hy₂ h₁ h₂ =>
      edgeuniq hw₂ hw₁ x hx y₁ hy₁ y₂ hy₂
        (sameedgesymm h₁) (sameedgesymm h₂)
  · intro x hx y hy hxy
    by_cases hx0 : x.colors = []
    · have hy0 : y.colors = [] := by
        cases hyc : y.colors with
        | nil => rfl
        | cons c cs =>
            have hc : c ∈ x.colors :=
              hxy.2.2.2 c (by simp [hyc])
            rw [hx0] at hc
            cases hc
      simp only [hx0, hy0, ↓reduceIte]
    · have hy0 : y.colors ≠ [] := by
        intro hy0
        apply hx0
        cases hxc : x.colors with
        | nil => rfl
        | cons c cs =>
            have hc : c ∈ y.colors :=
              hxy.2.2.1 c (by simp [hxc])
            rw [hy0] at hc
            cases hc
      simp only [hx0, hy0, ↓reduceIte]

/-- Determinism, distinct symbol count: the symbols
    occurring in one configuration are exactly those
    occurring in the other, since matched edges hold
    the same terms. -/
theorem msymbolseq [DecidableEq Sym]
    {c₁ c₂ : List (Edge Sym)}
    (h : ceq c₁ c₂) : msymbols c₁ = msymbols c₂ := by
  apply Aux.lengtheq _ _ (nodupdistinct _)
    (nodupdistinct _)
  intro s
  constructor
  · intro hs
    rw [memdistinct, List.mem_flatMap] at hs
    rw [memdistinct, List.mem_flatMap]
    obtain ⟨e, he, hs⟩ := hs
    rw [List.mem_flatMap] at hs
    obtain ⟨t, ht, hst⟩ := hs
    obtain ⟨e', he', hse⟩ := h.1 e he
    exact ⟨e', he', List.mem_flatMap.mpr
      ⟨t, hse.1 t ht, hst⟩⟩
  · intro hs
    rw [memdistinct, List.mem_flatMap] at hs
    rw [memdistinct, List.mem_flatMap]
    obtain ⟨e, he, hs⟩ := hs
    rw [List.mem_flatMap] at hs
    obtain ⟨t, ht, hst⟩ := hs
    obtain ⟨e', he', hse⟩ := h.2 e he
    exact ⟨e', he', List.mem_flatMap.mpr
      ⟨t, hse.1 t ht, hst⟩⟩

/-- Determinism: every measure of the five agrees on
    equivalent well formed configurations. -/
theorem measureeq [DecidableEq Sym]
    {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (h : ceq c₁ c₂) (name : Mname) :
    measureof name c₁ = measureof name c₂ := by
  cases name with
  | terms => exact mtermseq hw₁ hw₂ h
  | edges => exact medgeseq hw₁ hw₂ h
  | excess =>
      have ht := mtermseq hw₁ hw₂ h
      have he := medgeseq hw₁ hw₂ h
      simp only [measureof, mexcess, ht, he]
  | colored => exact mcoloredeq hw₁ hw₂ h
  | symbols => exact msymbolseq h

/-- Determinism of the color: equivalent well formed
    configurations have the same score under every
    scheme — two witnessings of one configuration
    under one scheme have the same color. -/
theorem scoreeq [DecidableEq Sym]
    {c₁ c₂ : List (Edge Sym)}
    (hw₁ : wellformed c₁) (hw₂ : wellformed c₂)
    (h : ceq c₁ c₂) (scheme : Scheme) :
    score scheme c₁ = score scheme c₂ := by
  induction scheme with
  | nil => rfl
  | cons p ps ih =>
      have hm : measureof p.1 c₁ = measureof p.1 c₂ :=
        measureeq hw₁ hw₂ h p.1
      show p.2 * measureof p.1 c₁ + score ps c₁ =
        p.2 * measureof p.1 c₂ + score ps c₂
      rw [hm, ih]

/- ## The registry

    A witness is a graph pin, a level, and an epoch.
    An entry holds a configuration, its provenance
    (the witnessings, in append order), and its
    colors as epoch and score pairs. The registry is
    the append only list of entries together with the
    append only list of epochs; epoch zero is the
    founding scheme. -/

/-- A witnessing: a graph pin, a level, an epoch. -/
structure Witness (Sym : Type) where
  /-- The graph pin. -/
  pin : Sym
  /-- The level at which it was witnessed. -/
  level : Sym
  /-- The epoch under which it was witnessed. -/
  epoch : Nat
deriving DecidableEq

/-- A registry entry: a configuration, its
    provenance, its colors as epoch and score
    pairs. -/
structure EntryR (Sym : Type) where
  /-- The configuration. -/
  config : List (Edge Sym)
  /-- The provenance: its witnessings, in append
      order. -/
  prov : List (Witness Sym)
  /-- The colors: epoch and score pairs, in append
      order. -/
  colors : List (Nat × Nat)
deriving DecidableEq

/-- The registry: entries and epochs, both append
    only. -/
structure Registry (Sym : Type) where
  /-- The entries, one per unique witnessed
      configuration. -/
  entries : List (EntryR Sym)
  /-- The epochs: appended schemes, numbered from
      zero in append order. -/
  epochs : List Scheme

/-- The founding of a registry under a scheme: no
    entries, and the scheme as epoch zero. -/
def founding (scheme : Scheme) : Registry Sym :=
  ⟨[], [scheme]⟩

/-- The scheme of an epoch, empty if there is no
    such epoch. -/
def schemeat (r : Registry Sym) (n : Nat) : Scheme :=
  (r.epochs[n]?).getD []

/-- A reweighting is exactly an epoch append: it
    edits no prior epoch and no entry. -/
def newepoch (r : Registry Sym) (s : Scheme) :
    Registry Sym :=
  ⟨r.entries, r.epochs ++ [s]⟩

/-- An epoch append keeps every entry. -/
theorem newepochentries (r : Registry Sym)
    (s : Scheme) :
    (newepoch r s).entries = r.entries := rfl

/-- An epoch append appends exactly one epoch. -/
theorem newepochepochs (r : Registry Sym)
    (s : Scheme) :
    (newepoch r s).epochs = r.epochs ++ [s] := rfl

/-- Earlier epochs are untouched by an epoch append:
    the scheme at any earlier number is the same
    before and after. -/
theorem schemeatnewepoch (r : Registry Sym)
    (s : Scheme) (n : Nat) (hn : n < r.epochs.length) :
    schemeat (newepoch r s) n = schemeat r n := by
  simp only [schemeat, newepoch, List.getElem?_append,
    hn, ↓reduceIte]

/-- The entry update of a witnessing: provenance
    grows by the witness; the color list grows by
    the epoch and score pair exactly when no pair of
    that epoch stands yet — pairs under earlier
    epochs stand. -/
def updentry (e : EntryR Sym) (w : Witness Sym)
    (sc : Nat) : EntryR Sym :=
  ⟨e.config, e.prov ++ [w],
    if e.colors.any (fun p => p.1 = w.epoch)
      then e.colors
      else e.colors ++ [(w.epoch, sc)]⟩

/-- Updating every entry whose configuration is
    equivalent to the witnessed one. Under the
    registry invariant there is at most one. -/
def upd [DecidableEq Sym] (es : List (EntryR Sym))
    (w : Witness Sym) (c : List (Edge Sym))
    (sc : Nat) : List (EntryR Sym) :=
  es.map (fun e => if ceqb e.config c
    then updentry e w sc else e)

/-- Noting a witnessing: if a configuration
    equivalent to the witnessed one already has an
    entry, that entry is updated and nothing else
    changes — no second entry, and no color change
    beyond the epoch pair rule. If none does, a new
    entry is appended with the witnessing as its
    provenance and the current epoch pair as its
    first color. -/
def note [DecidableEq Sym] (r : Registry Sym)
    (w : Witness Sym) (c : List (Edge Sym)) :
    Registry Sym :=
  if r.entries.any (fun e => ceqb e.config c)
    then ⟨upd r.entries w c
      (score (schemeat r w.epoch) c), r.epochs⟩
    else ⟨r.entries ++ [⟨c, [w],
      [(w.epoch, score (schemeat r w.epoch) c)]⟩],
      r.epochs⟩

/-- Noting a witnessing never touches the epochs. -/
theorem notekeepsepochs [DecidableEq Sym]
    (r : Registry Sym) (w : Witness Sym)
    (c : List (Edge Sym)) :
    (note r w c).epochs = r.epochs := by
  unfold note
  split
  · rfl
  · rfl

/-- The current color of an entry is its latest
    epoch pair. -/
def current (e : EntryR Sym) : Option (Nat × Nat) :=
  e.colors.reverse.head?

/-- The latest pair after an append is the appended
    pair. -/
theorem currentappend (l : List (Nat × Nat))
    (p : Nat × Nat) :
    current (⟨[], [], l ++ [p]⟩ : EntryR Sym) =
      some p := by
  simp [current, List.reverse_append]

/- ## Update lemmas -/

/-- The update function at one entry keeps its
    configuration. -/
theorem upd1config [DecidableEq Sym] (e : EntryR Sym)
    (w : Witness Sym) (c : List (Edge Sym))
    (sc : Nat) :
    (if ceqb e.config c then updentry e w sc
      else e).config = e.config := by
  split
  · rfl
  · rfl

/-- Every entry of an update has a source entry with
    the same configuration, and is that entry or its
    witnessing update. -/
theorem updconfig [DecidableEq Sym]
    (es : List (EntryR Sym)) (w : Witness Sym)
    (c : List (Edge Sym)) (sc : Nat)
    (x : EntryR Sym) (hx : x ∈ upd es w c sc) :
    ∃ e ∈ es, x = (if ceqb e.config c
        then updentry e w sc else e) ∧
      x.config = e.config := by
  obtain ⟨e, he, hf⟩ := List.mem_map.mp hx
  refine ⟨e, he, hf.symm, ?_⟩
  rw [← hf]
  exact upd1config e w c sc

/-- The image of an entry stands in the update. -/
theorem updmem [DecidableEq Sym]
    (es : List (EntryR Sym)) (w : Witness Sym)
    (c : List (Edge Sym)) (sc : Nat)
    (e : EntryR Sym) (he : e ∈ es) :
    (if ceqb e.config c then updentry e w sc else e) ∈
      upd es w c sc :=
  List.mem_map_of_mem he

/-- The updated entries are repeat free when the old
    ones are, under the uniqueness invariant. -/
theorem updNodup [DecidableEq Sym]
    (w : Witness Sym) (c : List (Edge Sym))
    (sc : Nat) :
    ∀ (es : List (EntryR Sym)), es.Nodup →
      (∀ e₁ ∈ es, ∀ e₂ ∈ es,
        ceq e₁.config e₂.config → e₁ = e₂) →
      (upd es w c sc).Nodup := by
  intro es
  induction es with
  | nil => intro _ _; exact List.nodup_nil
  | cons e es ih =>
      intro hnodup hpair
      have he : e ∉ es := (List.nodup_cons.mp
        hnodup).1
      have hes : es.Nodup := (List.nodup_cons.mp
        hnodup).2
      have hpair' : ∀ e₁ ∈ es, ∀ e₂ ∈ es,
          ceq e₁.config e₂.config → e₁ = e₂ :=
        fun e₁ h₁ e₂ h₂ h =>
          hpair e₁ (List.mem_cons_of_mem e h₁) e₂
            (List.mem_cons_of_mem e h₂) h
      have hupd : upd (e :: es) w c sc =
          (if ceqb e.config c then updentry e w sc
            else e) :: upd es w c sc := rfl
      rw [hupd]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hes hpair'⟩
      intro hmem
      obtain ⟨e₂, he₂, -, hcfg⟩ :=
        updconfig es w c sc _ hmem
      have hcfg1 : (if ceqb e.config c
          then updentry e w sc else e).config =
          e.config := upd1config e w c sc
      have hceq : ceq e.config e₂.config := by
        have h1 : e.config = e₂.config := by
          rw [← hcfg1, ← hcfg]
        rw [h1]
        exact ceqrefl _
      have hee : e = e₂ := hpair e (by simp) e₂
        (List.mem_cons_of_mem e he₂) hceq
      exact he (hee ▸ he₂)

/-- A filter whose test fails everywhere is empty. -/
theorem filterfalse {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) →
      l.filter p = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      have ha : p a = false := h a (by simp)
      have hrest : ∀ x ∈ as, p x = false :=
        fun x hx => h x (List.mem_cons_of_mem a hx)
      rw [List.filter_cons_of_neg (by simp [ha]),
        ih hrest]

/-- Filters with pointwise equal tests agree. -/
theorem filtercongr {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) →
      l.filter p = l.filter q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      have ha : p a = q a := h a (by simp)
      have hrest : (as.filter p) = (as.filter q) :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      by_cases hpa : p a = true
      · have hqa : q a = true := ha ▸ hpa
        rw [List.filter_cons_of_pos hpa,
          List.filter_cons_of_pos hqa, hrest]
      · have hpaf : p a = false := by
          cases h' : p a with
          | true => exact absurd h' hpa
          | false => rfl
        have hqaf : q a = false := ha ▸ hpaf
        rw [List.filter_cons_of_neg (by simp [hpaf]),
          List.filter_cons_of_neg (by simp [hqaf]),
          hrest]

/- ## The registry invariant and its preservation

    The invariant over a history of witnessings: the
    entries are repeat free; two entries with
    equivalent configurations are equal; every entry's
    configuration was witnessed; every witnessing's
    configuration has an entry; and every entry's
    provenance is exactly the witnessings of its
    configuration class, in append order. -/

/-- The registry invariant over a history. -/
def inv [DecidableEq Sym] (r : Registry Sym)
    (hist : List (Witness Sym × List (Edge Sym))) :
    Prop :=
  r.entries.Nodup ∧
  (∀ e₁ ∈ r.entries, ∀ e₂ ∈ r.entries,
    ceq e₁.config e₂.config → e₁ = e₂) ∧
  (∀ e ∈ r.entries, ∃ p ∈ hist, ceq e.config p.2) ∧
  (∀ p ∈ hist, ∃ e ∈ r.entries, ceq e.config p.2) ∧
  (∀ e ∈ r.entries, ∀ p ∈ hist, ceq e.config p.2 →
    e.prov = (hist.filter
      (fun q => ceqb q.2 p.2)).map Prod.fst)

/-- The founding registry satisfies the invariant
    over the empty history. -/
theorem foundinginv [DecidableEq Sym]
    (scheme : Scheme) :
    inv (founding (Sym := Sym) scheme) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ([] : List (EntryR Sym)).Nodup
    exact List.nodup_nil
  · intro e he
    cases he
  · intro e he
    cases he
  · intro p hp
    cases hp
  · intro e he
    cases he

/-- The class filter of a history, at a configuration
    equivalent to a witnessed one, does not change
    when the class representative changes: the tests
    agree pointwise by transitivity. -/
theorem classfilter [DecidableEq Sym]
    (hist : List (Witness Sym × List (Edge Sym)))
    {c₁ c₂ : List (Edge Sym)} (h : ceq c₁ c₂) :
    hist.filter (fun q => ceqb q.2 c₁) =
      hist.filter (fun q => ceqb q.2 c₂) := by
  apply filtercongr
  intro q _
  by_cases h1 : ceqb q.2 c₁ = true
  · have hceq : ceq q.2 c₁ := (ceqbiff q.2 c₁).mp h1
    have h2 : ceqb q.2 c₂ = true :=
      (ceqbiff q.2 c₂).mpr (ceqtrans hceq h)
    rw [h1, h2]
  · have h1f : ceqb q.2 c₁ = false := by
      cases h' : ceqb q.2 c₁ with
      | true => exact absurd h' h1
      | false => rfl
    have h2 : ceqb q.2 c₂ = false := by
      by_cases h2' : ceqb q.2 c₂ = true
      · have hceq : ceq q.2 c₂ :=
          (ceqbiff q.2 c₂).mp h2'
        have hback : ceq q.2 c₁ :=
          ceqtrans hceq (ceqsymm h)
        exact absurd ((ceqbiff q.2 c₁).mpr hback) h1
      · cases h' : ceqb q.2 c₂ with
        | true => exact absurd h' h2'
        | false => rfl
    rw [h1f, h2]

/-- Preservation: noting one witnessing preserves
    the invariant, with the witnessing appended to
    the history. The two cases are the two clauses of
    the registry's append rule: an existing entry is
    updated, or a new entry is appended. -/
theorem notestep [DecidableEq Sym] {r : Registry Sym}
    {hist : List (Witness Sym × List (Edge Sym))}
    (hinv : inv r hist) (w : Witness Sym)
    (c : List (Edge Sym)) :
    inv (note r w c) (hist ++ [(w, c)]) := by
  obtain ⟨hnodup, hpair, hex1, hex2, hprov⟩ := hinv
  by_cases hany : r.entries.any
      (fun e => ceqb e.config c) = true
  · have hnote : (note r w c).entries =
        upd r.entries w c (score (schemeat r w.epoch)
          c) := by
      unfold note
      rw [if_pos hany]
    obtain ⟨e₀, he₀, hceq0⟩ :
        ∃ e ∈ r.entries, ceq e.config c := by
      rw [List.any_eq_true] at hany
      obtain ⟨e, he, hb⟩ := hany
      exact ⟨e, he, (ceqbiff e.config c).mp hb⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hnote]
      exact updNodup w c _ r.entries hnodup hpair
    · intro x₁ hx₁ x₂ hx₂ hceq
      rw [hnote] at hx₁ hx₂
      obtain ⟨e₁, he₁, hfx₁, hcfg₁⟩ :=
        updconfig _ _ _ _ _ hx₁
      obtain ⟨e₂, he₂, hfx₂, hcfg₂⟩ :=
        updconfig _ _ _ _ _ hx₂
      have hceqe : ceq e₁.config e₂.config := by
        rw [hcfg₁, hcfg₂] at hceq
        exact hceq
      have hee : e₁ = e₂ := hpair e₁ he₁ e₂ he₂ hceqe
      rw [hfx₁, hfx₂, hee]
    · intro x hx
      rw [hnote] at hx
      obtain ⟨e, he, -, hcfg⟩ := updconfig _ _ _ _ _ hx
      obtain ⟨p, hp, hceq⟩ := hex1 e he
      refine ⟨p, List.mem_append_left _ hp, ?_⟩
      rw [hcfg]
      exact hceq
    · intro p hp
      cases List.mem_append.mp hp with
      | inl hp =>
          obtain ⟨e, he, hceq⟩ := hex2 p hp
          refine ⟨(if ceqb e.config c
            then updentry e w
              (score (schemeat r w.epoch) c) else e),
            ?_, ?_⟩
          · rw [hnote]
            exact updmem _ _ _ _ e he
          · have hcfg : (if ceqb e.config c
                then updentry e w
                  (score (schemeat r w.epoch) c)
                else e).config =
                e.config := upd1config e w c _
            rw [hcfg]
            exact hceq
      | inr hp =>
          rw [List.mem_singleton] at hp
          refine ⟨(if ceqb e₀.config c
            then updentry e₀ w
              (score (schemeat r w.epoch) c) else e₀),
            ?_, ?_⟩
          · rw [hnote]
            exact updmem _ _ _ _ e₀ he₀
          · have hcfg : (if ceqb e₀.config c
                then updentry e₀ w
                  (score (schemeat r w.epoch) c)
                else e₀).config =
                e₀.config := upd1config e₀ w c _
            have hp2 : p.2 = c := by rw [hp]
            rw [hcfg, hp2]
            exact hceq0
    · intro x hx p hp hceq
      rw [hnote] at hx
      obtain ⟨e, he, hfx, hcfg⟩ := updconfig _ _ _ _ _ hx
      have hceqe : ceq e.config p.2 := by
        rw [← hcfg]
        exact hceq
      obtain ⟨p₀, hp₀, hceqe0⟩ := hex1 e he
      have hprov0 : e.prov = (hist.filter
          (fun q => ceqb q.2 p₀.2)).map Prod.fst :=
        hprov e he p₀ hp₀ hceqe0
      have hclass : hist.filter
          (fun q => ceqb q.2 p.2) =
          hist.filter (fun q => ceqb q.2 p₀.2) :=
        classfilter hist
          (ceqtrans (ceqsymm hceqe) hceqe0)
      have hsplit : (hist ++ [(w, c)]).filter
          (fun q => ceqb q.2 p.2) =
          hist.filter (fun q => ceqb q.2 p.2) ++
            ([(w, c)]).filter
              (fun q => ceqb q.2 p.2) :=
        List.filter_append _ _
      rw [hsplit, hclass, List.map_append]
      by_cases hcc : ceq e.config c
      · have hpass : ceqb c p.2 = true :=
          (ceqbiff c p.2).mpr
            (ceqtrans (ceqsymm hcc) hceqe)
        have hsingle : ([(w, c)]).filter
            (fun q => ceqb q.2 p.2) = [(w, c)] := by
          rw [List.filter_cons_of_pos (by exact hpass),
            List.filter_nil]
        rw [hsingle]
        have hfxe : x = updentry e w
            (score (schemeat r w.epoch) c) := by
          rw [hfx]
          have hb : ceqb e.config c = true :=
            (ceqbiff e.config c).mpr hcc
          simp only [hb, ↓reduceIte]
        rw [hfxe, ← hprov0]
        rfl
      · have hfail : ceqb c p.2 = false := by
          by_cases hb : ceqb c p.2 = true
          · have hceqc : ceq c p.2 :=
              (ceqbiff c p.2).mp hb
            exact absurd (ceqtrans hceqe
              (ceqsymm hceqc)) hcc
          · cases h' : ceqb c p.2 with
            | true => exact absurd h' hb
            | false => rfl
        have hsingle : ([(w, c)]).filter
            (fun q => ceqb q.2 p.2) = [] := by
          rw [List.filter_cons_of_neg (by simp [hfail]),
            List.filter_nil]
        rw [hsingle]
        have hfxe : x = e := by
          have hb : ceqb e.config c = false := by
            by_cases hb' : ceqb e.config c = true
            · exact absurd ((ceqbiff e.config c).mp
                hb') hcc
            · cases h' : ceqb e.config c with
              | true => exact absurd h' hb'
              | false => rfl
          rw [hfx, if_neg (by simp [hb])]
        rw [hfxe, ← hprov0]
        simp
  · have hfalse : r.entries.any
        (fun e => ceqb e.config c) = false := by
      cases h : r.entries.any (fun e => ceqb e.config c)
        with
      | true => exact absurd h hany
      | false => rfl
    have hall : ∀ e ∈ r.entries, ¬ ceq e.config c := by
      intro e he hceq
      have hb : (fun e => ceqb e.config c) e = true :=
        (ceqbiff e.config c).mpr hceq
      have := (List.any_eq_false.mp hfalse) e he
      exact this hb
    have hnote : (note r w c).entries =
        r.entries ++ [⟨c, [w],
          [(w.epoch, score (schemeat r w.epoch) c)]⟩] := by
      unfold note
      rw [if_neg hany]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hnote]
      apply Aux.nodupappend.mpr
      refine ⟨hnodup, List.nodup_cons.mpr
        ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro x hx hxn
      rw [List.mem_singleton] at hxn
      apply hall x hx
      rw [hxn]
      exact ceqrefl _
    · intro x₁ hx₁ x₂ hx₂ hceq
      rw [hnote] at hx₁ hx₂
      cases List.mem_append.mp hx₁ with
      | inl hx₁ =>
          cases List.mem_append.mp hx₂ with
          | inl hx₂ => exact hpair x₁ hx₁ x₂ hx₂ hceq
          | inr hx₂ =>
              rw [List.mem_singleton] at hx₂
              exfalso
              apply hall x₁ hx₁
              rw [hx₂] at hceq
              exact hceq
      | inr hx₁ =>
          rw [List.mem_singleton] at hx₁
          cases List.mem_append.mp hx₂ with
          | inl hx₂ =>
              exfalso
              apply hall x₂ hx₂
              rw [hx₁] at hceq
              exact ceqsymm hceq
          | inr hx₂ =>
              rw [List.mem_singleton] at hx₂
              rw [hx₁, hx₂]
    · intro x hx
      rw [hnote] at hx
      cases List.mem_append.mp hx with
      | inl hx =>
          obtain ⟨p, hp, hceq⟩ := hex1 x hx
          exact ⟨p, List.mem_append_left _ hp, hceq⟩
      | inr hx =>
          rw [List.mem_singleton] at hx
          refine ⟨(w, c), ?_, ?_⟩
          · exact List.mem_append_right _
              (List.mem_singleton_self _)
          · rw [hx]
            exact ceqrefl _
    · intro p hp
      cases List.mem_append.mp hp with
      | inl hp =>
          obtain ⟨e, he, hceq⟩ := hex2 p hp
          refine ⟨e, ?_, hceq⟩
          rw [hnote]
          exact List.mem_append_left _ he
      | inr hp =>
          rw [List.mem_singleton] at hp
          refine ⟨⟨c, [w], [(w.epoch,
            score (schemeat r w.epoch) c)]⟩, ?_, ?_⟩
          · rw [hnote]
            exact List.mem_append_right _
              (List.mem_singleton_self _)
          · rw [hp]
            exact ceqrefl _
    · intro x hx p hp hceq
      rw [hnote] at hx
      have hsplit : (hist ++ [(w, c)]).filter
          (fun q => ceqb q.2 p.2) =
          hist.filter (fun q => ceqb q.2 p.2) ++
            ([(w, c)]).filter
              (fun q => ceqb q.2 p.2) :=
        List.filter_append _ _
      rw [hsplit, List.map_append]
      cases List.mem_append.mp hx with
      | inl hx =>
          cases List.mem_append.mp hp with
          | inl hp =>
              have hfail : ceqb c p.2 = false := by
                by_cases hb : ceqb c p.2 = true
                · have hceqc : ceq c p.2 :=
                    (ceqbiff c p.2).mp hb
                  exact absurd (ceqtrans hceq
                    (ceqsymm hceqc)) (hall x hx)
                · cases h' : ceqb c p.2 with
                  | true => exact absurd h' hb
                  | false => rfl
              have hsingle : ([(w, c)]).filter
                  (fun q => ceqb q.2 p.2) = [] := by
                rw [List.filter_cons_of_neg
                  (by simp [hfail]), List.filter_nil]
              rw [hsingle]
              have hprov0 : x.prov = (hist.filter
                  (fun q => ceqb q.2 p.2)).map
                  Prod.fst := hprov x hx p hp hceq
              rw [hprov0]
              simp
          | inr hp =>
              rw [List.mem_singleton] at hp
              have hceqc : ceq x.config c := by
                rw [hp] at hceq
                exact hceq
              exact (hall x hx hceqc).elim
      | inr hx =>
          rw [List.mem_singleton] at hx
          cases List.mem_append.mp hp with
          | inl hp =>
              exfalso
              obtain ⟨e, he, hceqe⟩ := hex2 p hp
              apply hall e he
              have hceqc : ceq c p.2 := by
                rw [hx] at hceq
                exact hceq
              exact ceqtrans hceqe (ceqsymm hceqc)
          | inr hp =>
              rw [List.mem_singleton] at hp
              have hfilthist : hist.filter
                  (fun q => ceqb q.2 p.2) = [] := by
                apply filterfalse
                intro q hq
                by_cases hb : ceqb q.2 p.2 = true
                · have hceqq : ceq q.2 p.2 :=
                    (ceqbiff q.2 p.2).mp hb
                  obtain ⟨e, he, hceqe⟩ := hex2 q hq
                  have hceqc : ceq c p.2 := by
                    rw [hx] at hceq
                    exact hceq
                  exact absurd (ceqtrans
                    (ceqtrans hceqe hceqq)
                    (ceqsymm hceqc)) (hall e he)
                · cases h' : ceqb q.2 p.2 with
                  | true => exact absurd h' hb
                  | false => rfl
              have hpass : ceqb c p.2 = true := by
                rw [hx] at hceq
                exact (ceqbiff c p.2).mpr hceq
              have hsingle : ([(w, c)]).filter
                  (fun q => ceqb q.2 p.2) =
                  [(w, c)] := by
                rw [List.filter_cons_of_pos
                  (by exact hpass), List.filter_nil]
              rw [hfilthist, hsingle, hx]
              rfl

/-- Applying a list of witnessings, in order. -/
def applyall [DecidableEq Sym] (r : Registry Sym) :
    List (Witness Sym × List (Edge Sym)) →
      Registry Sym
  | [] => r
  | p :: rest => applyall (note r p.1 p.2) rest

/-- The invariant is preserved by any list of
    witnessings, the history growing by exactly that
    list. -/
theorem applyallinv [DecidableEq Sym] :
    ∀ (l : List (Witness Sym × List (Edge Sym)))
      (r : Registry Sym)
      (hist : List (Witness Sym × List (Edge Sym))),
      inv r hist → inv (applyall r l) (hist ++ l) := by
  intro l
  induction l with
  | nil =>
      intro r hist hinv
      simp only [List.append_nil]
      exact hinv
  | cons p rest ih =>
      intro r hist hinv
      have hstep : inv (applyall (note r p.1 p.2) rest)
          ((hist ++ [p]) ++ rest) :=
        ih (note r p.1 p.2) (hist ++ [p])
          (notestep hinv p.1 p.2)
      have happs : (hist ++ [p]) ++ rest =
          hist ++ (p :: rest) := by
        simp only [List.append_assoc, List.cons_append,
          List.nil_append]
      rw [happs] at hstep
      exact hstep

/-- Exactly one entry per class: a repeat free list
    of entries, pairwise distinct up to equivalence,
    with an entry of the class, has exactly one entry
    of the class. -/
theorem classcountone [DecidableEq Sym]
    {es : List (EntryR Sym)} (hnodup : es.Nodup)
    (hpair : ∀ e₁ ∈ es, ∀ e₂ ∈ es,
      ceq e₁.config e₂.config → e₁ = e₂)
    {c : List (Edge Sym)} (e₀ : EntryR Sym)
    (he₀ : e₀ ∈ es) (hceq : ceq e₀.config c) :
    (es.filter (fun e => ceqb e.config c)).length =
      1 := by
  have hmem : e₀ ∈ es.filter
      (fun e => ceqb e.config c) :=
    List.mem_filter.mpr
      ⟨he₀, (ceqbiff e₀.config c).mpr hceq⟩
  have hnodupf : (es.filter
      (fun e => ceqb e.config c)).Nodup :=
    (List.filter_sublist).nodup hnodup
  have hall : ∀ x ∈ es.filter
      (fun e => ceqb e.config c), x = e₀ := by
    intro x hx
    obtain ⟨hxe, hxc⟩ := List.mem_filter.mp hx
    have hceqx : ceq x.config c :=
      (ceqbiff x.config c).mp hxc
    exact hpair x hxe e₀ he₀
      (ceqtrans hceqx (ceqsymm hceq))
  have hle : (es.filter
      (fun e => ceqb e.config c)).length ≤
      [e₀].length :=
    Aux.lengthle _ _ hnodupf (fun x hx => by
      rw [hall x hx]
      exact List.mem_singleton_self _)
  have hne : es.filter (fun e => ceqb e.config c) ≠
      [] := by
    intro hnil
    rw [hnil] at hmem
    cases hmem
  have hge : 0 < (es.filter
      (fun e => ceqb e.config c)).length :=
    Aux.lengthpos hne
  simp at hle
  omega

/-- Claim eight, uniqueness and provenance: after any
    witnessings from the founding, every witnessed
    configuration class has exactly one entry; every
    entry's provenance is exactly the witnessings of
    its class in append order; and every entry's
    configuration was witnessed. -/
theorem registryexact [DecidableEq Sym]
    (scheme : Scheme)
    (notes : List (Witness Sym × List (Edge Sym))) :
    (∀ p ∈ notes, ((applyall
        (founding (Sym := Sym) scheme) notes).entries
        |>.filter (fun e => ceqb e.config p.2)).length
        = 1) ∧
    (∀ e ∈ (applyall (founding (Sym := Sym) scheme)
        notes).entries,
      ∀ p ∈ notes, ceq e.config p.2 →
        e.prov = (notes.filter
          (fun q => ceqb q.2 p.2)).map Prod.fst) ∧
    (∀ e ∈ (applyall (founding (Sym := Sym) scheme)
        notes).entries,
      ∃ p ∈ notes, ceq e.config p.2) := by
  have hinv : inv (applyall
      (founding (Sym := Sym) scheme) notes)
      ([] ++ notes) :=
    applyallinv notes _ [] (foundinginv scheme)
  simp only [List.nil_append] at hinv
  refine ⟨?_, hinv.2.2.2.2, hinv.2.2.1⟩
  intro p hp
  obtain ⟨e₀, he₀, hceq⟩ := hinv.2.2.2.1 p hp
  exact classcountone hinv.1 hinv.2.1 e₀ he₀ hceq

/-- Claim eight, epochs and colors standing: under
    the uniqueness invariant, the colors of the entry
    of a configuration after a noting extend the
    colors of its entry before — pairs under earlier
    epochs stand, the list only grows by append. -/
theorem colorsstand [DecidableEq Sym]
    (r : Registry Sym)
    (hpair : ∀ e₁ ∈ r.entries, ∀ e₂ ∈ r.entries,
      ceq e₁.config e₂.config → e₁ = e₂)
    (w : Witness Sym) (c : List (Edge Sym))
    (e : EntryR Sym) (he : e ∈ r.entries)
    (e' : EntryR Sym) (he' : e' ∈ (note r w c).entries)
    (hcfg : e'.config = e.config) :
    ∃ rest, e.colors ++ rest = e'.colors := by
  by_cases hany : r.entries.any
      (fun e => ceqb e.config c) = true
  · have hnote : (note r w c).entries =
        upd r.entries w c (score (schemeat r w.epoch)
          c) := by
      unfold note
      rw [if_pos hany]
    rw [hnote] at he'
    obtain ⟨e₂, he₂, hf, hcfg₂⟩ :=
      updconfig _ _ _ _ _ he'
    have hceq : ceq e₂.config e.config := by
      rw [← hcfg₂, hcfg]
      exact ceqrefl _
    have hee : e₂ = e := hpair e₂ he₂ e he hceq
    rw [hee] at hf
    by_cases hb : ceqb e.config c = true
    · simp only [hb, ↓reduceIte] at hf
      subst hf
      by_cases hcol : e.colors.any
          (fun p => p.1 = w.epoch) = true
      · refine ⟨[], ?_⟩
        simp only [updentry, hcol, ↓reduceIte,
          List.append_nil]
      · have hcolf : e.colors.any
            (fun p => p.1 = w.epoch) = false := by
          cases h : e.colors.any
              (fun p => p.1 = w.epoch) with
          | true => exact absurd h hcol
          | false => rfl
        refine ⟨[(w.epoch,
          score (schemeat r w.epoch) c)], ?_⟩
        show e.colors ++
            [(w.epoch, score (schemeat r w.epoch) c)] =
          (if e.colors.any (fun p => p.1 = w.epoch) =
              true
            then e.colors
            else e.colors ++
              [(w.epoch, score (schemeat r w.epoch) c)])
        rw [if_neg (by simp [hcolf])]
    · have hbf : ceqb e.config c = false := by
        cases h : ceqb e.config c with
        | true => exact absurd h hb
        | false => rfl
      simp only [hbf, ↓reduceIte] at hf
      exact ⟨[], by simp [hf]⟩
  · have hfalse : r.entries.any
        (fun e => ceqb e.config c) = false := by
      cases h : r.entries.any (fun e => ceqb e.config c)
        with
      | true => exact absurd h hany
      | false => rfl
    have hnote : (note r w c).entries =
        r.entries ++ [⟨c, [w],
          [(w.epoch, score (schemeat r w.epoch) c)]⟩] := by
      unfold note
      rw [if_neg hany]
    rw [hnote] at he'
    cases List.mem_append.mp he' with
    | inl he' =>
        have hee : e' = e := hpair e' he' e he (by
          rw [hcfg]
          exact ceqrefl _)
        exact ⟨[], by simp [hee]⟩
    | inr he' =>
        rw [List.mem_singleton] at he'
        exfalso
        apply hany
        rw [List.any_eq_true]
        refine ⟨e, he, ?_⟩
        apply (ceqbiff e.config c).mpr
        rw [he'] at hcfg
        have h1 : e.config = c := hcfg.symm
        rw [h1]
        exact ceqrefl _

/-- Claim eight, determinism at the registry: the
    pair a noting records for the entry of a witnessed
    configuration is that epoch and the score of the
    witnessed configuration under the epoch's scheme
    — a function of content alone, by scoreeq the
    same for the entry's own configuration. -/
theorem notecolor [DecidableEq Sym]
    (r : Registry Sym) (w : Witness Sym)
    (c : List (Edge Sym)) (e : EntryR Sym)
    (he : e ∈ r.entries) (hc : ceq e.config c)
    (hnew : e.colors.any
      (fun p => p.1 = w.epoch) = false) :
    ∃ e' ∈ (note r w c).entries,
      e'.config = e.config ∧
      e'.colors = e.colors ++
        [(w.epoch, score (schemeat r w.epoch) c)] ∧
      e'.prov = e.prov ++ [w] := by
  have hany : r.entries.any
      (fun e => ceqb e.config c) = true := by
    rw [List.any_eq_true]
    exact ⟨e, he, (ceqbiff e.config c).mpr hc⟩
  have hnote : (note r w c).entries =
      upd r.entries w c (score (schemeat r w.epoch)
        c) := by
    unfold note
    rw [if_pos hany]
  refine ⟨updentry e w
    (score (schemeat r w.epoch) c), ?_, rfl, ?_, rfl⟩
  · rw [hnote]
    have hfe : (fun x => if ceqb x.config c
        then updentry x w
          (score (schemeat r w.epoch) c) else x) e =
        updentry e w
          (score (schemeat r w.epoch) c) := by
      simp only [(ceqbiff e.config c).mpr hc,
        ↓reduceIte]
    exact hfe ▸ List.mem_map_of_mem he
  · simp [updentry, hnew]

/-- The current color after a noting that appends a
    pair is that pair: the latest epoch pair, whose
    score is the deterministic color of the
    configuration under that epoch. -/
theorem notecurrent [DecidableEq Sym]
    (r : Registry Sym) (w : Witness Sym)
    (c : List (Edge Sym)) (e : EntryR Sym)
    (he : e ∈ r.entries) (hc : ceq e.config c)
    (hnew : e.colors.any
      (fun p => p.1 = w.epoch) = false) :
    ∃ e' ∈ (note r w c).entries,
      e'.config = e.config ∧
      current e' = some
        (w.epoch, score (schemeat r w.epoch) c) := by
  obtain ⟨e', he', hcfg, hcolors, -⟩ :=
    notecolor r w c e he hc hnew
  refine ⟨e', he', hcfg, ?_⟩
  show e'.colors.reverse.head? = some
    (w.epoch, score (schemeat r w.epoch) c)
  rw [hcolors]
  simp [List.reverse_append]
