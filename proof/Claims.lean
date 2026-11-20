import Ops

/- ## The claims of section 13

    Each claim of section 13 is proved here from the
    model of Core and the operations of Ops, and given
    the single word name the spec assigns it: mono,
    compound, appear, coloring, bounds, reconcile,
    widen. The registry claim is in the registry file.
    The counting heart of mono and compound is proved
    first: excess, read as the sum over edges of size
    minus one, never grows when every old edge is
    covered jointly by one new edge. -/

open scoped Classical

/-- A sum over a list splits over a filter and its
    complement filter. -/
theorem sumsplit [DecidableEq Sym] :
    ∀ (f : Edge Sym → Nat) (p : Edge Sym → Bool)
      (l : List (Edge Sym)),
      (l.map f).sum = ((l.filter p).map f).sum +
        ((l.filter (fun e => !p e)).map f).sum := by
  intro f p l
  induction l with
  | nil => rfl
  | cons e es ih =>
      by_cases hp : p e = true
      · have hneg : ¬ (fun x => !p x) e = true := by
          simp only [hp, Bool.not_true, Bool.false_eq_true,
            not_false_eq_true]
        rw [List.filter_cons_of_pos hp,
          List.filter_cons_of_neg (p := fun x => !p x) hneg]
        simp only [List.map_cons, List.sum_cons, ih]
        omega
      · have hp2 : (fun x => !p x) e = true := by
          have hpf : p e = false := by
            cases hpe : p e with
            | false => rfl
            | true => exact absurd hpe hp
          simp only [hpf, Bool.not_false]
        rw [List.filter_cons_of_neg hp,
          List.filter_cons_of_pos (p := fun x => !p x) hp2]
        simp only [List.map_cons, List.sum_cons, ih]
        omega

/-- The sum of size minus one over a list of nonempty
    edges is the sum of the sizes minus the count. -/
theorem sumsubone [DecidableEq Sym] :
    ∀ (l : List (Edge Sym)),
      (∀ e ∈ l, e.terms ≠ []) →
        (l.map (fun e => e.terms.length - 1)).sum =
          (l.map (fun e => e.terms.length)).sum -
            l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e es ih =>
      intro hne
      have h1 : 1 ≤ e.terms.length :=
        Aux.lengthpos (hne e (by simp))
      have ih' := ih (fun x hx => hne x (by
        exact List.mem_cons_of_mem e hx))
      have hge : es.length ≤
          (es.map (fun e => e.terms.length)).sum :=
        Aux.sumge (fun e => e.terms.length) es
          (fun x hx => Aux.lengthpos
            (hne x (List.mem_cons_of_mem e hx)))
      simp only [List.map_cons, List.sum_cons,
        List.length_cons, ih']
      omega

/-- The sum of the sizes of a list of pairwise disjoint
    nodup edges, all of whose terms lie in one nodup
    list, is at most the length of that list: their
    flattened terms form a nodup sublist of it. -/
theorem concatle [DecidableEq Sym] :
    ∀ (l : List (Edge Sym)) (big : List (Term Sym)),
      (∀ e ∈ l, ∀ x ∈ e.terms, x ∈ big) →
      (∀ e ∈ l, e.terms.Nodup) →
      (∀ e₁ ∈ l, ∀ e₂ ∈ l, ∀ t, t ∈ e₁.terms →
        t ∈ e₂.terms → e₁ = e₂) →
      l.Nodup → big.Nodup →
        (l.map (fun e => e.terms.length)).sum ≤
          big.length := by
  intro l big hcover hnodup hdisj hlnd hbig
  have hflat : (l.flatMap (fun e => e.terms)).Nodup := by
    induction l with
    | nil => exact List.nodup_nil
    | cons e es ih =>
        have hnd1 : e.terms.Nodup :=
          hnodup e (by simp)
        have hnd2 : (es.flatMap (fun e => e.terms)).Nodup :=
          ih (fun x hx => hcover x (by
              exact List.mem_cons_of_mem e hx))
            (fun x hx => hnodup x (by
              exact List.mem_cons_of_mem e hx))
            (fun x hx y hy => hdisj x (by
                exact List.mem_cons_of_mem e hx) y (by
                exact List.mem_cons_of_mem e hy))
            (by
              have h := hlnd
              rw [List.nodup_cons] at h
              exact h.2)
        rw [List.flatMap_cons]
        rw [Aux.nodupappend]
        refine ⟨hnd1, hnd2, ?_⟩
        intro x hx hxflat
        rw [List.mem_flatMap] at hxflat
        obtain ⟨e₂, he₂, hx₂⟩ := hxflat
        have hee : e₂ = e :=
          hdisj e₂ (List.mem_cons_of_mem e he₂) e (by simp)
            x hx₂ hx
        have hne : e ∉ es := by
          have h := hlnd
          rw [List.nodup_cons] at h
          exact h.1
        exact hne (hee ▸ he₂)
  have hlen : (l.flatMap (fun e => e.terms)).length =
      (l.map (fun e => e.terms.length)).sum := by
    rw [List.length_flatMap]
  rw [← hlen]
  exact Aux.lengthle _ _ hflat (by
    intro x hx
    rw [List.mem_flatMap] at hx
    obtain ⟨e, he, hxe⟩ := hx
    exact hcover e he x hxe)

/-- Whether every term of the second edge lies in the
    first: the covering test of the covering bound, as a
    boolean. -/
def coveredby [DecidableEq Sym] (big small : Edge Sym) :
    Bool :=
  small.terms.all (fun x => decide (x ∈ big.terms))

/-- The covering test holds exactly when every term of
    the small edge lies in the big edge. -/
theorem coveredbyiff [DecidableEq Sym]
    (big small : Edge Sym) :
    coveredby big small = true ↔
      ∀ x ∈ small.terms, x ∈ big.terms := by
  simp only [coveredby, List.all_eq_true,
    decide_eq_true_eq]

/-- The covering bound: when every edge of one list is
    jointly covered by one edge of a second list, and
    both lists are partitions into nonempty nodup
    edges, the sum of size minus one over the first is
    at most that over the second. Excess is monotone
    under joint covering. -/
theorem coverbound [DecidableEq Sym] :
    ∀ (first second : List (Edge Sym)),
      (∀ e ∈ first, e.terms ≠ []) →
      (∀ e ∈ first, e.terms.Nodup) →
      (∀ e₁ ∈ first, ∀ e₂ ∈ first, ∀ t, t ∈ e₁.terms →
        t ∈ e₂.terms → e₁ = e₂) →
      first.Nodup →
      (∀ e ∈ second, e.terms ≠ []) →
      (∀ e ∈ second, e.terms.Nodup) →
      (∀ e₁ ∈ second, ∀ e₂ ∈ second, ∀ t, t ∈ e₁.terms →
        t ∈ e₂.terms → e₁ = e₂) →
      (∀ e ∈ first, ∃ big ∈ second,
        ∀ x ∈ e.terms, x ∈ big.terms) →
        (first.map (fun e => e.terms.length - 1)).sum ≤
          (second.map (fun e => e.terms.length - 1)).sum := by
  intro first second
  induction second generalizing first with
  | nil =>
      intro hne _ _ _ _ _ _ hcover
      cases first with
      | nil => exact Nat.zero_le _
      | cons e es =>
          exfalso
          obtain ⟨big, hbig, -⟩ := hcover e (by simp)
          cases hbig
  | cons big rest ih =>
      intro hne hnodup hdisj hfirst hne2 hnodup2 hdisj2
        hcover
      have hbigne : big.terms ≠ [] :=
        hne2 big (by simp)
      have hbignd : big.terms.Nodup :=
        hnodup2 big (by simp)
      have hsplit := sumsplit (fun e => e.terms.length - 1)
        (coveredby big) first
      have hfiber : ((first.filter (coveredby big)).map
          (fun e => e.terms.length - 1)).sum ≤
          big.terms.length - 1 := by
        have hsub := sumsubone (first.filter
          (coveredby big)) (by
          intro x hx
          rw [List.mem_filter] at hx
          exact hne x hx.1)
        rw [hsub]
        have hcon := concatle (first.filter (coveredby big))
          big.terms
          (by
            intro e he x hx
            rw [List.mem_filter] at he
            exact (coveredbyiff big e).mp he.2 x hx)
          (by
            intro x hx
            rw [List.mem_filter] at hx
            exact hnodup x hx.1)
          (by
            intro x hx y hy t ht1 ht2
            rw [List.mem_filter] at hx hy
            exact hdisj x hx.1 y hy.1 t ht1 ht2)
          (List.Sublist.nodup List.filter_sublist hfirst)
          hbignd
        by_cases hempty : first.filter (coveredby big) = []
        · rw [hempty]
          simp
        · have hlen : 1 ≤ (first.filter
              (coveredby big)).length :=
            Aux.lengthpos (by
              cases hlist : first.filter (coveredby big) with
              | nil => exact absurd hlist hempty
              | cons e es => simp)
          omega
      have hrest : ((first.filter
          (fun e => !(coveredby big e))).map
          (fun e => e.terms.length - 1)).sum ≤
          (rest.map (fun e => e.terms.length - 1)).sum := by
        apply ih
        · intro x hx
          rw [List.mem_filter] at hx
          exact hne x hx.1
        · intro x hx
          rw [List.mem_filter] at hx
          exact hnodup x hx.1
        · intro x hx y hy t ht1 ht2
          rw [List.mem_filter] at hx hy
          exact hdisj x hx.1 y hy.1 t ht1 ht2
        · exact List.Sublist.nodup List.filter_sublist
            hfirst
        · intro x hx
          exact hne2 x (by exact List.mem_cons_of_mem big hx)
        · intro x hx
          exact hnodup2 x (by
            exact List.mem_cons_of_mem big hx)
        · intro x hx y hy t ht1 ht2
          exact hdisj2 x (List.mem_cons_of_mem big hx) y
            (List.mem_cons_of_mem big hy) t ht1 ht2
        · intro e he
          rw [List.mem_filter] at he
          obtain ⟨big', hbig', hcov⟩ := hcover e he.1
          cases List.mem_cons.mp hbig' with
          | inl heq =>
              exfalso
              have hall : coveredby big e = true :=
                (coveredbyiff big e).mpr (fun x hx =>
                  heq ▸ hcov x hx)
              have hne2' : (!(coveredby big e)) = true :=
                he.2
              rw [hall] at hne2'
              cases hne2'
          | inr hrest' => exact ⟨big', hrest', hcov⟩
      rw [hsplit]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Excess monotonicity, in the form every later use
    needs: between two valid graphs, when every term
    collected in the first stays collected in the
    second and every equivalence of the first stands in
    the second, the excess of the first is at most the
    excess of the second. -/
theorem excessmono [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (validg : Valid kinds g)
    (validh : Valid kinds h)
    (hcol : ∀ t, collected g t → collected h t)
    (hsame : ∀ x y, same g x y → same h x y) :
    excess g ≤ excess h := by
  have hsumg : (g.edges.map
      (fun e => e.terms.length - 1)).sum = excess g := by
    rw [sumsubone g.edges validg.nonempty, excess]
  have hsumh : (h.edges.map
      (fun e => e.terms.length - 1)).sum = excess h := by
    rw [sumsubone h.edges validh.nonempty, excess]
  rw [← hsumg, ← hsumh]
  apply coverbound
  · exact validg.nonempty
  · exact validg.nodup
  · exact validg.disjoint
  · exact validg.edgenodup
  · exact validh.nonempty
  · exact validh.nodup
  · exact validh.disjoint
  · intro e he
    have hne := validg.nonempty e he
    obtain ⟨x, hxe⟩ : ∃ x, x ∈ e.terms := by
      cases hterms : e.terms with
      | nil => exact absurd hterms hne
      | cons x xs => exact ⟨x, by simp [hterms]⟩
    obtain ⟨big, hbig, hxbig⟩ := hcol x ⟨e, he, hxe⟩
    refine ⟨big, hbig, ?_⟩
    intro y hy
    have hsy : same h x y := hsame x y ⟨e, he, hxe, hy⟩
    obtain ⟨e', he', hx', hy'⟩ := hsy
    have heq : e' = big :=
      validh.disjoint e' he' big hbig x hx' hxbig
    exact heq ▸ hy'

/- ## Claim one: mono

    Monotonicity under expansion. Under the growth
    relation every equivalent pair stays equivalent,
    witnessed redundancy persists, and excess never
    decreases — proved for the bare growth relation by
    the covering bound, and along operation runs by the
    run excess theorem, whose per operation deltas are
    the ones the spec names: enter, record, and paint
    change excess by zero, and join by exactly its
    effective join count. -/

/-- Claim one, equivalence: under the growth relation,
    every pair equivalent stays equivalent. -/
theorem mono [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h)
    (x y : Term Sym) : same g x y → same h x y :=
  growth.same x y

/-- Claim one, excess: under the growth relation,
    between valid graphs, excess never decreases. -/
theorem monoexcess [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (validg : Valid kinds g)
    (validh : Valid kinds h) (growth : Growth kinds g h) :
    excess g ≤ excess h :=
  excessmono kinds validg validh growth.collected
    growth.same

/-- Claim one, witnesses: a witnessed pair of distinct
    equivalent terms persists under growth, as a pair
    in one edge of the grown graph. -/
theorem monopair [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h)
    {e : Edge Sym} (he : e ∈ g.edges)
    {x y : Term Sym} (hx : x ∈ e.terms) (hy : y ∈ e.terms) :
    ∃ e' ∈ h.edges, x ∈ e'.terms ∧ y ∈ e'.terms :=
  growth.same x y ⟨e, he, hx, hy⟩

/-- Claim one, along a run: the excess after a ready
    run is at least the excess before it. -/
theorem excessrun [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {ops : List (Op Sym)}
    (ready : Ready kinds g ops) :
    excess g ≤ excess (run kinds g ops) := by
  have h := runexcess kinds ready
  omega

/- ## Twins: two graphs related by collection and
    equivalence inclusion

    The compounding claim needs one run read from two
    starting graphs: when the second start is grown
    from the first, everything the run collects or
    identifies from the first start it also collects or
    identifies from the second. The relation carrying
    exactly those two inclusions is a twin relation;
    growth implies it, and every operation preserves
    it. The backward readings of the operations — what
    collection and equivalence in an operated graph
    came from — are proved first. -/

/-- Entering a collected term changes no edge. -/
theorem enteredgesof [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym)
    (hcol : collected graph term) :
    (enter kinds graph term level wit).edges =
      graph.edges := by
  cases hs : seek graph.edges term with
  | none =>
      exfalso
      obtain ⟨e, he, ht⟩ := hcol
      exact (seeknone graph.edges term hs e he) ht
  | some found => simp only [enter, hs]

/-- The edges after one entry: an old edge, or the new
    singleton. -/
theorem enteredgesback [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (term : Term Sym) (level wit : Sym) (edge : Edge Sym) :
    edge ∈ (enter kinds graph term level wit).edges →
      edge ∈ graph.edges ∨
        edge = { terms := [term], colors := [] } := by
  intro hedge
  cases hs : seek graph.edges term with
  | none =>
      have h2 : (enter kinds graph term level
          wit).edges =
          graph.edges ++
            [{ terms := [term], colors := [] }] := by
        simp only [enter, hs]
      rw [h2] at hedge
      cases List.mem_append.mp hedge with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (List.mem_singleton.mp h)
  | some found =>
      have h2 : (enter kinds graph term level
          wit).edges = graph.edges := by
        simp only [enter, hs]
      rw [h2] at hedge
      exact Or.inl hedge

/-- The edges after entering a list: an old edge, or
    the singleton of a listed term. -/
theorem enteralledgesback [DecidableEq Sym]
    (kinds : Kinds Sym) (terms : List (Term Sym))
    (level wit : Sym) :
    ∀ (graph : Graph Sym) (edge : Edge Sym),
      edge ∈ (enterall kinds graph terms level
        wit).edges →
        edge ∈ graph.edges ∨
          ∃ t ∈ terms,
            edge = { terms := [t], colors := [] } := by
  induction terms with
  | nil => intro graph edge hedge; exact Or.inl hedge
  | cons t ts ih =>
      intro graph edge hedge
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit)
            ts level wit := rfl
      rw [h1] at hedge
      cases ih _ edge hedge with
      | inl h =>
          cases enteredgesback kinds graph t level wit
              edge h with
          | inl h2 => exact Or.inl h2
          | inr h2 =>
              exact Or.inr ⟨t, by simp, h2⟩
      | inr h =>
          obtain ⟨u, hu, heq⟩ := h
          exact Or.inr ⟨u, List.mem_cons_of_mem t hu, heq⟩

/-- Collection after entering a list comes from the
    graph or from the list. -/
theorem enterallcollectedback [DecidableEq Sym]
    (kinds : Kinds Sym) (terms : List (Term Sym))
    (level wit : Sym) :
    ∀ (graph : Graph Sym) (term : Term Sym),
      collected (enterall kinds graph terms level wit)
          term →
        collected graph term ∨ term ∈ terms := by
  induction terms with
  | nil => intro graph term hcol; exact Or.inl hcol
  | cons t ts ih =>
      intro graph term hcol
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit)
            ts level wit := rfl
      rw [h1] at hcol
      cases ih _ term hcol with
      | inl h =>
          cases (entercollected kinds graph t level wit
              term).mp h with
          | inl h2 => exact Or.inl h2
          | inr h2 =>
              exact Or.inr (List.mem_cons.mpr (Or.inl h2))
      | inr h =>
          exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- The singleton of an uncollected listed term stands
    after entering the list. -/
theorem enterallsing [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym) (term : Term Sym),
      term ∈ terms → ¬ collected graph term →
        { terms := [term], colors := [] } ∈
          (enterall kinds graph terms level wit).edges := by
  induction terms with
  | nil => intro graph term hmem _; cases hmem
  | cons t ts ih =>
      intro graph term hmem hnc
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit)
            ts level wit := rfl
      have hsing : ∀ (g : Graph Sym),
          ¬ collected g term →
            { terms := [term], colors := [] } ∈
              (enter kinds g term level wit).edges := by
        intro g hncg
        have hs : seek g.edges term = none := by
          by_cases h : seek g.edges term = none
          · exact h
          · cases hso : seek g.edges term with
            | none => rfl
            | some found =>
                obtain ⟨hfin, hfterm⟩ :=
                  seeksome g.edges term found hso
                exact absurd ⟨found, hfin, hfterm⟩ hncg
        have h2 : (enter kinds g term level wit).edges =
            g.edges ++
              [{ terms := [term], colors := [] }] := by
          simp only [enter, hs]
        rw [h2]
        exact List.mem_append_right _ (by simp)
      cases List.mem_cons.mp hmem with
      | inl heq =>
          subst heq
          rw [h1]
          exact enteralledges kinds ts level wit _
            _ (hsing graph hnc)
      | inr hts =>
          by_cases heq : term = t
          · subst heq
            rw [h1]
            exact enteralledges kinds ts level wit _
              _ (hsing graph hnc)
          · rw [h1]
            apply ih _ _ hts
            intro hcol
            cases (entercollected kinds graph t level wit
                term).mp hcol with
            | inl h => exact hnc h
            | inr h => exact heq h

/-- Collection in a merge step comes from the graph
    before it. -/
theorem mergecollectedback [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (one two : Term Sym) (level wit : Sym)
    (term : Term Sym) :
    collected (merge kinds graph one two level wit)
        term →
      collected graph term := by
  intro hcol
  obtain ⟨e, he, ht⟩ := hcol
  cases h1 : seek graph.edges one with
  | none =>
      have h2 : (merge kinds graph one two level
          wit).edges = graph.edges := by
        simp only [merge, h1]
      exact ⟨e, h2 ▸ he, ht⟩
  | some ea =>
      cases h2s : seek graph.edges two with
      | none =>
          have h2 : (merge kinds graph one two level
              wit).edges = graph.edges := by
            simp only [merge, h1, h2s]
          exact ⟨e, h2 ▸ he, ht⟩
      | some eb =>
          by_cases hee : ea = eb
          · have h2 : (merge kinds graph one two level
                wit).edges = graph.edges := by
              simp only [merge, h1, h2s, hee, ↓reduceIte]
            exact ⟨e, h2 ▸ he, ht⟩
          · have h2 : (merge kinds graph one two level
                wit).edges =
                joinEdges graph.edges one two := by
              simp only [merge, h1, h2s, hee, ↓reduceIte]
            rw [h2, joinEdgesmem graph one two ea eb h1
              h2s e] at he
            cases he with
            | inl h => exact ⟨e, h.1, ht⟩
            | inr h =>
                rw [h] at ht
                have ht2 : term ∈ ea.terms ++ eb.terms :=
                  ht
                cases List.mem_append.mp ht2 with
                | inl ht' =>
                    obtain ⟨hfin, -⟩ :=
                      seeksome graph.edges one ea h1
                    exact ⟨ea, hfin, ht'⟩
                | inr ht' =>
                    obtain ⟨hfin, -⟩ :=
                      seeksome graph.edges two eb h2s
                    exact ⟨eb, hfin, ht'⟩

/-- Collection in a join operation comes from the
    graph, or is one of the two joined terms. -/
theorem joincollectedback [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (one two : Term Sym) (level wit : Sym)
    (term : Term Sym) :
    collected (join kinds graph one two level wit)
        term →
      collected graph term ∨ term = one ∨ term = two := by
  intro hcol
  have h1 := mergecollectedback kinds
    (enter kinds (enter kinds graph one level wit) two
      level wit) one two level wit term hcol
  cases (entercollected kinds _ two level wit term).mp
      h1 with
  | inl h =>
      cases (entercollected kinds graph one level wit
          term).mp h with
      | inl h2 => exact Or.inl h2
      | inr h2 => exact Or.inr (Or.inl h2)
  | inr h => exact Or.inr (Or.inr h)

/-- Both joined terms are collected after a join. -/
theorem joincollected [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    collected (join kinds graph one two level wit) one ∧
      collected (join kinds graph one two level wit)
        two := by
  have hv1 := entervalid kinds graph valid one level wit
  have hv2 := entervalid kinds _ hv1 two level wit
  have hcol1 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) one :=
    (entercollected kinds _ two level wit one).mpr
      (Or.inl ((entercollected kinds graph one level
        wit one).mpr (Or.inr rfl)))
  have hcol2 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) two :=
    (entercollected kinds _ two level wit two).mpr
      (Or.inr rfl)
  obtain ⟨ea, hea, hae⟩ := hcol1
  obtain ⟨e1, he1, ht1, -, -⟩ := mergeedges kinds _ hv2
    one two level wit ea hea one one hae hae
  obtain ⟨eb, heb, hbe⟩ := hcol2
  obtain ⟨e2, he2, ht2, -, -⟩ := mergeedges kinds _ hv2
    one two level wit eb heb two two hbe hbe
  exact ⟨⟨e1, he1, ht1⟩, ⟨e2, he2, ht2⟩⟩

/-- The two joined terms stand together after a join. -/
theorem joinsame [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    same (join kinds graph one two level wit) one two := by
  have hv1 := entervalid kinds graph valid one level wit
  have hv2 := entervalid kinds _ hv1 two level wit
  have hcol1 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) one :=
    (entercollected kinds _ two level wit one).mpr
      (Or.inl ((entercollected kinds graph one level
        wit one).mpr (Or.inr rfl)))
  have hcol2 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) two :=
    (entercollected kinds _ two level wit two).mpr
      (Or.inr rfl)
  obtain ⟨ea, hsea, hea, hae⟩ :=
    seekof _ one hcol1
  obtain ⟨eb, hseb, heb, hbe⟩ :=
    seekof _ two hcol2
  by_cases hee : ea = eb
  · have hsame : same
        (enter kinds (enter kinds graph one level wit)
          two level wit) one two :=
      ⟨ea, hea, hae, hee ▸ hbe⟩
    exact (mergegrows kinds _ hv2 one two level
      wit).same one two hsame
  · have h2 : (merge kinds
        (enter kinds (enter kinds graph one level wit)
          two level wit) one two level wit).edges =
        joinEdges
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges one two := by
      simp only [merge, hsea, hseb, hee, ↓reduceIte]
    have hmem : merged ea eb ∈
        (merge kinds
          (enter kinds (enter kinds graph one level wit)
            two level wit) one two level wit).edges := by
      rw [h2, joinEdgesmem _ one two ea eb hsea hseb]
      exact Or.inr rfl
    exact ⟨merged ea eb, hmem,
      List.mem_append_left _ hae,
      List.mem_append_right _ hbe⟩

/-- Equivalence in a join operation comes from the
    graph, or each side reaches a joined term in the
    graph: the joined pair is the only new
    identification a join makes. -/
theorem joinsameback [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym)
    (x y : Term Sym) :
    same (join kinds graph one two level wit) x y →
      same graph x y ∨
        ((same graph x one ∨ x = one ∨
            same graph x two ∨ x = two) ∧
          (same graph y one ∨ y = one ∨
            same graph y two ∨ y = two)) := by
  intro hsame
  have hv1 := entervalid kinds graph valid one level wit
  have hv2 := entervalid kinds _ hv1 two level wit
  have hcol1 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) one :=
    (entercollected kinds _ two level wit one).mpr
      (Or.inl ((entercollected kinds graph one level
        wit one).mpr (Or.inr rfl)))
  have hcol2 : collected
      (enter kinds (enter kinds graph one level wit)
        two level wit) two :=
    (entercollected kinds _ two level wit two).mpr
      (Or.inr rfl)
  obtain ⟨ea, hsea, hea, hae⟩ := seekof _ one hcol1
  obtain ⟨eb, hseb, heb, hbe⟩ := seekof _ two hcol2
  have hdec : ∀ {u v : Term Sym},
      same (enter kinds (enter kinds graph one level
        wit) two level wit) u v →
        same graph u v ∨ (u = v ∧ (u = one ∨ u = two)) := by
    intro u v huv
    have hrw : enter kinds (enter kinds graph one level
        wit) two level wit =
        enterall kinds graph [one, two] level wit := rfl
    rw [hrw] at huv
    cases (enterallsame kinds [one, two] level wit graph
        u v).mp huv with
    | inl h => exact Or.inl h
    | inr h =>
        refine Or.inr ⟨h.1, ?_⟩
        cases List.mem_cons.mp h.2 with
        | inl h3 => exact Or.inl h3
        | inr h3 =>
            cases List.mem_cons.mp h3 with
            | inl h4 => exact Or.inr h4
            | inr h4 => cases h4
  have hcross : ∀ {u v : Term Sym},
      (u = v ∧ (u = one ∨ u = two)) →
        (same graph u one ∨ u = one ∨
            same graph u two ∨ u = two) ∧
          (same graph v one ∨ v = one ∨
            same graph v two ∨ v = two) := by
    intro u v h
    constructor
    · cases h.2 with
      | inl h3 => exact Or.inr (Or.inl h3)
      | inr h3 => exact Or.inr (Or.inr (Or.inr h3))
    · cases h.2 with
      | inl h3 =>
          exact Or.inr (Or.inl (h.1 ▸ h3))
      | inr h3 =>
          exact Or.inr (Or.inr (Or.inr (h.1 ▸ h3)))
  obtain ⟨e, he, hx, hy⟩ := hsame
  by_cases hee : ea = eb
  · have h2 : (merge kinds
        (enter kinds (enter kinds graph one level wit)
          two level wit) one two level wit).edges =
        (enter kinds (enter kinds graph one level wit)
          two level wit).edges := by
      simp only [merge, hsea, hseb, hee, ↓reduceIte]
    have he2 : e ∈
        (enter kinds (enter kinds graph one level wit)
          two level wit).edges := h2 ▸ he
    cases hdec ⟨e, he2, hx, hy⟩ with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (hcross h)
  · have h2 : (merge kinds
        (enter kinds (enter kinds graph one level wit)
          two level wit) one two level wit).edges =
        joinEdges
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges one two := by
      simp only [merge, hsea, hseb, hee, ↓reduceIte]
    have he2 : e ∈ joinEdges
        (enter kinds (enter kinds graph one level wit)
          two level wit).edges one two := h2 ▸ he
    rw [joinEdgesmem _ one two ea eb hsea hseb e] at he2
    cases he2 with
    | inl h =>
        cases hdec ⟨e, h.1, hx, hy⟩ with
        | inl h3 => exact Or.inl h3
        | inr h3 => exact Or.inr (hcross h3)
    | inr h =>
        rw [h] at hx hy
        have hx2 : x ∈ ea.terms ++ eb.terms := hx
        have hy2 : y ∈ ea.terms ++ eb.terms := hy
        have hcomp : ∀ (u : Term Sym),
            u ∈ ea.terms ++ eb.terms →
              same graph u one ∨ u = one ∨
                same graph u two ∨ u = two := by
          intro u hu
          cases List.mem_append.mp hu with
          | inl hu' =>
              cases hdec ⟨ea, hea, hu', hae⟩ with
              | inl hs => exact Or.inl hs
              | inr hs => exact Or.inr (Or.inl hs.1)
          | inr hu' =>
              cases hdec ⟨eb, heb, hu', hbe⟩ with
              | inl hs =>
                  exact Or.inr (Or.inr (Or.inl hs))
              | inr hs =>
                  exact Or.inr (Or.inr (Or.inr hs.1))
        exact Or.inr ⟨hcomp x hx2, hcomp y hy2⟩

/-- The twin relation: every term collected in the
    first graph is collected in the second, and every
    equivalence of the first stands in the second. -/
structure Twin (kinds : Kinds Sym) (g h : Graph Sym) :
    Prop where
  collected : ∀ t, collected g t → collected h t
  same : ∀ x y, same g x y → same h x y

/-- Growth implies twins. -/
theorem growthtwin [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h) :
    Twin kinds g h :=
  { collected := growth.collected
    same := growth.same }

/-- Twins survive an entry on both sides. -/
theorem twinenter [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (twin : Twin kinds g h)
    (term : Term Sym) (level wit : Sym) :
    Twin kinds (enter kinds g term level wit)
      (enter kinds h term level wit) :=
  { collected := fun t ht =>
      (entercollected kinds h term level wit t).mpr
        (match (entercollected kinds g term level wit
          t).mp ht with
          | Or.inl h1 => Or.inl (twin.collected t h1)
          | Or.inr h1 => Or.inr h1)
    same := fun x y hxy =>
      (entersame kinds h term level wit x y).mpr
        (match (entersame kinds g term level wit x y).mp
          hxy with
          | Or.inl h1 => Or.inl (twin.same x y h1)
          | Or.inr h1 => Or.inr h1) }

/-- Twins survive a painting on both sides. -/
theorem twinpaint [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (twin : Twin kinds g h)
    (term : Term Sym) (color : Color Sym)
    (level wit : Sym) :
    Twin kinds (paint kinds g term color level wit)
      (paint kinds h term color level wit) :=
  { collected := fun t ht =>
      (paintcollected kinds h term color level wit
        t).mpr ((paintcollected kinds g term color level
          wit t).mp ht |> twin.collected t)
    same := fun x y hxy =>
      (paintsame kinds h term color level wit x y).mpr
        (twin.same x y
          ((paintsame kinds g term color level wit x
            y).mp hxy)) }

/-- Twins survive a recording on both sides, for a
    level whose terms are distinct and in scope. -/
theorem twinrecord [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (twin : Twin kinds g h)
    (validh : Valid kinds h)
    (level : Level Sym) (wit : Sym) :
    Twin kinds (record kinds g level wit)
      (record kinds h level wit) := by
  have hcol : ∀ t, collected (record kinds g level wit)
      t → collected (record kinds h level wit) t := by
    intro t ht
    by_cases hg : haslevel g level
    · rw [recordstands kinds g level wit hg] at ht
      exact (recordgrows kinds h level wit).collected t
        (twin.collected t ht)
    · have hrecg := recordelse kinds g level wit hg
      have hedg : (record kinds g level wit).edges =
          (enterall kinds g level.terms kinds.record
            wit).edges := by
        simp only [hrecg]
      obtain ⟨e, he, hte⟩ := ht
      have ht2 : collected (enterall kinds g level.terms
          kinds.record wit) t :=
        ⟨e, hedg ▸ he, hte⟩
      cases enterallcollectedback kinds level.terms
          kinds.record wit g t ht2 with
      | inl h1 =>
          exact (recordgrows kinds h level
            wit).collected t (twin.collected t h1)
      | inr h1 =>
          by_cases hh : haslevel h level
          · rw [recordstands kinds h level wit hh]
            obtain ⟨ℓ, hℓ, -, hterms, -⟩ := hh
            obtain ⟨-, hrest⟩ := validh.levels ℓ hℓ
            exact (hrest t (hterms ▸ h1)).1
          · have hrech := recordelse kinds h level wit hh
            have hedh : (record kinds h level wit).edges =
                (enterall kinds h level.terms kinds.record
                  wit).edges := by
              simp only [hrech]
            obtain ⟨e2, he2, hte2⟩ :=
              enterallcollected kinds level.terms
                kinds.record wit h t h1
            exact ⟨e2, hedh ▸ he2, hte2⟩
  refine { collected := hcol, same := ?_ }
  intro x y hxy
  by_cases hg : haslevel g level
  · rw [recordstands kinds g level wit hg] at hxy
    exact (recordgrows kinds h level wit).same x y
      (twin.same x y hxy)
  · have hrecg := recordelse kinds g level wit hg
    have hedg : (record kinds g level wit).edges =
        (enterall kinds g level.terms kinds.record
          wit).edges := by
      simp only [hrecg]
    obtain ⟨e, he, hx, hy⟩ := hxy
    have hxy2 : same (enterall kinds g level.terms
        kinds.record wit) x y :=
      ⟨e, hedg ▸ he, hx, hy⟩
    cases (enterallsame kinds level.terms kinds.record
        wit g x y).mp hxy2 with
    | inl h1 =>
        exact (recordgrows kinds h level wit).same x y
          (twin.same x y h1)
    | inr h1 =>
        have hcolx : collected (record kinds h level
            wit) x := hcol x (by
          rw [h1.1]
          exact ⟨e, he, hy⟩)
        exact h1.1 ▸ samerefl _ _ hcolx

/-- Twins survive a join on both sides, on valid
    graphs. -/
theorem twinjoin [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (twin : Twin kinds g h)
    (validg : Valid kinds g) (validh : Valid kinds h)
    (one two : Term Sym) (level wit : Sym) :
    Twin kinds (join kinds g one two level wit)
      (join kinds h one two level wit) := by
  have hvalid : Valid kinds
      (join kinds h one two level wit) :=
    joinvalid kinds h validh one two level wit
  have hjc := joincollected kinds h validh one two
    level wit
  have hjs := joinsame kinds h validh one two level wit
  have hgrows : Growth kinds h
      (join kinds h one two level wit) :=
    joingrows kinds h validh one two level wit
  refine { collected := ?_, same := ?_ }
  · intro t ht
    cases joincollectedback kinds g one two level wit
        t ht with
    | inl h1 =>
        exact hgrows.collected t (twin.collected t h1)
    | inr h1 =>
        cases h1 with
        | inl h2 => exact h2 ▸ hjc.1
        | inr h2 => exact h2 ▸ hjc.2
  · intro x y hxy
    cases joinsameback kinds g validg one two level wit
        x y hxy with
    | inl h1 =>
        exact hgrows.same x y (twin.same x y h1)
    | inr h1 =>
        obtain ⟨hx, hy⟩ := h1
        have haj : ∀ {u : Term Sym},
            (same g u one ∨ u = one) →
              same (join kinds h one two level wit)
                u one := by
          intro u hu
          cases hu with
          | inl hs =>
              exact hgrows.same u one (twin.same u one hs)
          | inr he =>
              rw [he]
              exact samerefl _ _ hjc.1
        have hbj : ∀ {u : Term Sym},
            (same g u two ∨ u = two) →
              same (join kinds h one two level wit)
                u two := by
          intro u hu
          cases hu with
          | inl hs =>
              exact hgrows.same u two (twin.same u two hs)
          | inr he =>
              rw [he]
              exact samerefl _ _ hjc.2
        have hxa : same (join kinds h one two level wit)
            x one ∨
            same (join kinds h one two level wit)
              x two := by
          cases hx with
          | inl h2 => exact Or.inl (haj (Or.inl h2))
          | inr h2 =>
              cases h2 with
              | inl h3 => exact Or.inl (haj (Or.inr h3))
              | inr h3 =>
                  cases h3 with
                  | inl h4 =>
                      exact Or.inr (hbj (Or.inl h4))
                  | inr h4 =>
                      exact Or.inr (hbj (Or.inr h4))
        have hya : same (join kinds h one two level wit)
            y one ∨
            same (join kinds h one two level wit)
              y two := by
          cases hy with
          | inl h2 => exact Or.inl (haj (Or.inl h2))
          | inr h2 =>
              cases h2 with
              | inl h3 => exact Or.inl (haj (Or.inr h3))
              | inr h3 =>
                  cases h3 with
                  | inl h4 =>
                      exact Or.inr (hbj (Or.inl h4))
                  | inr h4 =>
                      exact Or.inr (hbj (Or.inr h4))
        cases hxa with
        | inl h2 =>
            cases hya with
            | inl h3 =>
                exact sametrans kinds _ hvalid h2
                  (samesymm _ h3)
            | inr h3 =>
                exact sametrans kinds _ hvalid
                  (sametrans kinds _ hvalid h2 hjs)
                  (samesymm _ h3)
        | inr h2 =>
            cases hya with
            | inl h3 =>
                exact sametrans kinds _ hvalid
                  (sametrans kinds _ hvalid h2
                    (samesymm _ hjs))
                  (samesymm _ h3)
            | inr h3 =>
                exact sametrans kinds _ hvalid h2
                  (samesymm _ h3)

/-- Twins survive one operation applied on both sides:
    the step condition of a record is the level
    hypothesis of the record operation. -/
theorem twinop [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (twin : Twin kinds g h)
    (validg : Valid kinds g) (validh : Valid kinds h)
    (op : Op Sym) :
    Twin kinds (apply kinds g op) (apply kinds h op) := by
  cases op with
  | enter t l w => exact twinenter kinds twin t l w
  | join a b l w =>
      exact twinjoin kinds twin validg validh a b l w
  | record lv w =>
      exact twinrecord kinds twin validh lv w
  | paint t c l w => exact twinpaint kinds twin t c l w

/-- One run from twin starts ends in twins: everything
    the run collects or identifies from the first start
    it also collects or identifies from the second. -/
theorem runmono [DecidableEq Sym] (kinds : Kinds Sym) :
    ∀ (ops : List (Op Sym)) {g h : Graph Sym},
      Twin kinds g h → Valid kinds g → Valid kinds h →
      Ready kinds g ops → Ready kinds h ops →
      Twin kinds (run kinds g ops)
        (run kinds h ops) := by
  intro ops
  induction ops with
  | nil =>
      intro g h twin _ _ _ _
      exact twin
  | cons op rest ih =>
      intro g h twin validg validh readyg readyh
      cases readyg with
      | more _ opf stepg tailg =>
          cases readyh with
          | more _ opf steph tailh =>
              rw [runcons, runcons]
              exact ih
                (twinop kinds twin validg validh op)
                (readystart kinds tailg)
                (readystart kinds tailh) tailg tailh

/-- Ready runs concatenate: a ready run of the second
    append from the graph the first reaches makes the
    joined list ready from the start. -/
theorem readyappend [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {first second : List (Op Sym)}
    (ready1 : Ready kinds g first) :
    Ready kinds (run kinds g first) second →
      Ready kinds g (first ++ second) := by
  induction ready1 with
  | done valid =>
      intro ready2
      exact ready2
  | more valid op step tail ih =>
      intro ready2
      refine Ready.more valid op step ?_
      apply ih
      rw [runcons] at ready2
      exact ready2

/- ## Claim two: compound

    Compounding is accumulation of effective joins. The
    excess after both appends is exactly the common
    excess plus the effective joins of the two appends
    together, counted at their moments; it is at least
    the excess after each append alone — the first by
    the accumulation itself, the second by excess
    monotonicity, since the second append's run from
    the common graph is collected and identified inside
    its run after the first append, by runmono. No
    additive claim over shared content is stated:
    shared content is collected once. -/

/-- Claim two, exact: the excess after both appends is
    the common excess plus the effective joins of the
    first append plus the effective joins of the second
    append counted from the graph the first reaches. -/
theorem compound [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {first second : List (Op Sym)}
    (ready1 : Ready kinds g first)
    (ready2 : Ready kinds (run kinds g first) second) :
    excess (run kinds g (first ++ second)) =
      excess g + joins kinds g first +
        joins kinds (run kinds g first) second := by
  have h := runexcess kinds
    (readyappend kinds ready1 ready2)
  rw [joinsappend] at h
  omega

/-- Claim two, at least the first append alone. -/
theorem compoundge [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {first second : List (Op Sym)}
    (ready1 : Ready kinds g first)
    (ready2 : Ready kinds (run kinds g first) second) :
    excess (run kinds g first) ≤
      excess (run kinds g (first ++ second)) := by
  have h1 := runexcess kinds ready1
  have h2 := compound kinds ready1 ready2
  omega

/-- Claim two, at least the second append alone: the
    second append's excess from the common graph is at
    most its excess inside the combined run, by excess
    monotonicity over the twin inclusion. -/
theorem compoundge2 [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {first second : List (Op Sym)}
    (ready1 : Ready kinds g first)
    (ready2alone : Ready kinds g second)
    (ready2 : Ready kinds (run kinds g first) second) :
    excess (run kinds g second) ≤
      excess (run kinds g (first ++ second)) := by
  have htwin := runmono kinds second
    (growthtwin kinds (rungrows kinds ready1))
    (readystart kinds ready2alone)
    (readystart kinds ready2) ready2alone ready2
  rw [← runappend] at htwin
  exact excessmono kinds (runvalid kinds ready2alone)
    (runvalid kinds (readyappend kinds ready1 ready2))
    htwin.collected htwin.same

/-- Seeking in an appended list finds what the first
    list finds. -/
theorem seekappendleft [DecidableEq Sym] :
    ∀ (l₁ l₂ : List (Edge Sym)) (term : Term Sym)
      (e : Edge Sym),
      seek l₁ term = some e →
        seek (l₁ ++ l₂) term = some e := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ term e h; cases h
  | cons x xs ih =>
      intro l₂ term e h
      by_cases hx : term ∈ x.terms
      · have h1 : seek (x :: xs) term = some x := by
          simp only [seek, hx, ↓reduceIte]
        rw [h1] at h
        simp only [List.cons_append, seek, hx,
          ↓reduceIte, h]
      · have h1 : seek (x :: xs) term = seek xs term := by
          simp only [seek, hx, ↓reduceIte]
        rw [h1] at h
        simp only [List.cons_append, seek, hx,
          ↓reduceIte]
        exact ih l₂ term e h

/-- Seeking an uncollected term in a list with its
    singleton appended finds the singleton. -/
theorem seekappend [DecidableEq Sym] :
    ∀ (l : List (Edge Sym)) (term : Term Sym),
      (∀ e ∈ l, term ∉ e.terms) →
        seek (l ++ [{ terms := [term], colors := [] }])
            term =
          some { terms := [term], colors := [] } := by
  intro l
  induction l with
  | nil =>
      intro term _
      simp [seek]
  | cons x xs ih =>
      intro term hall
      have hx : term ∉ x.terms := hall x (by simp)
      have hxs : ∀ e ∈ xs, term ∉ e.terms :=
        fun e he => hall e (List.mem_cons_of_mem x he)
      simp only [List.cons_append, seek, hx, ↓reduceIte]
      exact ih term hxs

/-- Entering an unsought term appends exactly its
    singleton to the edge list. -/
theorem enteredgesnone [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (term : Term Sym) (level wit : Sym)
    (h : seek graph.edges term = none) :
    (enter kinds graph term level wit).edges =
      graph.edges ++ [{ terms := [term], colors := [] }] := by
  simp only [enter, h]

/-- The effective join count of a join, characterized:
    it is one exactly when the two terms are distinct
    and do not already stand together. -/
theorem effone [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    eff kinds graph one two level wit = 1 ↔
      one ≠ two ∧ ¬ same graph one two := by
  have hent : ∀ (t : Term Sym),
      collected (enter kinds graph one level wit) t ↔
        collected graph t ∨ t = one :=
    fun t => entercollected kinds graph one level wit t
  by_cases hcol1 : collected graph one
  · by_cases hcol2 : collected graph two
    · have he1 : (enter kinds graph one level
          wit).edges = graph.edges :=
        enteredgesof kinds graph one level wit hcol1
      have hcol2' : collected
          (enter kinds graph one level wit) two :=
        (hent two).mpr (Or.inl hcol2)
      have he2 : (enter kinds
          (enter kinds graph one level wit) two level
          wit).edges = graph.edges := by
        have h := enteredgesof kinds _ two level wit
          hcol2'
        rw [he1] at h
        exact h
      obtain ⟨ea, hsea, hea, hae⟩ :=
        seekof graph.edges one hcol1
      obtain ⟨eb, hseb, heb, hbe⟩ :=
        seekof graph.edges two hcol2
      have hseek1 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges one = some ea := by
        rw [he2]
        exact hsea
      have hseek2 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges two = some eb := by
        rw [he2]
        exact hseb
      have heff : eff kinds graph one two level wit =
          (if ea = eb then 0 else 1) := by
        simp only [eff, hseek1, hseek2]
      rw [heff]
      constructor
      · intro h
        by_cases hee : ea = eb
        · simp only [hee, ↓reduceIte] at h
          cases h
        · refine ⟨?_, ?_⟩
          · intro heq
            apply hee
            have : seek graph.edges one =
                seek graph.edges two := by rw [heq]
            rw [hsea, hseb] at this
            exact Option.some.inj this
          · intro hs
            obtain ⟨e, he, h1, h2⟩ := hs
            apply hee
            have h1' : e = ea :=
              valid.disjoint e he ea hea one h1 hae
            have h2' : e = eb :=
              valid.disjoint e he eb heb two h2 hbe
            exact h1'.symm.trans h2'
      · intro h
        by_cases hee : ea = eb
        · exfalso
          exact h.2 ⟨ea, hea, hae, hee ▸ hbe⟩
        · simp only [hee, ↓reduceIte]
    · have he1 : (enter kinds graph one level
          wit).edges = graph.edges :=
        enteredgesof kinds graph one level wit hcol1
      have hnc2 : ¬ collected
          (enter kinds graph one level wit) two := by
        intro hc
        cases (hent two).mp hc with
        | inl h => exact hcol2 h
        | inr h => subst h; exact hcol2 hcol1
      have hsnone : seek
          (enter kinds graph one level wit).edges
            two = none := by
        by_cases h : seek
            (enter kinds graph one level wit).edges
              two = none
        · exact h
        · cases hso : seek
              (enter kinds graph one level wit).edges
                two with
          | none => rfl
          | some found =>
              obtain ⟨hfin, hfterm⟩ := seeksome _ two
                found hso
              exact absurd ⟨found, hfin, hfterm⟩ hnc2
      have he2 : (enter kinds
          (enter kinds graph one level wit) two level
          wit).edges =
          graph.edges ++
            [{ terms := [two], colors := [] }] := by
        have h := enteredgesnone kinds _ two level wit
          hsnone
        rw [he1] at h
        exact h
      obtain ⟨ea, hsea, hea, hae⟩ :=
        seekof graph.edges one hcol1
      have hseek1 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges one = some ea := by
        rw [he2]
        exact seekappendleft _ _ one ea hsea
      have hseek2 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges two =
          some { terms := [two], colors := [] } := by
        rw [he2]
        apply seekappend
        intro e he
        intro ht
        exact hcol2 ⟨e, he, ht⟩
      have heff : eff kinds graph one two level wit =
          (if ea = { terms := [two], colors := [] }
            then 0 else 1) := by
        simp only [eff, hseek1, hseek2]
      have hne : ea ≠ { terms := [two], colors := [] } := by
        intro heq
        apply hcol2
        have h2 : two ∈ ea.terms := by
          rw [heq]
          simp
        exact ⟨ea, hea, h2⟩
      rw [heff, if_neg hne]
      constructor
      · intro _
        refine ⟨?_, ?_⟩
        · intro heq
          subst heq
          exact hcol2 hcol1
        · intro hs
          obtain ⟨e, he, -, h2⟩ := hs
          exact hcol2 ⟨e, he, h2⟩
      · intro _
        rfl
  · by_cases hcol2 : collected graph two
    · have hnc1 : ¬ collected graph one := hcol1
      have hsnone : seek graph.edges one = none := by
        by_cases h : seek graph.edges one = none
        · exact h
        · cases hso : seek graph.edges one with
          | none => rfl
          | some found =>
              obtain ⟨hfin, hfterm⟩ :=
                seeksome graph.edges one found hso
              exact absurd ⟨found, hfin, hfterm⟩ hnc1
      have he1 : (enter kinds graph one level
          wit).edges =
          graph.edges ++
            [{ terms := [one], colors := [] }] := by
        simp only [enter, hsnone]
      have hcol2' : collected
          (enter kinds graph one level wit) two :=
        (hent two).mpr (Or.inl hcol2)
      have he2 : (enter kinds
          (enter kinds graph one level wit) two level
          wit).edges =
          graph.edges ++
            [{ terms := [one], colors := [] }] := by
        have h := enteredgesof kinds _ two level wit
          hcol2'
        rw [he1] at h
        exact h
      obtain ⟨eb, hseb, heb, hbe⟩ :=
        seekof graph.edges two hcol2
      have hseek1 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges one =
          some { terms := [one], colors := [] } := by
        rw [he2]
        apply seekappend
        intro e he
        intro ht
        exact hnc1 ⟨e, he, ht⟩
      have hseek2 : seek
          (enter kinds (enter kinds graph one level wit)
            two level wit).edges two = some eb := by
        rw [he2]
        exact seekappendleft _ _ two eb hseb
      have heff : eff kinds graph one two level wit =
          (if { terms := [one], colors := [] } = eb
            then 0 else 1) := by
        simp only [eff, hseek1, hseek2]
      have hne : ({ terms := [one], colors := [] } :
          Edge Sym) ≠ eb := by
        intro heq
        apply hnc1
        exact ⟨eb, heb, heq ▸ (by simp : one ∈
          ({ terms := [one], colors := [] } :
            Edge Sym).terms)⟩
      rw [heff, if_neg hne]
      constructor
      · intro _
        refine ⟨?_, ?_⟩
        · intro heq
          subst heq
          exact hnc1 hcol2
        · intro hs
          obtain ⟨e, he, h1, -⟩ := hs
          exact hnc1 ⟨e, he, h1⟩
      · intro _
        rfl
    · by_cases heq : one = two
      · subst heq
        have hs1 : seek
            (enter kinds graph one level wit).edges
              one =
            some { terms := [one], colors := [] } := by
          have hsnone : seek graph.edges one = none := by
            by_cases h : seek graph.edges one = none
            · exact h
            · cases hso : seek graph.edges one with
              | none => rfl
              | some found =>
                  obtain ⟨hfin, hfterm⟩ :=
                    seeksome graph.edges one found hso
                  exact absurd ⟨found, hfin, hfterm⟩ hcol1
          have he1 : (enter kinds graph one level
              wit).edges =
              graph.edges ++
                [{ terms := [one], colors := [] }] := by
            simp only [enter, hsnone]
          rw [he1]
          apply seekappend
          intro e he ht
          exact hcol1 ⟨e, he, ht⟩
        have hcol' : collected
            (enter kinds graph one level wit) one :=
          (hent one).mpr (Or.inr rfl)
        have he2 : (enter kinds
            (enter kinds graph one level wit) one level
            wit).edges =
            (enter kinds graph one level wit).edges :=
          enteredgesof kinds _ one level wit hcol'
        have heff : eff kinds graph one one level wit =
            (if ({ terms := [one], colors := [] } :
                Edge Sym) =
              { terms := [one], colors := [] }
              then 0 else 1) := by
          simp only [eff, he2, hs1]
        rw [heff, if_pos rfl]
        constructor
        · intro h
          cases h
        · intro h
          exact absurd rfl h.1
      · have hsnone1 : seek graph.edges one = none := by
          by_cases h : seek graph.edges one = none
          · exact h
          · cases hso : seek graph.edges one with
            | none => rfl
            | some found =>
                obtain ⟨hfin, hfterm⟩ :=
                  seeksome graph.edges one found hso
                exact absurd ⟨found, hfin, hfterm⟩ hcol1
        have he1 : (enter kinds graph one level
            wit).edges =
            graph.edges ++
              [{ terms := [one], colors := [] }] := by
          simp only [enter, hsnone1]
        have hnc2 : ¬ collected
            (enter kinds graph one level wit) two := by
          intro hc
          cases (hent two).mp hc with
          | inl h => exact hcol2 h
          | inr h => exact heq h.symm
        have hsnone2 : seek
            (enter kinds graph one level wit).edges
              two = none := by
          by_cases h : seek
              (enter kinds graph one level wit).edges
                two = none
          · exact h
          · cases hso : seek
                (enter kinds graph one level wit).edges
                  two with
            | none => rfl
            | some found =>
                obtain ⟨hfin, hfterm⟩ := seeksome _ two
                  found hso
                exact absurd ⟨found, hfin, hfterm⟩ hnc2
        have he2 : (enter kinds
            (enter kinds graph one level wit) two level
            wit).edges =
            (graph.edges ++
              [{ terms := [one], colors := [] }]) ++
              [{ terms := [two], colors := [] }] := by
          have h := enteredgesnone kinds _ two level
            wit hsnone2
          rw [he1] at h
          exact h
        have hseek1 : seek
            (enter kinds (enter kinds graph one level
              wit) two level wit).edges one =
            some { terms := [one], colors := [] } := by
          rw [he2]
          apply seekappendleft
          apply seekappend
          intro e he ht
          exact hcol1 ⟨e, he, ht⟩
        have hseek2 : seek
            (enter kinds (enter kinds graph one level
              wit) two level wit).edges two =
            some { terms := [two], colors := [] } := by
          rw [he2]
          apply seekappend
          intro e he ht
          cases List.mem_append.mp he with
          | inl h => exact hcol2 ⟨e, h, ht⟩
          | inr h =>
              rw [List.mem_singleton] at h
              rw [h] at ht
              have h2 : two = one := by
                have h3 : two ∈
                    ({ terms := [one], colors := [] } :
                      Edge Sym).terms := ht
                simpa using h3
              exact heq h2.symm
        have heff : eff kinds graph one two level wit =
            (if ({ terms := [one], colors := [] } :
                Edge Sym) =
              { terms := [two], colors := [] }
              then 0 else 1) := by
          simp only [eff, hseek1, hseek2]
        have hne : ({ terms := [one], colors := [] } :
            Edge Sym) ≠
            { terms := [two], colors := [] } := by
          intro h
          apply heq
          have h1 : one ∈
              ({ terms := [one], colors := [] } :
                Edge Sym).terms := by simp
          rw [h] at h1
          simpa using h1
        rw [heff, if_neg hne]
        constructor
        · intro _
          refine ⟨heq, ?_⟩
          intro hs
          obtain ⟨e, he, h1, -⟩ := hs
          exact hcol1 ⟨e, he, h1⟩
        · intro _
          rfl

/- ## Claim three: appear

    Appearance: two appends that each leave the excess
    at the common excess, followed by one equivalence
    joining a term of the first append to a distinct
    term of the second that do not already stand
    together, raise the excess by exactly one. The
    control direction is stated under the separateness
    premise named alone: the second append's effective
    joins counted from the graph the first append
    reaches are exactly its effective joins counted
    from the common graph. That premise is the precise
    content of "no cross join and no shared term"; it
    is discharged on the concrete control in the
    controls file by computation. -/

/-- The separateness premise of the control direction:
    no cross join and no shared term, stated as the
    equality of the second append's effective join
    counts from the two starts. Its falsification
    route: exhibit two appends to a common graph, with
    a shared term or a cross identification, whose
    combined second-append count differs from the
    alone count. -/
def alone [DecidableEq Sym] (kinds : Kinds Sym)
    (g : Graph Sym) (first second : List (Op Sym)) :
    Prop :=
  joins kinds (run kinds g first) second =
    joins kinds g second

/-- Claim three, appearance: the cross join raises the
    excess to exactly one above the common graph's. -/
theorem appear [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym}
    {first second : List (Op Sym)}
    (ready1 : Ready kinds g first)
    (ready2alone : Ready kinds g second)
    (ready2 : Ready kinds (run kinds g first) second)
    (hfirst : joins kinds g first = 0)
    (hsecond : joins kinds (run kinds g first) second = 0)
    (one two : Term Sym) (level wit : Sym)
    (hone : collected (run kinds g first) one)
    (htwo : collected (run kinds g second) two)
    (hne : one ≠ two)
    (hnsame : ¬ same (run kinds g (first ++ second))
      one two) :
    excess (run kinds g
      ((first ++ second) ++
        [Op.join one two level wit])) =
        excess g + 1 := by
  have hcomb : Ready kinds g (first ++ second) :=
    readyappend kinds ready1 ready2
  have hvalid : Valid kinds
      (run kinds g (first ++ second)) :=
    runvalid kinds hcomb
  have hcol1 : collected (run kinds g (first ++ second))
      one := by
    have h := (rungrows kinds ready2).collected one
      hone
    rwa [← runappend] at h
  have hcol2 : collected (run kinds g (first ++ second))
      two := by
    have htwin := runmono kinds second
      (growthtwin kinds (rungrows kinds ready1))
      (readystart kinds ready2alone)
      (readystart kinds ready2) ready2alone ready2
    rw [← runappend] at htwin
    exact htwin.collected two htwo
  have heff : eff kinds (run kinds g (first ++ second))
      one two level wit = 1 :=
    (effone kinds _ hvalid one two level wit).mpr
      ⟨hne, hnsame⟩
  have hready : Ready kinds g
      ((first ++ second) ++
        [Op.join one two level wit]) := by
    apply readyappend kinds hcomb
    exact Ready.more hvalid _ True.intro
      (Ready.done (joinvalid kinds _ hvalid one two
        level wit))
  have h := runexcess kinds hready
  have hsingle : joins kinds
      (run kinds g (first ++ second))
      [Op.join one two level wit] =
      eff kinds (run kinds g (first ++ second)) one two
        level wit := rfl
  rw [joinsappend, joinsappend, hfirst, hsecond,
    hsingle, heff] at h
  omega

/-- Claim three, control direction: under the
    separateness premise, the combined excess is
    exactly the common excess plus the two appends'
    deltas, each computed alone. -/
theorem appearcontrol [DecidableEq Sym]
    (kinds : Kinds Sym)
    {g : Graph Sym} {first second : List (Op Sym)}
    (ready1 : Ready kinds g first)
    (ready2 : Ready kinds (run kinds g first) second)
    (halone : alone kinds g first second) :
    excess (run kinds g (first ++ second)) =
      excess g + joins kinds g first +
        joins kinds g second := by
  have h := runexcess kinds
    (readyappend kinds ready1 ready2)
  rw [joinsappend, halone] at h
  omega

/- ## Claim four: coloring

    Color union is commutative, associative and
    idempotent up to membership — the only reading a
    color list carries. Painting never loses a color:
    every color of every old edge stands after the
    paint on an edge with the same terms. The two
    filters of the frontier home are then kept apart:
    the derived mark of a painter on an edge is the
    intended mark exactly when that painter has both
    an observation entry and an intent entry on the
    edge, and an intended qualification mark implies
    both, under the stated discipline premise. -/

/-- Claim four: color union commutes, up to
    membership. -/
theorem unioncomm [DecidableEq Sym] (a b : List (Color Sym))
    (c : Color Sym) :
    c ∈ union a b ↔ c ∈ union b a := by
  rw [memunion, memunion]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h

/-- Claim four: color union associates, up to
    membership. -/
theorem unionassoc [DecidableEq Sym]
    (a b d : List (Color Sym)) (c : Color Sym) :
    c ∈ union (union a b) d ↔ c ∈ union a (union b d) := by
  simp only [memunion]
  constructor
  · intro h
    cases h with
    | inl h =>
        cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  · intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
        cases h with
        | inl h => exact Or.inl (Or.inr h)
        | inr h => exact Or.inr h

/-- Claim four: color union is idempotent, up to
    membership. -/
theorem unionidem [DecidableEq Sym] (a : List (Color Sym))
    (c : Color Sym) :
    c ∈ union a a ↔ c ∈ a := by
  rw [memunion]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact h
  · intro h
    exact Or.inl h

/-- Claim four: painting keeps every color of every
    old edge, on an edge with the same terms. -/
theorem paintkeeps [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym)
    (color : Color Sym) (level wit : Sym) :
    ∀ old ∈ graph.edges, ∀ c ∈ old.colors,
      ∃ e' ∈ (paint kinds graph term color level
        wit).edges,
        e'.terms = old.terms ∧ c ∈ e'.colors :=
  fun old hold c hc => paintcolors kinds graph term
    color level wit old hold c hc

/-- The frontier home's two filters, as one
    qualification record: the observation kind, the
    intent kind, the qualification kind, and the four
    marks, with the distinctness the reading needs. -/
structure Qual (Sym : Type) where
  /-- The observation entry kind. -/
  obs : Sym
  /-- The intent entry kind. -/
  intent : Sym
  /-- The qualification entry kind. -/
  qual : Sym
  /-- The intended mark. -/
  intended : Sym
  /-- The stray mark: observed, not wanted. -/
  stray : Sym
  /-- The gap mark: wanted, not observed. -/
  gap : Sym
  /-- The unknown mark: neither. -/
  unknown : Sym
  /-- The marks differ, and the qualification kind is
      neither entry kind. -/
  distinct : intended ≠ stray ∧ intended ≠ gap ∧
    intended ≠ unknown ∧ obs ≠ qual ∧ intent ≠ qual

/-- The observation filter: the painter has an
    observation entry on the edge. -/
def seen [DecidableEq Sym] (q : Qual Sym) (who : Sym)
    (edge : Edge Sym) : Prop :=
  ∃ c ∈ edge.colors, c.who = who ∧ c.kind = q.obs

/-- The intent filter: the painter has an intent
    entry on the edge. -/
def wanted [DecidableEq Sym] (q : Qual Sym) (who : Sym)
    (edge : Edge Sym) : Prop :=
  ∃ c ∈ edge.colors, c.who = who ∧ c.kind = q.intent

/-- The observation filter, as a boolean test. -/
def seenb [DecidableEq Sym] (q : Qual Sym) (who : Sym)
    (edge : Edge Sym) : Bool :=
  edge.colors.any (fun c => decide (c.who = who) &&
    decide (c.kind = q.obs))

/-- The intent filter, as a boolean test. -/
def wantedb [DecidableEq Sym] (q : Qual Sym) (who : Sym)
    (edge : Edge Sym) : Bool :=
  edge.colors.any (fun c => decide (c.who = who) &&
    decide (c.kind = q.intent))

/-- The boolean observation test reads the filter. -/
theorem seeniff [DecidableEq Sym] (q : Qual Sym)
    (who : Sym) (edge : Edge Sym) :
    seenb q who edge = true ↔ seen q who edge := by
  simp only [seenb, seen, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]

/-- The boolean intent test reads the filter. -/
theorem wantediff [DecidableEq Sym] (q : Qual Sym)
    (who : Sym) (edge : Edge Sym) :
    wantedb q who edge = true ↔ wanted q who edge := by
  simp only [wantedb, wanted, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]

/-- The derived mark of a painter on an edge, from the
    two boolean filters: intended when both filters
    pass, stray when only observation passes, gap when
    only intent passes, unknown when neither does.
    The filters are never conflated: the mark is a
    reading of the two, not a third entry kind. -/
def derived [DecidableEq Sym] (q : Qual Sym) (who : Sym)
    (edge : Edge Sym) : Sym :=
  if seenb q who edge && wantedb q who edge then
    q.intended
  else if seenb q who edge then q.stray
  else if wantedb q who edge then q.gap
  else q.unknown

/-- The two-filter theorem: the derived mark is the
    intended mark exactly when both filters pass for
    that painter on that edge. -/
theorem derivedintended [DecidableEq Sym] (q : Qual Sym)
    (who : Sym) (edge : Edge Sym) :
    derived q who edge = q.intended ↔
      seen q who edge ∧ wanted q who edge := by
  by_cases hs : seenb q who edge = true
  · by_cases hw : wantedb q who edge = true
    · have hs2 : seen q who edge :=
        (seeniff q who edge).mp hs
      have hw2 : wanted q who edge :=
        (wantediff q who edge).mp hw
      have hder : derived q who edge = q.intended := by
        simp only [derived, hs, hw, Bool.true_and,
          ↓reduceIte]
      rw [hder]
      exact ⟨fun _ => ⟨hs2, hw2⟩, fun _ => rfl⟩
    · have hwf : wantedb q who edge = false := by
        cases h : wantedb q who edge with
        | true => exact absurd h hw
        | false => rfl
      have hder : derived q who edge = q.stray := by
        simp [derived, hs, hwf]
      rw [hder]
      constructor
      · intro h
        exact absurd h.symm q.distinct.1
      · intro h
        exact absurd ((wantediff q who edge).mpr h.2)
          (by simp [hwf])
  · have hsf : seenb q who edge = false := by
      cases h : seenb q who edge with
      | true => exact absurd h hs
      | false => rfl
    by_cases hw : wantedb q who edge = true
    · have hn1 : ¬ ((seenb q who edge &&
          wantedb q who edge) = true) := by
        intro h
        rw [Bool.and_eq_true] at h
        rw [hsf] at h
        exact Bool.noConfusion h.1
      have hn2 : ¬ (seenb q who edge = true) := by
        intro h
        rw [hsf] at h
        cases h
      have hder : derived q who edge = q.gap := by
        unfold derived
        rw [if_neg hn1, if_neg hn2, if_pos hw]
      rw [hder]
      constructor
      · intro h
        exact absurd h.symm q.distinct.2.1
      · intro h
        exact absurd ((seeniff q who edge).mpr h.1)
          (by simp [hsf])
    · have hwf : wantedb q who edge = false := by
        cases h : wantedb q who edge with
        | true => exact absurd h hw
        | false => rfl
      have hder : derived q who edge = q.unknown := by
        simp [derived, hsf, hwf]
      rw [hder]
      constructor
      · intro h
        exact absurd h.symm q.distinct.2.2.1
      · intro h
        exact absurd ((seeniff q who edge).mpr h.1)
          (by simp [hsf])

/-- The two-filter theorem, qualification direction:
    under the discipline premise — a qualification
    entry carries the intended mark only where its
    painter's derived mark is intended — an intended
    qualification mark on an edge implies both filters
    pass for its painter. The premise is explicit; its
    falsification route is a graph and edge where an
    intended qualification mark stands while an
    observation or intent entry of its painter is
    missing. -/
theorem intendedneeds [DecidableEq Sym] (q : Qual Sym)
    (graph : Graph Sym)
    (discipline : ∀ edge ∈ graph.edges,
      ∀ c ∈ edge.colors, c.kind = q.qual →
        c.mark = q.intended →
          derived q c.who edge = q.intended)
    (edge : Edge Sym) (hedge : edge ∈ graph.edges)
    (c : Color Sym) (hc : c ∈ edge.colors)
    (hkind : c.kind = q.qual)
    (hmark : c.mark = q.intended) :
    seen q c.who edge ∧ wanted q c.who edge :=
  (derivedintended q c.who edge).mp
    (discipline edge hedge c hc hkind hmark)

/- ## Claim five: bounds

    Leastness, saturation and finiteness of the bound
    are the section seven theorems of the core file,
    boundleast, boundsat and boundfin. Here: the
    membership reading of the bound, its growth along
    the growth relation, and the recorded bound kept
    apart from the recomputed reading — the log entry
    a record appends stands in every later graph with
    its terms field, the bound as taken at append
    time, unchanged. -/

/-- The bound's membership reading: a term is in the
    bound exactly when some edge holding it meets the
    level. -/
theorem boundmem [DecidableEq Sym] (graph : Graph Sym)
    (level : Level Sym) (term : Term Sym) :
    term ∈ bound graph level ↔
      ∃ e ∈ graph.edges, term ∈ e.terms ∧
        ∃ s ∈ e.terms, s ∈ level.terms := by
  simp only [bound, List.mem_flatMap, List.mem_filter,
    List.any_eq_true]
  constructor
  · intro h
    obtain ⟨e, ⟨he, ⟨s, hs, hs2⟩⟩, ht⟩ := h
    exact ⟨e, he, ht, s, hs, of_decide_eq_true hs2⟩
  · intro h
    obtain ⟨e, he, ht, s, hs, hs2⟩ := h
    exact ⟨e, ⟨he, ⟨s, hs, by simp [hs2]⟩⟩, ht⟩

/-- The bound grows along the growth relation: every
    term of the earlier bound is in the later bound,
    on a valid later graph. -/
theorem boundgrows [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h)
    (validh : Valid kinds h) (level : Level Sym) :
    ∀ term ∈ bound g level, term ∈ bound h level := by
  intro term ht
  rw [boundmem] at ht
  obtain ⟨e, he, hte, s, hs, hsl⟩ := ht
  rw [boundmem]
  have hcol : collected h s :=
    growth.collected s ⟨e, he, hs⟩
  obtain ⟨e', he', hs'⟩ := hcol
  refine ⟨e', he', ?_, s, hs', hsl⟩
  have hsame : same h s term :=
    growth.same s term ⟨e, he, hs, hte⟩
  obtain ⟨e'', he'', hs'', ht''⟩ := hsame
  have heq : e'' = e' :=
    validh.disjoint e'' he'' e' he' s hs'' hs'
  exact heq ▸ ht''

/-- The log only grows: every entry of the earlier
    graph stands in the later graph's log. -/
theorem boundrecord [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h)
    (e : Entry Sym) (he : e ∈ g.log) : e ∈ h.log := by
  obtain ⟨rest, hr⟩ := growth.logpre
  rw [hr]
  exact List.mem_append_left _ he

/-- The recorded bound, kept apart from the reading:
    the entry a record appends stands in every later
    grown graph's log, with its terms field still the
    bound as taken at append time — the recomputed
    reading of the later graph is a separate value,
    bound of that graph, not this entry. -/
theorem boundrecorded [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym)
    (h : ¬ haslevel graph level)
    {later : Graph Sym}
    (growth : Growth kinds (record kinds graph level
      wit) later) :
    ∃ e ∈ later.log, e.kind = kinds.record ∧
      e.level = level.name ∧
        e.terms = bound (enterall kinds graph
          level.terms kinds.record wit) level := by
  obtain ⟨e, he, hk, hl, ht⟩ :=
    recordentry kinds graph level wit h
  exact ⟨e, boundrecord kinds growth e he, hk, hl, ht⟩

/- ## Claim six: reconcile

    Recording two levels in either order ends at the
    same standing-together relation, the same edge
    content up to the matching of edges, growth from
    the common graph to both ends, and both record
    entries in both logs — each entry's terms the
    bound as taken at its own append time. -/

/-- Edges after enterall, refined: an edge of the
    entered graph is an old edge, or the singleton of
    a listed term that was not collected before. -/
theorem enteralledgesback2 [DecidableEq Sym]
    (kinds : Kinds Sym) (terms : List (Term Sym))
    (level wit : Sym) :
    ∀ (graph : Graph Sym) (edge : Edge Sym),
      edge ∈ (enterall kinds graph terms level
        wit).edges →
        edge ∈ graph.edges ∨
          ∃ t ∈ terms,
            edge = { terms := [t], colors := [] } ∧
              ¬ collected graph t := by
  induction terms with
  | nil =>
      intro graph edge hedge
      exact Or.inl hedge
  | cons t ts ih =>
      intro graph edge hedge
      cases ih (enter kinds graph t level wit) edge
          hedge with
      | inl h1 =>
          by_cases hc : collected graph t
          · have he : (enter kinds graph t level
                wit).edges = graph.edges :=
              enteredgesof kinds graph t level wit hc
            have h2 : edge ∈ graph.edges := by
              rw [← he]
              exact h1
            exact Or.inl h2
          · cases enteredgesback kinds graph t level wit
                edge h1 with
            | inl h2 => exact Or.inl h2
            | inr h2 =>
                exact Or.inr ⟨t, by simp, h2, hc⟩
      | inr h1 =>
          obtain ⟨u, hu, heq, hnc⟩ := h1
          refine Or.inr ⟨u, List.mem_cons_of_mem t hu,
            heq, ?_⟩
          intro hcol
          exact hnc ((entercollected kinds graph t level
            wit u).mpr (Or.inl hcol))

/-- Collected after a record: collected before, or a
    term of the recorded level. -/
theorem recordcollectedback [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (level : Level Sym) (wit : Sym) (term : Term Sym) :
    collected (record kinds graph level wit) term →
      collected graph term ∨ term ∈ level.terms := by
  intro h
  by_cases hs : haslevel graph level
  · rw [recordstands kinds graph level wit hs] at h
    exact Or.inl h
  · have hrec := recordelse kinds graph level wit hs
    have hedg : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by simp only [hrec]
    obtain ⟨e, he, ht⟩ := h
    have he2 : e ∈ (enterall kinds graph level.terms
        kinds.record wit).edges := by
      rw [← hedg]
      exact he
    exact enterallcollectedback kinds level.terms
      kinds.record wit graph term ⟨e, he2, ht⟩

/-- Edges after a record: an old edge, or the
    singleton of a level term that was not collected
    before. -/
theorem recordedges [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym)
    (edge : Edge Sym) :
    edge ∈ (record kinds graph level wit).edges →
      edge ∈ graph.edges ∨
        ∃ t ∈ level.terms,
          edge = { terms := [t], colors := [] } ∧
            ¬ collected graph t := by
  intro hedge
  by_cases hs : haslevel graph level
  · rw [recordstands kinds graph level wit hs] at hedge
    exact Or.inl hedge
  · have hrec := recordelse kinds graph level wit hs
    have hedg : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by simp only [hrec]
    have hedge2 : edge ∈ (enterall kinds graph
        level.terms kinds.record wit).edges := by
      rw [← hedg]
      exact hedge
    exact enteralledgesback2 kinds level.terms
      kinds.record wit graph edge hedge2

/-- Every old edge stands after a record. -/
theorem recordedgesmem [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (level : Level Sym) (wit : Sym) (edge : Edge Sym)
    (hedge : edge ∈ graph.edges) :
    edge ∈ (record kinds graph level wit).edges := by
  by_cases hs : haslevel graph level
  · rw [recordstands kinds graph level wit hs]
    exact hedge
  · have hrec := recordelse kinds graph level wit hs
    have hedg : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by simp only [hrec]
    rw [hedg]
    exact enteralledges kinds level.terms kinds.record
      wit graph edge hedge

/-- A term collected after a record, but not before,
    stands in its singleton edge after the record: the
    record's new edges are singletons of exactly such
    terms, by the edge characterization. -/
theorem singofcollected [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (level : Level Sym) (wit : Sym) (t : Term Sym)
    (hncg : ¬ collected graph t)
    (hcol : collected (record kinds graph level wit)
      t) :
    ({ terms := [t], colors := [] } : Edge Sym) ∈
      (record kinds graph level wit).edges := by
  obtain ⟨E, hE, htE⟩ := hcol
  cases recordedges kinds graph level wit E hE with
  | inl h1 => exact absurd ⟨E, h1, htE⟩ hncg
  | inr h1 =>
      obtain ⟨s, -, heq, -⟩ := h1
      have hts : t = s := by
        have h2 : t ∈ ({ terms := [s], colors := [] } :
          Edge Sym).terms := heq ▸ htE
        simpa using h2
      subst hts
      exact heq ▸ hE

/-- The singleton of an uncollected level term stands
    after the record, on a valid graph: a standing
    level would make the term collected, so the record
    is the fresh case and enterall appends it. -/
theorem singfresh [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (level : Level Sym) (wit : Sym) (t : Term Sym)
    (ht : t ∈ level.terms)
    (hnc : ¬ collected graph t) :
    ({ terms := [t], colors := [] } : Edge Sym) ∈
      (record kinds graph level wit).edges := by
  by_cases hs : haslevel graph level
  · obtain ⟨ℓ, hℓ, -, hterms, -⟩ := hs
    obtain ⟨-, hrest⟩ := valid.levels ℓ hℓ
    exact absurd (hrest t (hterms ▸ ht)).1 hnc
  · have hrec := recordelse kinds graph level wit hs
    have hedg : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by simp only [hrec]
    rw [hedg]
    exact enterallsing kinds level.terms kinds.record
      wit graph t ht hnc

/-- The singleton of an uncollected term of the second
    recorded level stands after both records, in the
    order where that level is recorded second. -/
theorem singsecond [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (a b : Level Sym) (wa wb : Sym)
    (hb : b.terms.Nodup ∧
      ∀ t ∈ b.terms, b.scope t = true)
    (t : Term Sym) (hta : t ∈ a.terms)
    (hncg : ¬ collected graph t) :
    ({ terms := [t], colors := [] } : Edge Sym) ∈
      (record kinds (record kinds graph b wb) a
        wa).edges := by
  by_cases hcol : collected (record kinds graph b wb) t
  · exact recordedgesmem kinds _ a wa _
      (singofcollected kinds graph b wb t hncg hcol)
  · exact singfresh kinds _ (recordvalid kinds graph
      valid b wb hb.1 hb.2) a wa t hta hcol

/-- Standing together after a record: as before, or
    the pair is one term of the level standing with
    itself. -/
theorem recordsame [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (level : Level Sym) (wit : Sym) (x y : Term Sym) :
    same (record kinds graph level wit) x y ↔
      same graph x y ∨ (x = y ∧ x ∈ level.terms) := by
  by_cases hs : haslevel graph level
  · rw [recordstands kinds graph level wit hs]
    constructor
    · intro h
      exact Or.inl h
    · intro h
      cases h with
      | inl h => exact h
      | inr h =>
          obtain ⟨ℓ, hℓ, -, hterms, -⟩ := hs
          obtain ⟨-, hrest⟩ := valid.levels ℓ hℓ
          have hcol : collected graph x :=
            (hrest x (hterms ▸ h.2)).1
          exact h.1 ▸ samerefl graph x hcol
  · have hrec := recordelse kinds graph level wit hs
    have hedg : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by simp only [hrec]
    constructor
    · intro h
      obtain ⟨e, he, hx, hy⟩ := h
      have he2 : e ∈ (enterall kinds graph level.terms
          kinds.record wit).edges := by
        rw [← hedg]
        exact he
      exact (enterallsame kinds level.terms kinds.record
        wit graph x y).mp ⟨e, he2, hx, hy⟩
    · intro h
      have h2 : same (enterall kinds graph level.terms
          kinds.record wit) x y :=
        (enterallsame kinds level.terms kinds.record wit
          graph x y).mpr h
      obtain ⟨e, he, hx, hy⟩ := h2
      have he2 : e ∈ (record kinds graph level
          wit).edges := by
        rw [hedg]
        exact he
      exact ⟨e, he2, hx, hy⟩

/-- Claim six, the standing-together part: recording
    two levels in either order ends at the same
    relation — both orders reduce to standing together
    before, or one term of either level with itself. -/
theorem reconpart [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Level Sym) (w1 w2 : Sym)
    (hone : one.terms.Nodup ∧
      ∀ t ∈ one.terms, one.scope t = true)
    (htwo : two.terms.Nodup ∧
      ∀ t ∈ two.terms, two.scope t = true)
    (x y : Term Sym) :
    same (record kinds (record kinds graph one w1) two
        w2) x y ↔
      same (record kinds (record kinds graph two w2)
        one w1) x y := by
  have hv1 : Valid kinds (record kinds graph one w1) :=
    recordvalid kinds graph valid one w1 hone.1 hone.2
  have hv2 : Valid kinds (record kinds graph two w2) :=
    recordvalid kinds graph valid two w2 htwo.1 htwo.2
  rw [recordsame kinds _ hv1 two w2 x y,
    recordsame kinds _ hv2 one w1 x y,
    recordsame kinds graph valid one w1 x y,
    recordsame kinds graph valid two w2 x y]
  constructor
  · intro h
    cases h with
    | inl h =>
        cases h with
        | inl h => exact Or.inl (Or.inl h)
        | inr h => exact Or.inr h
    | inr h => exact Or.inl (Or.inr h)
  · intro h
    cases h with
    | inl h =>
        cases h with
        | inl h => exact Or.inl (Or.inl h)
        | inr h => exact Or.inr h
    | inr h => exact Or.inl (Or.inr h)

/-- Claim six, the edge content part: the two final
    graphs have the same edge content — every edge of
    either is matched in the other by an edge with the
    same terms and the same colors. -/
theorem reconcolors [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Level Sym) (w1 w2 : Sym)
    (hone : one.terms.Nodup ∧
      ∀ t ∈ one.terms, one.scope t = true)
    (htwo : two.terms.Nodup ∧
      ∀ t ∈ two.terms, two.scope t = true) :
    (∀ e ∈ (record kinds (record kinds graph one w1)
        two w2).edges,
      ∃ e' ∈ (record kinds (record kinds graph two w2)
          one w1).edges,
        e'.terms = e.terms ∧ e'.colors = e.colors) ∧
    (∀ e ∈ (record kinds (record kinds graph two w2)
        one w1).edges,
      ∃ e' ∈ (record kinds (record kinds graph one
          w1) two w2).edges,
        e'.terms = e.terms ∧ e'.colors = e.colors) := by
  have key : ∀ (a b : Level Sym) (wa wb : Sym),
      (b.terms.Nodup ∧
        ∀ t ∈ b.terms, b.scope t = true) →
      ∀ e ∈ (record kinds (record kinds graph a wa) b
          wb).edges,
        ∃ e' ∈ (record kinds (record kinds graph b wb)
            a wa).edges,
          e'.terms = e.terms ∧ e'.colors = e.colors := by
    intro a b wa wb hb e he
    cases recordedges kinds _ b wb e he with
    | inl h1 =>
        cases recordedges kinds graph a wa e h1 with
        | inl h2 =>
            exact ⟨e, recordedgesmem kinds _ a wa e
              (recordedgesmem kinds graph b wb e h2),
              rfl, rfl⟩
        | inr h2 =>
            obtain ⟨t, hta, heq, hncg⟩ := h2
            have hsing : ({ terms := [t], colors := [] } :
                Edge Sym) ∈
                (record kinds (record kinds graph b wb)
                  a wa).edges :=
              singsecond kinds graph valid a b wa wb hb t
                hta hncg
            exact ⟨{ terms := [t], colors := [] }, hsing,
              by rw [heq], by rw [heq]⟩
    | inr h1 =>
        obtain ⟨t, htb, heq, hnca⟩ := h1
        have hncg : ¬ collected graph t :=
          fun hc => hnca ((recordgrows kinds graph a
            wa).collected t hc)
        have hsing : ({ terms := [t], colors := [] } :
            Edge Sym) ∈
            (record kinds (record kinds graph b wb) a
              wa).edges :=
          recordedgesmem kinds _ a wa _
            (singfresh kinds graph valid b wb t htb hncg)
        exact ⟨{ terms := [t], colors := [] }, hsing,
          by rw [heq], by rw [heq]⟩
  exact ⟨key one two w1 w2 htwo, key two one w2 w1 hone⟩

/-- Claim six, growth: the common graph grows to both
    final graphs. -/
theorem recongrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Level Sym)
    (w1 w2 : Sym) :
    Growth kinds graph
        (record kinds (record kinds graph one w1) two
          w2) ∧
      Growth kinds graph
        (record kinds (record kinds graph two w2) one
          w1) :=
  ⟨growthtrans kinds (recordgrows kinds graph one w1)
      (recordgrows kinds _ two w2),
    growthtrans kinds (recordgrows kinds graph two w2)
      (recordgrows kinds _ one w1)⟩

/-- Claim six, the entries: in the first order's final
    log, both record entries stand — the first level's
    with the bound as taken over the first entry graph,
    the second's with the bound as taken over the
    graph the first record reached. The second order
    is the symmetric statement with the roles exchanged;
    the two entries' terms fields are in general
    different values, each the bound of its moment. -/
theorem reconrecord [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Level Sym)
    (w1 w2 : Sym)
    (h1 : ¬ haslevel graph one)
    (h2 : ¬ haslevel (record kinds graph one w1) two) :
    (∃ e ∈ (record kinds (record kinds graph one w1)
        two w2).log,
      e.kind = kinds.record ∧ e.level = one.name ∧
        e.terms = bound (enterall kinds graph
          one.terms kinds.record w1) one) ∧
    (∃ e ∈ (record kinds (record kinds graph one w1)
        two w2).log,
      e.kind = kinds.record ∧ e.level = two.name ∧
        e.terms = bound (enterall kinds
          (record kinds graph one w1) two.terms
          kinds.record w2) two) := by
  obtain ⟨e1, he1, hk1, hl1, ht1⟩ :=
    recordentry kinds graph one w1 h1
  obtain ⟨e2, he2, hk2, hl2, ht2⟩ :=
    recordentry kinds (record kinds graph one w1) two
      w2 h2
  exact ⟨⟨e1, boundrecord kinds
      (recordgrows kinds _ two w2) e1 he1, hk1, hl1,
      ht1⟩,
    ⟨e2, he2, hk2, hl2, ht2⟩⟩

/- ## Claim seven: widen

    A run that only grows the graph from a valid start
    keeps every collected term collected with its
    spelling — terms are values, so the spelling in
    the later graph is the same term — and every old
    edge grows: some later edge holds all its terms
    and all its colors. The scope half of the claim is
    the core file's section three nesting: the trivial
    scope sits inside the first scope, and the full
    scope is the top. -/

/-- Every old edge grows along the growth relation:
    some later edge holds all its terms and colors. -/
theorem edgegrow [DecidableEq Sym] (kinds : Kinds Sym)
    {g h : Graph Sym} (growth : Growth kinds g h)
    (validg : Valid kinds g) (validh : Valid kinds h)
    (e : Edge Sym) (he : e ∈ g.edges) :
    ∃ e' ∈ h.edges, (∀ t ∈ e.terms, t ∈ e'.terms) ∧
      ∀ c ∈ e.colors, c ∈ e'.colors := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ e.terms := by
    cases hterms : e.terms with
    | nil => exact absurd hterms (validg.nonempty e he)
    | cons t ts => exact ⟨t, by simp [hterms]⟩
  obtain ⟨e', he', ht', hc'⟩ := growth.colors e he t ht
  refine ⟨e', he', ?_, hc'⟩
  intro s hs
  have hsame : same h t s :=
    growth.same t s ⟨e, he, ht, hs⟩
  obtain ⟨e'', he'', ht'', hs''⟩ := hsame
  have heq : e'' = e' :=
    validh.disjoint e'' he'' e' he' t ht'' ht'
  exact heq ▸ hs''

/-- Claim seven: a ready run from a valid graph grows
    the graph, keeps every collected term collected,
    and grows every old edge. -/
theorem widen [DecidableEq Sym] (kinds : Kinds Sym)
    {g : Graph Sym} {ops : List (Op Sym)}
    (validg : Valid kinds g) (ready : Ready kinds g ops) :
    Growth kinds g (run kinds g ops) ∧
      (∀ t, collected g t →
        collected (run kinds g ops) t) ∧
      (∀ e ∈ g.edges,
        ∃ e' ∈ (run kinds g ops).edges,
          (∀ t ∈ e.terms, t ∈ e'.terms) ∧
            ∀ c ∈ e.colors, c ∈ e'.colors) := by
  have hg := rungrows kinds ready
  exact ⟨hg, hg.collected, fun e he =>
    edgegrow kinds hg validg (runvalid kinds ready) e
      he⟩
