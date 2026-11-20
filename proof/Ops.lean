/-
  The growth operations of section 8, and what they
  preserve. Every graph of this program is built from
  the empty graph by these operations and no others:
  enter a term, join two terms, record a level, paint a
  color. Each operation appends its entry to the log,
  preserves validity, and satisfies the growth relation,
  so drift is excluded by construction: there is no
  operation in the model whose output drifts from its
  input, and no other route to a graph value.
-/

import Core

open scoped Classical

variable {Sym : Type}

/- ## Finding the edge that holds a term -/

/-- The first edge of a list holding the term, if any.
    On a valid graph the partition makes the edge
    unique, so the first is the only. -/
def seek [DecidableEq Sym] : List (Edge Sym) → Term Sym → Option (Edge Sym)
  | [], _ => none
  | edge :: rest, term =>
      if term ∈ edge.terms then some edge else seek rest term

/-- A found edge is in the list and holds the term. -/
theorem seeksome [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym)
    (edge : Edge Sym), seek edges term = some edge →
    edge ∈ edges ∧ term ∈ edge.terms := by
  intro edges
  induction edges with
  | nil =>
      intro term edge h
      cases h
  | cons e es ih =>
      intro term edge h
      by_cases hc : term ∈ e.terms
      · have h2 : seek (e :: es) term = some e := by
          simp only [seek, hc, ↓reduceIte]
        rw [h2] at h
        cases h
        exact ⟨by simp, hc⟩
      · have h2 : seek (e :: es) term = seek es term := by
          simp only [seek, hc, ↓reduceIte]
        rw [h2] at h
        obtain ⟨h1, h2⟩ := ih term edge h
        exact ⟨List.mem_cons_of_mem e h1, h2⟩

/-- When no edge is found, no edge of the list holds
    the term. -/
theorem seeknone [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym),
    seek edges term = none →
    ∀ edge ∈ edges, term ∉ edge.terms := by
  intro edges
  induction edges with
  | nil =>
      intro term _ edge hedge
      cases hedge
  | cons e es ih =>
      intro term h edge hedge
      by_cases hc : term ∈ e.terms
      · have h2 : seek (e :: es) term = some e := by
          simp only [seek, hc, ↓reduceIte]
        rw [h2] at h
        cases h
      · have h2 : seek (e :: es) term = seek es term := by
          simp only [seek, hc, ↓reduceIte]
        rw [h2] at h
        cases List.mem_cons.mp hedge with
        | inl heq =>
            rw [heq]
            exact hc
        | inr hm =>
            exact ih term h edge hm

/-- A collected term is found: some edge is returned,
    and it holds the term. -/
theorem seekof [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym),
    (∃ edge ∈ edges, term ∈ edge.terms) →
    ∃ edge, seek edges term = some edge ∧
      edge ∈ edges ∧ term ∈ edge.terms := by
  intro edges
  induction edges with
  | nil =>
      intro term h
      obtain ⟨edge, hedge, _⟩ := h
      cases hedge
  | cons e es ih =>
      intro term h
      by_cases hc : term ∈ e.terms
      · exact ⟨e, by simp only [seek, hc, ↓reduceIte], by simp, hc⟩
      · have h2 : seek (e :: es) term = seek es term := by
          simp only [seek, hc, ↓reduceIte]
        obtain ⟨edge, hedge, hterm⟩ := h
        have hrest : ∃ edge ∈ es, term ∈ edge.terms := by
          cases List.mem_cons.mp hedge with
          | inl heq =>
              rw [heq] at hterm
              exact absurd hterm hc
          | inr hm =>
              exact ⟨edge, hm, hterm⟩
        obtain ⟨found, hfound, hfin, hfterm⟩ := ih term hrest
        exact ⟨found, h2.trans hfound, List.mem_cons_of_mem e hfin,
          hfterm⟩

/- ## Chains under growth of the log -/

/-- A chain over a log is a chain over any longer log
    that has the first as a prefix. -/
theorem chainmono (kinds : Kinds Sym) {log extra : List (Entry Sym)}
    {left right : Term Sym} (h : Chain kinds log left right) :
    Chain kinds (log ++ extra) left right := by
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, hkind, h1, h2⟩ := hstep
      exact Chain.step ⟨entry, List.mem_append_left extra hentry,
        hkind, h1, h2⟩
  | trans _ _ ih1 ih2 =>
      exact Chain.trans ih1 ih2

/-- Appending entries that are not equivalence entries
    adds no chain: a chain over the longer log was
    already a chain over the first. -/
theorem chainappend (kinds : Kinds Sym) {log extra : List (Entry Sym)}
    (hkind : ∀ entry ∈ extra, entry.kind ≠ kinds.join)
    {left right : Term Sym}
    (h : Chain kinds (log ++ extra) left right) :
    Chain kinds log left right := by
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, hkind2, h1, h2⟩ := hstep
      cases List.mem_append.mp hentry with
      | inl hm =>
          exact Chain.step ⟨entry, hm, hkind2, h1, h2⟩
      | inr hm =>
          exact absurd hkind2 (hkind entry hm)
  | trans _ _ ih1 ih2 =>
      exact Chain.trans ih1 ih2

/-- Reachability is monotone in the log. -/
theorem reachmono (kinds : Kinds Sym) {log extra : List (Entry Sym)}
    {left right : Term Sym} (h : reach kinds log left right) :
    reach kinds (log ++ extra) left right := by
  cases h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (chainmono kinds h)

/-- Appending entries that are not equivalence entries
    adds no reachability. -/
theorem reachappend (kinds : Kinds Sym) {log extra : List (Entry Sym)}
    (hkind : ∀ entry ∈ extra, entry.kind ≠ kinds.join)
    {left right : Term Sym}
    (h : reach kinds (log ++ extra) left right) :
    reach kinds log left right := by
  cases h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (chainappend kinds hkind h)

/-- Reachability is reflexive. -/
theorem reachrefl (kinds : Kinds Sym) (log : List (Entry Sym))
    (term : Term Sym) : reach kinds log term term :=
  Or.inl rfl

/-- A single step is a reachability. -/
theorem reachstep (kinds : Kinds Sym) {log : List (Entry Sym)}
    {left right : Term Sym}
    (h : step kinds log left right) :
    reach kinds log left right :=
  Or.inr (Chain.step h)

/-- A chain read backward is a chain: a step is
    symmetric in its two terms, since both stand in the
    one entry's term list, and the closure inherits it. -/
theorem chainsymm (kinds : Kinds Sym) {log : List (Entry Sym)}
    {left right : Term Sym} (h : Chain kinds log left right) :
    Chain kinds log right left := by
  induction h with
  | step hstep =>
      obtain ⟨entry, hentry, hkind, h1, h2⟩ := hstep
      exact Chain.step ⟨entry, hentry, hkind, h2, h1⟩
  | trans _ _ ih1 ih2 =>
      exact Chain.trans ih2 ih1

/-- Reachability is symmetric. -/
theorem reachsymm (kinds : Kinds Sym) {log : List (Entry Sym)}
    {left right : Term Sym} (h : reach kinds log left right) :
    reach kinds log right left := by
  cases h with
  | inl h => exact Or.inl h.symm
  | inr h => exact Or.inr (chainsymm kinds h)

/-- Reachability is transitive. -/
theorem reachtrans (kinds : Kinds Sym) {log : List (Entry Sym)}
    {one two three : Term Sym}
    (h1 : reach kinds log one two)
    (h2 : reach kinds log two three) :
    reach kinds log one three := by
  cases h1 with
  | inl h =>
      rw [h]
      exact h2
  | inr h =>
      cases h2 with
      | inl h2 =>
          rw [← h2]
          exact Or.inr h
      | inr h2 =>
          exact Or.inr (Chain.trans h h2)

/-- The class reading of one appended equivalence: after
    an equivalence entry for the pair is appended, two
    terms reach each other exactly when they reached
    each other before, or both reach the pair's class:
    each reaches one of the two joined terms. This is
    the whole content of one join for reachability. -/
theorem reachjoin (kinds : Kinds Sym) (log : List (Entry Sym))
    (one two : Term Sym) (level wit : Sym) {x y : Term Sym} :
    reach kinds (log ++ [⟨kinds.join, [one, two], level, wit⟩]) x y ↔
      reach kinds log x y ∨
        ((reach kinds log x one ∨ reach kinds log x two) ∧
          (reach kinds log y one ∨ reach kinds log y two)) := by
  constructor
  · intro h
    cases h with
    | inl h =>
        exact Or.inl (Or.inl h)
    | inr h =>
        induction h with
        | step hstep =>
            obtain ⟨entry, hentry, hkind, h1, h2⟩ := hstep
            cases List.mem_append.mp hentry with
            | inl hm =>
                exact Or.inl (reachstep kinds
                  ⟨entry, hm, hkind, h1, h2⟩)
            | inr hm =>
                have heq : entry =
                    ⟨kinds.join, [one, two], level, wit⟩ :=
                  List.mem_singleton.mp hm
                rw [heq] at h1 h2
                refine Or.inr ⟨?_, ?_⟩
                · cases List.mem_cons.mp h1 with
                  | inl h =>
                      exact Or.inl (Or.inl h)
                  | inr h =>
                      cases List.mem_cons.mp h with
                      | inl h =>
                          exact Or.inr (Or.inl h)
                      | inr h => cases h
                · cases List.mem_cons.mp h2 with
                  | inl h =>
                      exact Or.inl (Or.inl h)
                  | inr h =>
                      cases List.mem_cons.mp h with
                      | inl h =>
                          exact Or.inr (Or.inl h)
                      | inr h => cases h
        | trans _ _ ih1 ih2 =>
            cases ih1 with
            | inl h1 =>
                cases ih2 with
                | inl h2 =>
                    exact Or.inl (reachtrans kinds h1 h2)
                | inr h2 =>
                    obtain ⟨hm, hy⟩ := h2
                    refine Or.inr ⟨?_, hy⟩
                    cases hm with
                    | inl hm =>
                        exact Or.inl (reachtrans kinds h1 hm)
                    | inr hm =>
                        exact Or.inr (reachtrans kinds h1 hm)
            | inr h1 =>
                obtain ⟨hx, hm⟩ := h1
                cases ih2 with
                | inl h2 =>
                    refine Or.inr ⟨hx, ?_⟩
                    cases hm with
                    | inl hm =>
                        exact Or.inl (reachsymm kinds
                          (reachtrans kinds (reachsymm kinds hm) h2))
                    | inr hm =>
                        exact Or.inr (reachsymm kinds
                          (reachtrans kinds (reachsymm kinds hm) h2))
                | inr h2 =>
                    exact Or.inr ⟨hx, h2.2⟩
  · intro h
    have hstep : reach kinds
        (log ++ [⟨kinds.join, [one, two], level, wit⟩]) one two :=
      reachstep kinds ⟨⟨kinds.join, [one, two], level, wit⟩,
        by simp, rfl, by simp, by simp⟩
    cases h with
    | inl h =>
        exact reachmono kinds h
    | inr h =>
        obtain ⟨hx, hy⟩ := h
        have hxn : reach kinds
            (log ++ [⟨kinds.join, [one, two], level, wit⟩]) x one ∨
            reach kinds
            (log ++ [⟨kinds.join, [one, two], level, wit⟩]) x two := by
          cases hx with
          | inl h => exact Or.inl (reachmono kinds h)
          | inr h => exact Or.inr (reachmono kinds h)
        have hyn : reach kinds
            (log ++ [⟨kinds.join, [one, two], level, wit⟩]) y one ∨
            reach kinds
            (log ++ [⟨kinds.join, [one, two], level, wit⟩]) y two := by
          cases hy with
          | inl h => exact Or.inl (reachmono kinds h)
          | inr h => exact Or.inr (reachmono kinds h)
        cases hxn with
        | inl hx1 =>
            cases hyn with
            | inl hy1 =>
                exact reachtrans kinds hx1
                  (reachsymm kinds hy1)
            | inr hy2 =>
                exact reachtrans kinds
                  (reachtrans kinds hx1 hstep)
                  (reachsymm kinds hy2)
        | inr hx2 =>
            cases hyn with
            | inl hy1 =>
                exact reachtrans kinds
                  (reachtrans kinds hx2
                    (reachsymm kinds hstep))
                  (reachsymm kinds hy1)
            | inr hy2 =>
                exact reachtrans kinds hx2
                  (reachsymm kinds hy2)

/- ## The first operation: enter a term -/

/-- Enter a term at a level: if the term is already
    collected, the edges do not change; if not, a new
    edge is appended holding exactly that term and no
    colors. Either way, an entry is appended to the
    log. The first of the four operations of section
    8.2; the specification's word for it is the one this
    development avoids only because the checker reserves
    it, and the operation is that operation. -/
def enter [DecidableEq Sym] (kinds : Kinds Sym) (graph : Graph Sym)
    (term : Term Sym) (level wit : Sym) : Graph Sym :=
  match seek graph.edges term with
  | some _ =>
      ⟨graph.edges, graph.levels,
        graph.log ++ [⟨kinds.enter, [term], level, wit⟩]⟩
  | none =>
      ⟨graph.edges ++ [⟨[term], []⟩], graph.levels,
        graph.log ++ [⟨kinds.enter, [term], level, wit⟩]⟩

/-- Entering appends exactly its one entry to the log. -/
theorem enterlog [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym) :
    (enter kinds graph term level wit).log =
      graph.log ++ [⟨kinds.enter, [term], level, wit⟩] := by
  cases hs : seek graph.edges term <;> simp only [enter, hs]

/-- Entering does not change the recorded levels. -/
theorem enterlevels [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym) :
    (enter kinds graph term level wit).levels = graph.levels := by
  cases hs : seek graph.edges term <;> simp only [enter, hs]

/-- The collected terms after entering are the collected
    terms before, together with the entered term. -/
theorem entercollected [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym)
    (other : Term Sym) :
    collected (enter kinds graph term level wit) other ↔
      collected graph other ∨ other = term := by
  cases hs : seek graph.edges term with
  | some found =>
      obtain ⟨hfin, hfterm⟩ := seeksome graph.edges term found hs
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges := by simp only [enter, hs]
      constructor
      · intro h
        obtain ⟨edge, hedge, hinte⟩ := h
        rw [h2] at hedge
        exact Or.inl ⟨edge, hedge, hinte⟩
      · intro h
        cases h with
        | inl h =>
            obtain ⟨edge, hedge, hinte⟩ := h
            exact ⟨edge, h2 ▸ hedge, hinte⟩
        | inr h =>
            rw [h]
            exact ⟨found, h2 ▸ hfin, hfterm⟩
  | none =>
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges ++ [⟨[term], []⟩] := by simp only [enter, hs]
      constructor
      · intro h
        obtain ⟨edge, hedge, hinte⟩ := h
        rw [h2] at hedge
        cases List.mem_append.mp hedge with
        | inl hm =>
            exact Or.inl ⟨edge, hm, hinte⟩
        | inr hm =>
            have heq : edge = ⟨[term], []⟩ :=
              List.mem_singleton.mp hm
            rw [heq] at hinte
            exact Or.inr (List.mem_singleton.mp hinte)
      · intro h
        cases h with
        | inl h =>
            obtain ⟨edge, hedge, hinte⟩ := h
            exact ⟨edge, h2 ▸ List.mem_append_left _ hedge, hinte⟩
        | inr h =>
            rw [h]
            exact ⟨⟨[term], []⟩, h2 ▸ (by simp), by simp⟩

/-- Equivalence after entering is equivalence before,
    together with the entered term standing with itself:
    a repeat entry of one spelling adds provenance, not
    a new classmate. -/
theorem entersame [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym)
    (one two : Term Sym) :
    same (enter kinds graph term level wit) one two ↔
      same graph one two ∨ (one = term ∧ two = term) := by
  cases hs : seek graph.edges term with
  | some found =>
      obtain ⟨hfin, hfterm⟩ := seeksome graph.edges term found hs
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges := by simp only [enter, hs]
      constructor
      · intro h
        obtain ⟨edge, hedge, h1, h2'⟩ := h
        rw [h2] at hedge
        exact Or.inl ⟨edge, hedge, h1, h2'⟩
      · intro h
        cases h with
        | inl h =>
            obtain ⟨edge, hedge, h1, h2'⟩ := h
            exact ⟨edge, h2 ▸ hedge, h1, h2'⟩
        | inr h =>
            obtain ⟨h1, h2'⟩ := h
            rw [h1, h2']
            exact ⟨found, h2 ▸ hfin, hfterm, hfterm⟩
  | none =>
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges ++ [⟨[term], []⟩] := by simp only [enter, hs]
      constructor
      · intro h
        obtain ⟨edge, hedge, h1, h2'⟩ := h
        rw [h2] at hedge
        cases List.mem_append.mp hedge with
        | inl hm =>
            exact Or.inl ⟨edge, hm, h1, h2'⟩
        | inr hm =>
            have heq : edge = ⟨[term], []⟩ :=
              List.mem_singleton.mp hm
            rw [heq] at h1 h2'
            exact Or.inr ⟨List.mem_singleton.mp h1,
              List.mem_singleton.mp h2'⟩
      · intro h
        cases h with
        | inl h =>
            obtain ⟨edge, hedge, h1, h2'⟩ := h
            exact ⟨edge, h2 ▸ List.mem_append_left _ hedge, h1, h2'⟩
        | inr h =>
            obtain ⟨h1, h2'⟩ := h
            rw [h1, h2']
            exact ⟨⟨[term], []⟩, h2 ▸ (by simp), by simp, by simp⟩

/-- Entering preserves validity: the new edge, when one
    is appended, is a singleton with no colors, disjoint
    from every old edge because its term was not
    collected; the log grows by an entry that is not an
    equivalence entry, so no chain changes; the old
    exactness readings carry over. -/
theorem entervalid [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (term : Term Sym) (level wit : Sym) :
    Valid kinds (enter kinds graph term level wit) := by
  cases hs : seek graph.edges term with
  | some found =>
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges := by simp only [enter, hs]
      have h3 : (enter kinds graph term level wit).levels =
          graph.levels := by simp only [enter, hs]
      have h4 : (enter kinds graph term level wit).log =
          graph.log ++ [⟨kinds.enter, [term], level, wit⟩] :=
        enterlog kinds graph term level wit
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro edge hedge
        rw [h2] at hedge
        exact valid.nonempty edge hedge
      · intro edge hedge
        rw [h2] at hedge
        exact valid.nodup edge hedge
      · intro one hone two htwo t ht1 ht2
        rw [h2] at hone htwo
        exact valid.disjoint one hone two htwo t ht1 ht2
      · intro edge hedge
        rw [h2] at hedge
        exact valid.cnodup edge hedge
      · intro lev hlev
        rw [h3] at hlev
        obtain ⟨hnd, hmem⟩ := valid.levels lev hlev
        refine ⟨hnd, fun t ht => ?_⟩
        obtain ⟨hcol, hscope⟩ := hmem t ht
        exact ⟨(entercollected kinds graph term level wit t).mpr
          (Or.inl hcol), hscope⟩
      · intro one two h
        obtain ⟨edge, hedge, h1, h2'⟩ := h
        rw [h2] at hedge
        have hr := valid.exactone one two ⟨edge, hedge, h1, h2'⟩
        rw [h4]
        exact reachmono kinds hr
      · intro one two h
        rw [h4] at h
        have hc := chainappend kinds
          (log := graph.log)
          (extra := [⟨kinds.enter, [term], level, wit⟩])
          (by
            intro entry hentry
            have heq : entry = ⟨kinds.enter, [term], level, wit⟩ :=
              List.mem_singleton.mp hentry
            rw [heq]
            exact kinds.distinct.1)
          h
        have hs2 := valid.exacttwo one two hc
        obtain ⟨edge, hedge, h1, h2'⟩ := hs2
        exact ⟨edge, h2 ▸ hedge, h1, h2'⟩
      · rw [h2]
        exact valid.edgenodup
  | none =>
      have hnc : ∀ edge ∈ graph.edges, term ∉ edge.terms :=
        seeknone graph.edges term hs
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges ++ [⟨[term], []⟩] := by simp only [enter, hs]
      have h3 : (enter kinds graph term level wit).levels =
          graph.levels := by simp only [enter, hs]
      have h4 : (enter kinds graph term level wit).log =
          graph.log ++ [⟨kinds.enter, [term], level, wit⟩] :=
        enterlog kinds graph term level wit
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro edge hedge
        rw [h2] at hedge
        cases List.mem_append.mp hedge with
        | inl hm => exact valid.nonempty edge hm
        | inr hm =>
            have heq : edge = ⟨[term], []⟩ :=
              List.mem_singleton.mp hm
            rw [heq]
            simp
      · intro edge hedge
        rw [h2] at hedge
        cases List.mem_append.mp hedge with
        | inl hm => exact valid.nodup edge hm
        | inr hm =>
            have heq : edge = ⟨[term], []⟩ :=
              List.mem_singleton.mp hm
            rw [heq]
            simp [List.Nodup]
      · intro one hone two htwo t ht1 ht2
        rw [h2] at hone htwo
        cases List.mem_append.mp hone with
        | inl hm1 =>
            cases List.mem_append.mp htwo with
            | inl hm2 =>
                exact valid.disjoint one hm1 two hm2 t ht1 ht2
            | inr hm2 =>
                have heq : two = ⟨[term], []⟩ :=
                  List.mem_singleton.mp hm2
                rw [heq] at ht2
                have ht : t = term := List.mem_singleton.mp ht2
                rw [ht] at ht1
                exact absurd ht1 (hnc one hm1)
        | inr hm1 =>
            cases List.mem_append.mp htwo with
            | inl hm2 =>
                have heq : one = ⟨[term], []⟩ :=
                  List.mem_singleton.mp hm1
                rw [heq] at ht1
                have ht : t = term := List.mem_singleton.mp ht1
                rw [ht] at ht2
                exact absurd ht2 (hnc two hm2)
            | inr hm2 =>
                have heq1 : one = ⟨[term], []⟩ :=
                  List.mem_singleton.mp hm1
                have heq2 : two = ⟨[term], []⟩ :=
                  List.mem_singleton.mp hm2
                rw [heq1, heq2]
      · intro edge hedge
        rw [h2] at hedge
        cases List.mem_append.mp hedge with
        | inl hm => exact valid.cnodup edge hm
        | inr hm =>
            have heq : edge = ⟨[term], []⟩ :=
              List.mem_singleton.mp hm
            rw [heq]
            exact List.nodup_nil
      · intro lev hlev
        rw [h3] at hlev
        obtain ⟨hnd, hmem⟩ := valid.levels lev hlev
        refine ⟨hnd, fun t ht => ?_⟩
        obtain ⟨hcol, hscope⟩ := hmem t ht
        exact ⟨(entercollected kinds graph term level wit t).mpr
          (Or.inl hcol), hscope⟩
      · intro one two h
        have hr := (entersame kinds graph term level wit one two).mp h
        rw [h4]
        cases hr with
        | inl hr =>
            exact reachmono kinds (valid.exactone one two hr)
        | inr hr =>
            exact Or.inl (hr.1.trans hr.2.symm)
      · intro one two h
        rw [h4] at h
        have hc := chainappend kinds
          (log := graph.log)
          (extra := [⟨kinds.enter, [term], level, wit⟩])
          (by
            intro entry hentry
            have heq : entry = ⟨kinds.enter, [term], level, wit⟩ :=
              List.mem_singleton.mp hentry
            rw [heq]
            exact kinds.distinct.1)
          h
        have hs2 := valid.exacttwo one two hc
        exact (entersame kinds graph term level wit one two).mpr
          (Or.inl hs2)
      · rw [h2, Aux.nodupappend]
        refine ⟨valid.edgenodup, by simp [List.Nodup], ?_⟩
        intro x hx hcon
        have heq : x = ⟨[term], []⟩ :=
          List.mem_singleton.mp hcon
        have hterm : term ∈ x.terms := by
          rw [heq]
          simp
        exact hnc x hx hterm

/- ## The fourth operation: paint a color -/

/-- Painting on an edge list: the first edge holding the
    term has the color appended to its color list, if
    the color is not already present; every other edge
    is untouched. On a valid graph at most one edge
    holds the term, so this paints exactly that edge. -/
def paintedges [DecidableEq Sym] : List (Edge Sym) →
    Term Sym → Color Sym → List (Edge Sym)
  | [], _, _ => []
  | edge :: rest, term, color =>
      if term ∈ edge.terms then
        ⟨edge.terms,
          if color ∈ edge.colors then edge.colors
          else edge.colors ++ [color]⟩ :: rest
      else
        edge :: paintedges rest term color

/-- Every old edge is covered by a painted edge with the
    same terms and at least its colors: painting never
    removes, alters, or shadows an existing color. -/
theorem paintedgescover [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym)
      (color : Color Sym) (old : Edge Sym), old ∈ edges →
      ∃ edge ∈ paintedges edges term color,
        edge.terms = old.terms ∧
        ∀ col ∈ old.colors, col ∈ edge.colors := by
  intro edges
  induction edges with
  | nil =>
      intro term color old hold
      cases hold
  | cons e es ih =>
      intro term color old hold
      cases List.mem_cons.mp hold with
      | inl heq =>
          rw [heq]
          by_cases hc : term ∈ e.terms
          · have h2 : paintedges (e :: es) term color =
                ⟨e.terms,
                  if color ∈ e.colors then e.colors
                  else e.colors ++ [color]⟩ :: es := by
              simp only [paintedges, hc, ↓reduceIte]
            refine ⟨⟨e.terms,
              if color ∈ e.colors then e.colors
              else e.colors ++ [color]⟩,
              by rw [h2]; simp, rfl, ?_⟩
            intro col hcol
            by_cases hc2 : color ∈ e.colors
            · simp only [hc2, ↓reduceIte]
              exact hcol
            · simp only [hc2, ↓reduceIte]
              exact List.mem_append_left _ hcol
          · have h2 : paintedges (e :: es) term color =
                e :: paintedges es term color := by
              simp only [paintedges, hc, ↓reduceIte]
            exact ⟨e, by rw [h2]; simp, rfl,
              fun col hcol => hcol⟩
      | inr hm =>
          by_cases hc : term ∈ e.terms
          · have h2 : paintedges (e :: es) term color =
                ⟨e.terms,
                  if color ∈ e.colors then e.colors
                  else e.colors ++ [color]⟩ :: es := by
              simp only [paintedges, hc, ↓reduceIte]
            exact ⟨old, by
              rw [h2]
              exact List.mem_cons_of_mem _ hm, rfl,
              fun col hcol => hcol⟩
          · have h2 : paintedges (e :: es) term color =
                e :: paintedges es term color := by
              simp only [paintedges, hc, ↓reduceIte]
            obtain ⟨edge, hedge, hterms, hcolors⟩ :=
              ih term color old hm
            exact ⟨edge, by
              rw [h2]
              exact List.mem_cons_of_mem _ hedge,
              hterms, hcolors⟩

/-- Every painted edge has the terms of some old edge:
    painting changes no term of any edge. -/
theorem paintedgesback [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym)
      (color : Color Sym) (edge : Edge Sym),
      edge ∈ paintedges edges term color →
      ∃ old ∈ edges, old.terms = edge.terms := by
  intro edges
  induction edges with
  | nil =>
      intro term color edge hedge
      cases hedge
  | cons e es ih =>
      intro term color edge hedge
      by_cases hc : term ∈ e.terms
      · have h2 : paintedges (e :: es) term color =
            ⟨e.terms,
              if color ∈ e.colors then e.colors
              else e.colors ++ [color]⟩ :: es := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2] at hedge
        cases List.mem_cons.mp hedge with
        | inl heq =>
            exact ⟨e, by simp, by rw [heq]⟩
        | inr hm =>
            exact ⟨edge, List.mem_cons_of_mem _ hm, rfl⟩
      · have h2 : paintedges (e :: es) term color =
            e :: paintedges es term color := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2] at hedge
        cases List.mem_cons.mp hedge with
        | inl heq =>
            exact ⟨e, by simp, by rw [heq]⟩
        | inr hm =>
            obtain ⟨old, hold, hterms⟩ := ih term color edge hm
            exact ⟨old, List.mem_cons_of_mem _ hold, hterms⟩

/-- When no edge holds the term, painting changes no
    edge. -/
theorem paintedgesnone [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)) (term : Term Sym)
      (color : Color Sym),
      seek edges term = none →
      paintedges edges term color = edges := by
  intro edges
  induction edges with
  | nil =>
      intro term color _
      rfl
  | cons e es ih =>
      intro term color hs
      have hnc : term ∉ e.terms := by
        by_cases hc : term ∈ e.terms
        · have h2 : seek (e :: es) term = some e := by
            simp only [seek, hc, ↓reduceIte]
          rw [h2] at hs
          cases hs
        · exact hc
      have hs2 : seek es term = none := by
        have h2 : seek (e :: es) term = seek es term := by
          simp only [seek, hnc, ↓reduceIte]
        rw [h2] at hs
        exact hs
      simp only [paintedges, hnc, ↓reduceIte, ih term color hs2]

/-- A map that fixes every member of a list is the
    identity on that list. -/
theorem mapfix {β : Type} (f : β → β) :
    ∀ (list : List β), (∀ x ∈ list, f x = x) →
      list.map f = list := by
  intro list
  induction list with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.map_cons, h x (by simp),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Painting, read as a map over the edge list: on a
    list whose edges are pairwise disjoint and free of
    repeats, painting is the map that changes only the
    found edge, appending the color to its colors when
    absent, and fixes every other edge. -/
theorem paintedgesmaplist [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)), edges.Nodup →
      (∀ one ∈ edges, ∀ two ∈ edges, ∀ t,
        t ∈ one.terms → t ∈ two.terms → one = two) →
      ∀ (term : Term Sym) (color : Color Sym) (found : Edge Sym),
        seek edges term = some found →
        paintedges edges term color =
          edges.map (fun edge =>
            if edge = found then
              ⟨edge.terms,
                if color ∈ edge.colors then edge.colors
                else edge.colors ++ [color]⟩
            else edge) := by
  intro edges
  induction edges with
  | nil =>
      intro _ _ term color found hs
      cases hs
  | cons e es ih =>
      intro hnd hdisj term color found hs
      rw [List.nodup_cons] at hnd
      obtain ⟨hne, hndes⟩ := hnd
      have hdisjes : ∀ one ∈ es, ∀ two ∈ es, ∀ t,
          t ∈ one.terms → t ∈ two.terms → one = two :=
        fun one hone two htwo t ht1 ht2 =>
          hdisj one (List.mem_cons_of_mem e hone)
            two (List.mem_cons_of_mem e htwo) t ht1 ht2
      obtain ⟨hfin, hfterm⟩ := seeksome (e :: es) term found hs
      by_cases hc : term ∈ e.terms
      · have hseek : seek (e :: es) term = some e := by
          simp only [seek, hc, ↓reduceIte]
        rw [hseek] at hs
        cases hs
        have h2 : paintedges (e :: es) term color =
            ⟨e.terms,
              if color ∈ e.colors then e.colors
              else e.colors ++ [color]⟩ :: es := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2, List.map_cons]
        have hfix : es.map (fun edge =>
            if edge = e then
              ⟨edge.terms,
                if color ∈ edge.colors then edge.colors
                else edge.colors ++ [color]⟩
            else edge) = es := by
          apply mapfix
          intro x hx
          have hxne : x ≠ e := by
            intro heq
            exact hne (heq ▸ hx)
          simp only [hxne, ↓reduceIte]
        rw [hfix]
        simp only [↓reduceIte]
      · have hseek : seek (e :: es) term = seek es term := by
          simp only [seek, hc, ↓reduceIte]
        have hs2 : seek es term = some found := by
          rw [← hseek]
          exact hs
        have hfines : found ∈ es := by
          cases List.mem_cons.mp hfin with
          | inl heq =>
              rw [heq] at hfterm
              exact absurd hfterm hc
          | inr hm =>
              exact hm
        have hih := ih hndes hdisjes term color found hs2
        have h2 : paintedges (e :: es) term color =
            e :: paintedges es term color := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2, List.map_cons, hih]
        have hne2 : e ≠ found := by
          intro heq
          rw [← heq] at hfterm
          exact hc hfterm
        simp only [hne2, ↓reduceIte]

/-- Painting on a valid graph, read as a map over its
    edge list. -/
theorem paintedgesmap [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (term : Term Sym) (color : Color Sym) (found : Edge Sym)
    (hs : seek graph.edges term = some found) :
    paintedges graph.edges term color =
      graph.edges.map (fun edge =>
        if edge = found then
          ⟨edge.terms,
            if color ∈ edge.colors then edge.colors
            else edge.colors ++ [color]⟩
        else edge) :=
  paintedgesmaplist graph.edges valid.edgenodup
    valid.disjoint term color found hs

/-- Paint a color on the edge holding a named term: the
    color is appended to that edge's color list if not
    already present, and a painting entry is appended to
    the log either way. Painting never alters terms,
    equivalences, levels, or bounds. The fourth of the
    four operations of section 8.2. -/
def paint [DecidableEq Sym] (kinds : Kinds Sym) (graph : Graph Sym)
    (term : Term Sym) (color : Color Sym) (level wit : Sym) :
    Graph Sym :=
  ⟨paintedges graph.edges term color, graph.levels,
    graph.log ++ [⟨kinds.paint, [term], level, wit⟩]⟩

/-- The collected terms are unchanged by painting. -/
theorem paintcollected [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (color : Color Sym)
    (level wit : Sym) (other : Term Sym) :
    collected (paint kinds graph term color level wit) other ↔
      collected graph other := by
  constructor
  · intro h
    obtain ⟨edge, hedge, hinte⟩ := h
    obtain ⟨old, hold, hterms⟩ :=
      paintedgesback graph.edges term color edge hedge
    exact ⟨old, hold, hterms ▸ hinte⟩
  · intro h
    obtain ⟨edge, hedge, hinte⟩ := h
    obtain ⟨new, hnew, hterms, _⟩ :=
      paintedgescover graph.edges term color edge hedge
    exact ⟨new, hnew, hterms ▸ hinte⟩

/-- Equivalence is unchanged by painting. -/
theorem paintsame [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (color : Color Sym)
    (level wit : Sym) (one two : Term Sym) :
    same (paint kinds graph term color level wit) one two ↔
      same graph one two := by
  constructor
  · intro h
    obtain ⟨edge, hedge, h1, h2⟩ := h
    obtain ⟨old, hold, hterms⟩ :=
      paintedgesback graph.edges term color edge hedge
    exact ⟨old, hold, hterms ▸ h1, hterms ▸ h2⟩
  · intro h
    obtain ⟨edge, hedge, h1, h2⟩ := h
    obtain ⟨new, hnew, hterms, _⟩ :=
      paintedgescover graph.edges term color edge hedge
    exact ⟨new, hnew, hterms ▸ h1, hterms ▸ h2⟩

/-- Painting preserves every existing color: a color on
    an edge of the first graph is a color on the painted
    graph's edge with the same terms. -/
theorem paintcolors [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (color : Color Sym)
    (level wit : Sym) (old : Edge Sym) (hold : old ∈ graph.edges)
    (col : Color Sym) (hcol : col ∈ old.colors) :
    ∃ edge ∈ (paint kinds graph term color level wit).edges,
      edge.terms = old.terms ∧ col ∈ edge.colors :=
  paintedgescover graph.edges term color old hold |>.imp
    (fun _ h => ⟨h.1, h.2.1, h.2.2 col hcol⟩)


/-- Painting a list of pairwise disjoint, nonempty,
    repeat free edges keeps it repeat free: the painted
    edge keeps its terms, so it cannot collide with
    another edge, and no other edge changes. -/
theorem paintedgesnodup [DecidableEq Sym] :
    ∀ (edges : List (Edge Sym)), edges.Nodup →
      (∀ one ∈ edges, ∀ two ∈ edges, ∀ t,
        t ∈ one.terms → t ∈ two.terms → one = two) →
      (∀ edge ∈ edges, edge.terms ≠ []) →
      ∀ (term : Term Sym) (color : Color Sym),
        (paintedges edges term color).Nodup := by
  intro edges
  induction edges with
  | nil =>
      intro _ _ _ term color
      exact List.nodup_nil
  | cons e es ih =>
      intro hnd hdisj hne term color
      rw [List.nodup_cons] at hnd
      obtain ⟨hnen, hndes⟩ := hnd
      have hdisjes : ∀ one ∈ es, ∀ two ∈ es, ∀ t,
          t ∈ one.terms → t ∈ two.terms → one = two :=
        fun one hone two htwo t ht1 ht2 =>
          hdisj one (List.mem_cons_of_mem e hone)
            two (List.mem_cons_of_mem e htwo) t ht1 ht2
      have hnees : ∀ edge ∈ es, edge.terms ≠ [] :=
        fun edge hedge => hne edge (List.mem_cons_of_mem e hedge)
      obtain ⟨t, ht⟩ : ∃ t, t ∈ e.terms := by
        cases hxt : e.terms with
        | nil =>
            exact absurd hxt (hne e (by simp))
        | cons z zs =>
            exact ⟨z, by simp⟩
      by_cases hc : term ∈ e.terms
      · have h2 : paintedges (e :: es) term color =
            ⟨e.terms,
              if color ∈ e.colors then e.colors
              else e.colors ++ [color]⟩ :: es := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2, List.nodup_cons]
        refine ⟨?_, hndes⟩
        intro hcon
        have heq := hdisj _ (List.mem_cons_of_mem e hcon)
          e (by simp) t ht ht
        have hmem : e ∈ es := by
          rw [← heq]
          exact hcon
        exact hnen hmem
      · have h2 : paintedges (e :: es) term color =
            e :: paintedges es term color := by
          simp only [paintedges, hc, ↓reduceIte]
        rw [h2, List.nodup_cons]
        refine ⟨?_, ih hndes hdisjes hnees term color⟩
        intro hcon
        obtain ⟨old, hold, hterms⟩ :=
          paintedgesback es term color e hcon
        have ht2 : t ∈ old.terms := by
          rw [hterms]
          exact ht
        have heq := hdisj e (by simp) old
          (List.mem_cons_of_mem e hold) t ht ht2
        exact hnen (heq ▸ hold)

/-- Painting preserves validity. -/
theorem paintvalid [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (term : Term Sym) (color : Color Sym) (level wit : Sym) :
    Valid kinds (paint kinds graph term color level wit) := by
  have h3 : (paint kinds graph term color level wit).levels =
      graph.levels := rfl
  have h4 : (paint kinds graph term color level wit).log =
      graph.log ++ [⟨kinds.paint, [term], level, wit⟩] := rfl
  have hlevels : ∀ lev ∈ (paint kinds graph term color
        level wit).levels, lev.terms.Nodup ∧
        ∀ t ∈ lev.terms,
          collected (paint kinds graph term color level wit) t ∧
          lev.scope t = true := by
    intro lev hlev
    rw [h3] at hlev
    obtain ⟨hnd, hmem⟩ := valid.levels lev hlev
    refine ⟨hnd, fun t ht => ?_⟩
    obtain ⟨hcol, hscope⟩ := hmem t ht
    exact ⟨(paintcollected kinds graph term color level wit
      t).mpr hcol, hscope⟩
  have hexactone : ∀ one two,
      same (paint kinds graph term color level wit) one two →
      reach kinds (paint kinds graph term color level wit).log
        one two := by
    intro one two h
    have hr := valid.exactone one two
      ((paintsame kinds graph term color level wit one two).mp h)
    rw [h4]
    exact reachmono kinds hr
  have hexacttwo : ∀ one two,
      Chain kinds (paint kinds graph term color level wit).log
        one two →
      same (paint kinds graph term color level wit) one two := by
    intro one two h
    rw [h4] at h
    have hc := chainappend kinds
      (log := graph.log)
      (extra := [⟨kinds.paint, [term], level, wit⟩])
      (by
        intro entry hentry
        have heq : entry = ⟨kinds.paint, [term], level, wit⟩ :=
          List.mem_singleton.mp hentry
        rw [heq]
        exact Ne.symm kinds.distinct.2.2.2.2.1)
      h
    exact (paintsame kinds graph term color level wit
      one two).mpr (valid.exacttwo one two hc)
  cases hs : seek graph.edges term with
  | none =>
      have hpe : paintedges graph.edges term color = graph.edges :=
        paintedgesnone graph.edges term color hs
      have h2 : (paint kinds graph term color level wit).edges =
          graph.edges := hpe
      refine ⟨?_, ?_, ?_, ?_, hlevels, hexactone, hexacttwo, ?_⟩
      · intro edge hedge
        rw [h2] at hedge
        exact valid.nonempty edge hedge
      · intro edge hedge
        rw [h2] at hedge
        exact valid.nodup edge hedge
      · intro one hone two htwo t ht1 ht2
        rw [h2] at hone htwo
        exact valid.disjoint one hone two htwo t ht1 ht2
      · intro edge hedge
        rw [h2] at hedge
        exact valid.cnodup edge hedge
      · rw [h2]
        exact valid.edgenodup
  | some found =>
      have hmap := paintedgesmap kinds graph valid term color found hs
      have h2 : (paint kinds graph term color level wit).edges =
          graph.edges.map (fun edge =>
            if edge = found then
              ⟨edge.terms,
                if color ∈ edge.colors then edge.colors
                else edge.colors ++ [color]⟩
            else edge) := hmap
      have hterms : ∀ edge ∈ graph.edges,
          (if edge = found then
            ⟨edge.terms,
              if color ∈ edge.colors then edge.colors
              else edge.colors ++ [color]⟩
            else edge).terms = edge.terms := by
        intro edge _
        by_cases heq : edge = found
        · simp only [heq, ↓reduceIte]
        · simp only [heq, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, hlevels, hexactone, hexacttwo, ?_⟩
      · intro edge hedge
        rw [h2] at hedge
        obtain ⟨old, hold, hmap2⟩ := List.mem_map.mp hedge
        rw [← hmap2]
        rw [hterms old hold]
        exact valid.nonempty old hold
      · intro edge hedge
        rw [h2] at hedge
        obtain ⟨old, hold, hmap2⟩ := List.mem_map.mp hedge
        rw [← hmap2]
        rw [hterms old hold]
        exact valid.nodup old hold
      · intro one hone two htwo t ht1 ht2
        rw [h2] at hone htwo
        obtain ⟨o1, ho1, hm1⟩ := List.mem_map.mp hone
        obtain ⟨o2, ho2, hm2⟩ := List.mem_map.mp htwo
        rw [← hm1] at ht1
        rw [hterms o1 ho1] at ht1
        rw [← hm2] at ht2
        rw [hterms o2 ho2] at ht2
        have heq := valid.disjoint o1 ho1 o2 ho2 t ht1 ht2
        rw [← hm1, ← hm2, heq]
      · intro edge hedge
        rw [h2] at hedge
        obtain ⟨old, hold, hmap2⟩ := List.mem_map.mp hedge
        have hgoal : (if old = found then
              ⟨old.terms,
                if color ∈ old.colors then old.colors
                else old.colors ++ [color]⟩
              else old).colors.Nodup := by
          by_cases heq : old = found
          · rw [if_pos heq]
            by_cases hc2 : color ∈ old.colors
            · rw [if_pos hc2]
              exact valid.cnodup old hold
            · rw [if_neg hc2]
              rw [Aux.nodupappend]
              exact ⟨valid.cnodup old hold, by simp [List.Nodup],
                fun x hx hcon =>
                  absurd (List.mem_singleton.mp hcon ▸ hx) hc2⟩
          · rw [if_neg heq]
            exact valid.cnodup old hold
        rw [← hmap2]
        exact hgoal
      · exact paintedgesnodup graph.edges valid.edgenodup
          valid.disjoint valid.nonempty term color

/- ## The second operation: join two terms -/

/-- Two filters with pointwise equal tests filter
    alike. -/
theorem filtereq {β : Type} (p q : β → Bool)
    (h : ∀ x, p x = q x) : ∀ (list : List β),
      list.filter p = list.filter q := by
  intro list
  induction list with
  | nil => rfl
  | cons x xs ih =>
      by_cases hc : p x = true
      · rw [List.filter_cons_of_pos hc,
          List.filter_cons_of_pos (h x ▸ hc), ih]
      · have hc2 : ¬ q x = true := by
          rw [← h x]
          exact hc
        rw [List.filter_cons_of_neg hc,
          List.filter_cons_of_neg hc2, ih]

/-- A filter whose test passes everywhere is the
    identity. -/
theorem filterall {β : Type} (p : β → Bool) :
    ∀ (list : List β), (∀ x ∈ list, p x = true) →
      list.filter p = list := by
  intro list
  induction list with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.filter_cons_of_pos (h x (by simp)),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Removing the one element a test fails on: the total
    of a count over the filtered list, plus the count of
    the removed element, is the total over the list. -/
theorem filtersum [DecidableEq Sym] (f : Edge Sym → Nat)
    (p : Edge Sym → Bool) :
    ∀ (edges : List (Edge Sym)), ∀ e0 ∈ edges,
      edges.Nodup →
      (∀ e ∈ edges, (¬ p e = true) ↔ e = e0) →
      ((edges.filter p).map f).sum + f e0 =
        (edges.map f).sum := by
  intro edges
  induction edges with
  | nil =>
      intro e0 he0 _ _
      cases he0
  | cons x xs ih =>
      intro e0 he0 hnd hex
      rw [List.nodup_cons] at hnd
      obtain ⟨hxnd, hxsnd⟩ := hnd
      by_cases hxe : x = e0
      · have hpx : ¬ p x = true := (hex x (by simp)).mpr hxe
        have hfall : ∀ e ∈ xs, p e = true := by
          intro e he
          by_cases hpe : p e = true
          · exact hpe
          · have hee := (hex e (List.mem_cons_of_mem x he)).mp hpe
            rw [← hxe] at hee
            rw [hee] at he
            exact absurd he hxnd
        rw [List.filter_cons_of_neg hpx,
          filterall p xs hfall]
        simp only [List.map_cons, List.sum_cons, hxe]
        omega
      · have hpx : p x = true := by
          by_cases hp : p x = true
          · exact hp
          · exact absurd ((hex x (by simp)).mp hp) hxe
        have he0xs : e0 ∈ xs := by
          cases List.mem_cons.mp he0 with
          | inl h => exact absurd h.symm hxe
          | inr h => exact h
        have hexs : ∀ e ∈ xs, (¬ p e = true) ↔ e = e0 :=
          fun e he => hex e (List.mem_cons_of_mem x he)
        have hih := ih e0 he0xs hxsnd hexs
        rw [List.filter_cons_of_pos hpx]
        simp only [List.map_cons, List.sum_cons]
        omega

/-- The merged edge of a join: the two term lists
    joined and the two color lists united, up to
    membership. -/
def merged [DecidableEq Sym] (one two : Edge Sym) : Edge Sym :=
  ⟨one.terms ++ two.terms, union one.colors two.colors⟩

/-- The edge list of a join: the edges holding neither
    of the two terms, with the merged edge appended.
    When either term is not collected the list is
    unchanged; the join operation enters both terms
    first, so on its outputs both are collected. -/
def joinEdges [DecidableEq Sym] (edges : List (Edge Sym))
    (one two : Term Sym) : List (Edge Sym) :=
  match seek edges one, seek edges two with
  | some ea, some eb =>
      (edges.filter (fun edge =>
        decide (one ∉ edge.terms) &&
          decide (two ∉ edge.terms))) ++ [merged ea eb]
  | _, _ => edges

/-- Membership in a joined edge list, when both terms
    are collected in edges that differ: an edge is a
    kept old edge, holding neither term, or it is the
    merged edge. -/
theorem joinEdgesmem [DecidableEq Sym]
    (graph : Graph Sym)
    (one two : Term Sym) (ea eb : Edge Sym)
    (ha : seek graph.edges one = some ea)
    (hb : seek graph.edges two = some eb)
    (edge : Edge Sym) :
    edge ∈ joinEdges graph.edges one two ↔
      (edge ∈ graph.edges ∧ one ∉ edge.terms ∧
        two ∉ edge.terms) ∨ edge = merged ea eb := by
  have hje : joinEdges graph.edges one two =
      (graph.edges.filter (fun e =>
        decide (one ∉ e.terms) &&
          decide (two ∉ e.terms))) ++ [merged ea eb] := by
    simp only [joinEdges, ha, hb]
  rw [hje]
  constructor
  · intro h
    cases List.mem_append.mp h with
    | inl hm =>
        rw [List.mem_filter] at hm
        obtain ⟨h1, h2⟩ := hm
        have h2' : (decide (one ∉ edge.terms) &&
            decide (two ∉ edge.terms)) = true := h2
        rw [Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq] at h2'
        exact Or.inl ⟨h1, h2'.1, h2'.2⟩
    | inr hm =>
        exact Or.inr (List.mem_singleton.mp hm)
  · intro h
    cases h with
    | inl h =>
        apply List.mem_append_left
        rw [List.mem_filter]
        exact ⟨h.1, by
          rw [Bool.and_eq_true, decide_eq_true_eq,
            decide_eq_true_eq]
          exact ⟨h.2.1, h.2.2⟩⟩
    | inr h =>
        apply List.mem_append_right
        rw [h]
        exact List.mem_singleton_self _

/-- The merge step of a join, on a graph where both
    terms are collected: if they already stand in one
    edge, the edges do not change; if they stand in two
    edges, those two edges are replaced by the merged
    edge. Either way an equivalence entry is appended.
    Replacement here is growth, not revision: the two
    edges' terms and colors are all carried into the one
    edge, and nothing is dropped. -/
def merge [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Term Sym)
    (level wit : Sym) : Graph Sym :=
  match seek graph.edges one, seek graph.edges two with
  | some ea, some eb =>
      if ea = eb then
        ⟨graph.edges, graph.levels,
          graph.log ++ [⟨kinds.join, [one, two], level, wit⟩]⟩
      else
        ⟨joinEdges graph.edges one two, graph.levels,
          graph.log ++ [⟨kinds.join, [one, two], level, wit⟩]⟩
  | _, _ =>
      ⟨graph.edges, graph.levels,
        graph.log ++ [⟨kinds.join, [one, two], level, wit⟩]⟩

/-- The join of two terms: both terms are entered first,
    in the same step if needed, and then merged. The
    second of the four operations of section 8.2. -/
def join [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Term Sym)
    (level wit : Sym) : Graph Sym :=
  merge kinds
    (enter kinds (enter kinds graph one level wit)
      two level wit)
    one two level wit

/-- Transitivity of standing together, from a partition
    of one edge list alone: the two edges holding the
    middle term are one edge. -/
theorem sametransof {edges : List (Edge Sym)}
    (hdisj : ∀ one ∈ edges, ∀ two ∈ edges, ∀ t,
      t ∈ one.terms → t ∈ two.terms → one = two)
    {x y z : Term Sym}
    (h1 : ∃ e ∈ edges, x ∈ e.terms ∧ y ∈ e.terms)
    (h2 : ∃ e ∈ edges, y ∈ e.terms ∧ z ∈ e.terms) :
    ∃ e ∈ edges, x ∈ e.terms ∧ z ∈ e.terms := by
  obtain ⟨e1, he1, h1a, h1b⟩ := h1
  obtain ⟨e2, he2, h2a, h2b⟩ := h2
  have heq := hdisj e1 he1 e2 he2 y h1b h2a
  exact ⟨e1, he1, h1a, heq ▸ h2b⟩

/-- Entering changes the excess by zero: a new singleton
    edge adds one term and one edge, and a repeat entry
    adds neither. -/
theorem enterexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym) :
    excess (enter kinds graph term level wit) = excess graph := by
  cases hs : seek graph.edges term with
  | some found =>
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges := by simp only [enter, hs]
      simp only [excess, h2]
  | none =>
      have h2 : (enter kinds graph term level wit).edges =
          graph.edges ++ [⟨[term], []⟩] := by simp only [enter, hs]
      have hsum : ((graph.edges ++
          [(⟨[term], []⟩ : Edge Sym)]).map
          (fun e => e.terms.length)).sum =
          (graph.edges.map (fun e => e.terms.length)).sum + 1 := by
        rw [Aux.mapsumappend]
        simp
      have hlen : (graph.edges ++
          [(⟨[term], []⟩ : Edge Sym)]).length =
          graph.edges.length + 1 := by simp
      simp only [excess, h2, hsum, hlen]
      omega

/-- The merge step preserves validity, on a graph where
    both terms are collected. When the terms already
    stand together, only the log grows, by an entry whose
    pair already stands in one edge. When they stand in
    two edges, the merged edge carries every term and
    every color of both, the partition is kept, and the
    new entry joins exactly the classes it merges. -/
theorem mergevalid [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym)
    (hcol1 : collected graph one) (hcol2 : collected graph two)
    (level wit : Sym) :
    Valid kinds (merge kinds graph one two level wit) := by
  obtain ⟨ea, ha, heain, haine⟩ := seekof graph.edges one hcol1
  obtain ⟨eb, hb, hebin, hbine⟩ := seekof graph.edges two hcol2
  have h3 : (merge kinds graph one two level wit).levels =
      graph.levels := by
    cases hs1 : seek graph.edges one <;>
      cases hs2 : seek graph.edges two <;>
      simp only [merge, hs1, hs2] <;>
      split <;> rfl
  have h4 : (merge kinds graph one two level wit).log =
      graph.log ++ [⟨kinds.join, [one, two], level, wit⟩] := by
    cases hs1 : seek graph.edges one <;>
      cases hs2 : seek graph.edges two <;>
      simp only [merge, hs1, hs2] <;>
      split <;> rfl
  by_cases hee : ea = eb
  · have h2 : (merge kinds graph one two level wit).edges =
        graph.edges := by
      simp only [merge, ha, hb, hee, ↓reduceIte]
    have hdisj : ∀ o1 ∈ (merge kinds graph one two
          level wit).edges,
        ∀ o2 ∈ (merge kinds graph one two level wit).edges,
        ∀ t, t ∈ o1.terms → t ∈ o2.terms → o1 = o2 := by
      intro o1 ho1 o2 ho2 t ht1 ht2
      rw [h2] at ho1 ho2
      exact valid.disjoint o1 ho1 o2 ho2 t ht1 ht2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro edge hedge
      rw [h2] at hedge
      exact valid.nonempty edge hedge
    · intro edge hedge
      rw [h2] at hedge
      exact valid.nodup edge hedge
    · exact hdisj
    · intro edge hedge
      rw [h2] at hedge
      exact valid.cnodup edge hedge
    · intro lev hlev
      rw [h3] at hlev
      obtain ⟨hnd, hmem⟩ := valid.levels lev hlev
      refine ⟨hnd, fun t ht => ?_⟩
      obtain ⟨hcol, hscope⟩ := hmem t ht
      obtain ⟨edge, hedge, hinte⟩ := hcol
      exact ⟨⟨edge, h2 ▸ hedge, hinte⟩, hscope⟩
    · intro x y h
      obtain ⟨edge, hedge, hx, hy⟩ := h
      rw [h2] at hedge
      have hr := valid.exactone x y ⟨edge, hedge, hx, hy⟩
      rw [h4]
      exact reachmono kinds hr
    · intro x y h
      rw [h4] at h
      induction h with
      | step hstep =>
          obtain ⟨entry, hentry, hkind, hx, hy⟩ := hstep
          cases List.mem_append.mp hentry with
          | inl hm =>
              have hs2 := valid.exacttwo _ _
                (Chain.step ⟨entry, hm, hkind, hx, hy⟩)
              obtain ⟨edge, hedge, hx2, hy2⟩ := hs2
              exact ⟨edge, h2 ▸ hedge, hx2, hy2⟩
          | inr hm =>
              have heq : entry =
                  ⟨kinds.join, [one, two], level, wit⟩ :=
                List.mem_singleton.mp hm
              rw [heq] at hx hy
              have htwoea : two ∈ ea.terms := hee ▸ hbine
              refine ⟨ea, h2 ▸ heain, ?_, ?_⟩
              · cases List.mem_cons.mp hx with
                | inl h =>
                    rw [h]
                    exact haine
                | inr h =>
                    cases List.mem_cons.mp h with
                    | inl h =>
                        rw [h]
                        exact htwoea
                    | inr h => cases h
              · cases List.mem_cons.mp hy with
                | inl h =>
                    rw [h]
                    exact haine
                | inr h =>
                    cases List.mem_cons.mp h with
                    | inl h =>
                        rw [h]
                        exact htwoea
                    | inr h => cases h
      | trans _ _ ih1 ih2 =>
          exact sametransof hdisj ih1 ih2
    · rw [h2]
      exact valid.edgenodup
  · have h2 : (merge kinds graph one two level wit).edges =
        joinEdges graph.edges one two := by
      simp only [merge, ha, hb, hee, ↓reduceIte]
    have hmem : ∀ edge, edge ∈ joinEdges graph.edges one two ↔
        (edge ∈ graph.edges ∧ one ∉ edge.terms ∧
          two ∉ edge.terms) ∨ edge = merged ea eb :=
      fun edge => joinEdgesmem graph one two ea eb ha hb edge
    have hcover : ∀ e ∈ graph.edges,
        ∃ e' ∈ joinEdges graph.edges one two,
          ∀ t ∈ e.terms, t ∈ e'.terms := by
      intro e he
      by_cases h1 : one ∈ e.terms
      · have heq : e = ea :=
          valid.disjoint e he ea heain one h1 haine
        refine ⟨merged ea eb, (hmem (merged ea eb)).mpr
          (Or.inr rfl), ?_⟩
        intro t ht
        rw [heq] at ht
        exact List.mem_append_left _ ht
      · by_cases h2' : two ∈ e.terms
        · have heq : e = eb :=
            valid.disjoint e he eb hebin two h2' hbine
          refine ⟨merged ea eb, (hmem (merged ea eb)).mpr
            (Or.inr rfl), ?_⟩
          intro t ht
          rw [heq] at ht
          exact List.mem_append_right _ ht
        · exact ⟨e, (hmem e).mpr (Or.inl ⟨he, h1, h2'⟩),
            fun t ht => ht⟩
    have hcollected : ∀ t, collected graph t →
        collected (merge kinds graph one two level wit) t := by
      intro t hcol
      obtain ⟨e, he, ht⟩ := hcol
      obtain ⟨e', he', hcover2⟩ := hcover e he
      exact ⟨e', h2 ▸ he', hcover2 t ht⟩
    have hdisj : ∀ o1 ∈ (merge kinds graph one two
          level wit).edges,
        ∀ o2 ∈ (merge kinds graph one two level wit).edges,
        ∀ t, t ∈ o1.terms → t ∈ o2.terms → o1 = o2 := by
      intro o1 ho1 o2 ho2 t ht1 ht2
      rw [h2] at ho1 ho2
      cases (hmem o1).mp ho1 with
      | inl h1 =>
          cases (hmem o2).mp ho2 with
          | inl h2' =>
              exact valid.disjoint o1 h1.1 o2 h2'.1 t ht1 ht2
          | inr h2' =>
              rw [h2'] at ht2
              cases List.mem_append.mp ht2 with
              | inl ht =>
                  have heq := valid.disjoint o1 h1.1 ea heain
                    t ht1 ht
                  exact (h1.2.1 (heq ▸ haine)).elim
              | inr ht =>
                  have heq := valid.disjoint o1 h1.1 eb hebin
                    t ht1 ht
                  exact (h1.2.2 (heq ▸ hbine)).elim
      | inr h1 =>
          cases (hmem o2).mp ho2 with
          | inl h2' =>
              rw [h1] at ht1
              cases List.mem_append.mp ht1 with
              | inl ht =>
                  have heq := valid.disjoint ea heain o2 h2'.1
                    t ht ht2
                  exact (h2'.2.1 (heq ▸ haine)).elim
              | inr ht =>
                  have heq := valid.disjoint eb hebin o2 h2'.1
                    t ht ht2
                  exact (h2'.2.2 (heq ▸ hbine)).elim
          | inr h2' =>
              rw [h1, h2']
    have hsameold : ∀ x y, same graph x y →
        same (merge kinds graph one two level wit) x y := by
      intro x y h
      obtain ⟨e, he, hx, hy⟩ := h
      obtain ⟨e', he', hcover2⟩ := hcover e he
      exact ⟨e', h2 ▸ he', hcover2 x hx, hcover2 y hy⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro edge hedge
      rw [h2] at hedge
      cases (hmem edge).mp hedge with
      | inl h1 =>
          exact valid.nonempty edge h1.1
      | inr h1 =>
          rw [h1]
          intro hcon
          have hcon2 : ea.terms ++ eb.terms = [] := hcon
          have hempty : ea.terms = [] := by
            cases hterms : ea.terms with
            | nil => rfl
            | cons z zs =>
                rw [hterms] at hcon2
                simp at hcon2
          exact valid.nonempty ea heain hempty
    · intro edge hedge
      rw [h2] at hedge
      cases (hmem edge).mp hedge with
      | inl h1 =>
          exact valid.nodup edge h1.1
      | inr h1 =>
          rw [h1]
          show (ea.terms ++ eb.terms).Nodup
          rw [Aux.nodupappend]
          exact ⟨valid.nodup ea heain, valid.nodup eb hebin,
            fun x hx hcon =>
              hee (valid.disjoint ea heain eb hebin x hx hcon)⟩
    · exact hdisj
    · intro edge hedge
      rw [h2] at hedge
      cases (hmem edge).mp hedge with
      | inl h1 =>
          exact valid.cnodup edge h1.1
      | inr h1 =>
          rw [h1]
          exact unionnodup ea.colors eb.colors
            (valid.cnodup ea heain) (valid.cnodup eb hebin)
    · intro lev hlev
      rw [h3] at hlev
      obtain ⟨hnd, hmem2⟩ := valid.levels lev hlev
      refine ⟨hnd, fun t ht => ?_⟩
      obtain ⟨hcol, hscope⟩ := hmem2 t ht
      exact ⟨hcollected t hcol, hscope⟩
    · intro x y h
      obtain ⟨edge, hedge, hx, hy⟩ := h
      rw [h2] at hedge
      rw [h4]
      cases (hmem edge).mp hedge with
      | inl h1 =>
          have hr := valid.exactone x y ⟨edge, h1.1, hx, hy⟩
          exact reachmono kinds hr
      | inr h1 =>
          rw [h1] at hx hy
          have hclass : (reach kinds graph.log x one ∨
                reach kinds graph.log x two) ∧
              (reach kinds graph.log y one ∨
                reach kinds graph.log y two) := by
            constructor
            · cases List.mem_append.mp hx with
              | inl hx2 =>
                  exact Or.inl (valid.exactone x one
                    ⟨ea, heain, hx2, haine⟩)
              | inr hx2 =>
                  exact Or.inr (valid.exactone x two
                    ⟨eb, hebin, hx2, hbine⟩)
            · cases List.mem_append.mp hy with
              | inl hy2 =>
                  exact Or.inl (valid.exactone y one
                    ⟨ea, heain, hy2, haine⟩)
              | inr hy2 =>
                  exact Or.inr (valid.exactone y two
                    ⟨eb, hebin, hy2, hbine⟩)
          exact (reachjoin kinds graph.log one two level
            wit).mpr (Or.inr hclass)
    · intro x y h
      rw [h4] at h
      induction h with
      | step hstep =>
          obtain ⟨entry, hentry, hkind, hx, hy⟩ := hstep
          cases List.mem_append.mp hentry with
          | inl hm =>
              exact hsameold _ _ (valid.exacttwo _ _
                (Chain.step ⟨entry, hm, hkind, hx, hy⟩))
          | inr hm =>
              have heq : entry =
                  ⟨kinds.join, [one, two], level, wit⟩ :=
                List.mem_singleton.mp hm
              rw [heq] at hx hy
              have hcross : same (merge kinds graph one two
                  level wit) one two :=
                ⟨merged ea eb, h2 ▸ (hmem (merged ea eb)).mpr
                  (Or.inr rfl),
                  List.mem_append_left _ haine,
                  List.mem_append_right _ hbine⟩
              cases List.mem_cons.mp hx with
              | inl hx1 =>
                  cases List.mem_cons.mp hy with
                  | inl hy1 =>
                      rw [hx1, hy1]
                      exact samerefl _ _ (hcollected one hcol1)
                  | inr hy1 =>
                      cases List.mem_cons.mp hy1 with
                      | inl hy2 =>
                          rw [hx1, hy2]
                          exact hcross
                      | inr hy2 => cases hy2
              | inr hx1 =>
                  cases List.mem_cons.mp hx1 with
                  | inl hx2 =>
                      cases List.mem_cons.mp hy with
                      | inl hy1 =>
                          rw [hx2, hy1]
                          exact samesymm _ hcross
                      | inr hy1 =>
                          cases List.mem_cons.mp hy1 with
                          | inl hy2 =>
                              rw [hx2, hy2]
                              exact samerefl _ _
                                (hcollected two hcol2)
                          | inr hy2 => cases hy2
                  | inr hx2 => cases hx2
      | trans _ _ ih1 ih2 =>
          exact sametransof hdisj ih1 ih2
    · have hje : joinEdges graph.edges one two =
          (graph.edges.filter (fun e =>
            decide (one ∉ e.terms) &&
              decide (two ∉ e.terms))) ++
            [merged ea eb] := by
        simp only [joinEdges, ha, hb]
      rw [h2, hje, Aux.nodupappend]
      refine ⟨List.Sublist.nodup List.filter_sublist
        valid.edgenodup, by simp [List.Nodup], ?_⟩
      intro e he hcon
      rw [List.mem_filter] at he
      have heq : e = merged ea eb :=
        List.mem_singleton.mp hcon
      have h2' : (decide (one ∉ e.terms) &&
          decide (two ∉ e.terms)) = true := he.2
      rw [Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq] at h2'
      exact h2'.1 (heq ▸ List.mem_append_left _ haine)

/-- The join operation preserves validity: its two
    terms are entered first, and entering preserves
    validity and collects them, and then the merge step
    preserves validity on collected terms. -/
theorem joinvalid [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    Valid kinds (join kinds graph one two level wit) := by
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
  exact mergevalid kinds _ hv2 one two hcol1 hcol2 level wit

/-- The excess change of a merge: exactly one when the
    two terms stand in two edges, and zero when they
    already stand in one edge or one is not collected. -/
theorem mergeexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    excess (merge kinds graph one two level wit) =
      excess graph +
        (match seek graph.edges one, seek graph.edges two with
          | some ea, some eb => if ea = eb then 0 else 1
          | _, _ => 0) := by
  by_cases hcol1 : collected graph one
  · by_cases hcol2 : collected graph two
    · obtain ⟨ea, ha, heain, haine⟩ := seekof graph.edges one hcol1
      obtain ⟨eb, hb, hebin, hbine⟩ := seekof graph.edges two hcol2
      by_cases hee : ea = eb
      · have h2 : (merge kinds graph one two level wit).edges =
            graph.edges := by
          simp only [merge, ha, hb, hee, ↓reduceIte]
        simp only [excess, h2, ha, hb, hee, ↓reduceIte,
          Nat.add_zero]
      · have h2 : (merge kinds graph one two level wit).edges =
            joinEdges graph.edges one two := by
          simp only [merge, ha, hb, hee, ↓reduceIte]
        have hje : joinEdges graph.edges one two =
            (graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))) ++
              [merged ea eb] := by
          simp only [joinEdges, ha, hb]
        have hpa : ∀ e ∈ graph.edges,
            (¬ (decide (one ∉ e.terms)) = true) ↔
              one ∈ e.terms := by
          intro e _
          constructor
          · intro h
            by_cases hc : one ∈ e.terms
            · exact hc
            · exact absurd (decide_eq_true_iff.mpr hc) h
          · intro h hcon
            exact (of_decide_eq_true hcon) h
        have hpb : ∀ e ∈ graph.edges,
            (¬ (decide (two ∉ e.terms)) = true) ↔
              two ∈ e.terms := by
          intro e _
          constructor
          · intro h
            by_cases hc : two ∈ e.terms
            · exact hc
            · exact absurd (decide_eq_true_iff.mpr hc) h
          · intro h hcon
            exact (of_decide_eq_true hcon) h
        have hexb : ∀ e ∈ graph.edges,
            (¬ (fun x => decide (two ∉ x.terms)) e = true) ↔
              e = eb := by
          intro e he
          constructor
          · intro h
            have h2' : two ∈ e.terms := by
              have := (hpb e he).mp h
              exact this
            exact valid.disjoint e he eb hebin two h2' hbine
          · intro h
            rw [h]
            show ¬ (decide (two ∉ eb.terms)) = true
            intro hcon
            exact (of_decide_eq_true hcon) hbine
        have hexaf : ∀ e ∈ graph.edges.filter
              (fun x => decide (two ∉ x.terms)),
            (¬ (fun x => decide (one ∉ x.terms)) e = true) ↔
              e = ea := by
          intro e he
          rw [List.mem_filter] at he
          constructor
          · intro h
            have h2' : one ∈ e.terms := by
              have := (hpa e he.1).mp h
              exact this
            exact valid.disjoint e he.1 ea heain one h2' haine
          · intro h
            rw [h]
            show ¬ (decide (one ∉ ea.terms)) = true
            intro hcon
            exact (of_decide_eq_true hcon) haine
        have heaf : ea ∈ graph.edges.filter
            (fun x => decide (two ∉ x.terms)) := by
          rw [List.mem_filter]
          refine ⟨heain, ?_⟩
          simp only [decide_eq_true_eq]
          intro hcon
          exact hee (valid.disjoint ea heain eb hebin two
            hcon hbine)
        have hfilternodup : (graph.edges.filter
            (fun x => decide (two ∉ x.terms))).Nodup :=
          List.Sublist.nodup List.filter_sublist valid.edgenodup
        have hsum1 : ∀ f : Edge Sym → Nat,
            ((graph.edges.filter
              (fun x => decide (two ∉ x.terms))).map f).sum +
              f eb = (graph.edges.map f).sum :=
          fun f => filtersum f _ graph.edges eb hebin
            valid.edgenodup hexb
        have hsum2 : ∀ f : Edge Sym → Nat,
            (((graph.edges.filter
              (fun x => decide (two ∉ x.terms))).filter
              (fun x => decide (one ∉ x.terms))).map f).sum +
              f ea = ((graph.edges.filter
              (fun x => decide (two ∉ x.terms))).map f).sum :=
          fun f => filtersum f _ _ ea heaf hfilternodup hexaf
        have hfiltereq : graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms)) =
            (graph.edges.filter
              (fun x => decide (two ∉ x.terms))).filter
              (fun x => decide (one ∉ x.terms)) := by
          rw [List.filter_filter]
        have hsumf : ∀ f : Edge Sym → Nat,
            ((graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))).map f).sum +
              f ea + f eb = (graph.edges.map f).sum := by
          intro f
          have h1 := hsum1 f
          have h2' := hsum2 f
          rw [hfiltereq]
          omega
        have hlen : (graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))).length + 1 + 1 =
            graph.edges.length := by
          have h1 := hsumf (fun _ => 1)
          have e1 : ∀ (l : List (Edge Sym)),
              (l.map (fun _ => 1)).sum = l.length :=
            fun l => Aux.sumone (fun _ => 1) l (fun _ _ => rfl)
          simp only [e1] at h1
          omega
        have hsum : ((graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))).map
              (fun e => e.terms.length)).sum +
              ea.terms.length + eb.terms.length =
            (graph.edges.map (fun e => e.terms.length)).sum :=
          hsumf _
        have hmergedlen : (merged ea eb).terms.length =
            ea.terms.length + eb.terms.length :=
          List.length_append
        have htotal : ((joinEdges graph.edges one two).map
              (fun e => e.terms.length)).sum =
            ((graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))).map
              (fun e => e.terms.length)).sum +
              (merged ea eb).terms.length := by
          rw [hje, Aux.mapsumappend]
          simp
        have hlentotal : (joinEdges graph.edges one
            two).length =
            (graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))).length + 1 := by
          rw [hje]
          simp
        have hge : graph.edges.length ≤
            (graph.edges.map (fun e => e.terms.length)).sum :=
          Aux.sumge (fun e => e.terms.length) graph.edges
            (fun x hx => Aux.lengthpos (valid.nonempty x hx))
        simp only [excess, h2, ha, hb, hee, ↓reduceIte]
        omega
    · have hseek : seek graph.edges two = none := by
        by_cases hs : seek graph.edges two = none
        · exact hs
        · cases hso : seek graph.edges two with
          | none => rfl
          | some found =>
              obtain ⟨hfin, hfterm⟩ :=
                seeksome graph.edges two found hso
              exact absurd ⟨found, hfin, hfterm⟩ hcol2
      have h2 : (merge kinds graph one two level wit).edges =
          graph.edges := by
        simp only [merge, hseek]
        cases seek graph.edges one <;> rfl
      rw [show excess (merge kinds graph one two level wit) =
          excess graph by simp only [excess, h2]]
      rw [hseek]
      cases seek graph.edges one <;> simp
  · have hseek : seek graph.edges one = none := by
      by_cases hs : seek graph.edges one = none
      · exact hs
      · cases hso : seek graph.edges one with
        | none => rfl
        | some found =>
            obtain ⟨hfin, hfterm⟩ :=
              seeksome graph.edges one found hso
            exact absurd ⟨found, hfin, hfterm⟩ hcol1
    have h2 : (merge kinds graph one two level wit).edges =
        graph.edges := by
      simp only [merge, hseek]
    rw [show excess (merge kinds graph one two level wit) =
        excess graph by simp only [excess, h2]]
    rw [hseek]
    cases seek graph.edges two <;> simp

/-- The number of effective joins a join operation makes
    on a graph: one when its merge step merges two
    edges, and zero otherwise. An effective join is a
    join that merges two edges at its moment. -/
def eff [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Term Sym)
    (level wit : Sym) : Nat :=
  match seek (enter kinds (enter kinds graph one level wit)
      two level wit).edges one,
    seek (enter kinds (enter kinds graph one level wit)
      two level wit).edges two with
  | some ea, some eb => if ea = eb then 0 else 1
  | _, _ => 0

/-- The excess change of a join operation is exactly its
    effective join count: the two entries change the
    excess by zero, and the merge changes it by one
    exactly when it merges. -/
theorem joinexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    excess (join kinds graph one two level wit) =
      excess graph + eff kinds graph one two level wit := by
  have h1 := enterexcess kinds graph one level wit
  have h2 := enterexcess kinds
    (enter kinds graph one level wit) two level wit
  have hv1 := entervalid kinds graph valid one level wit
  have hv2 := entervalid kinds _ hv1 two level wit
  have h3 := mergeexcess kinds
    (enter kinds (enter kinds graph one level wit)
      two level wit) hv2 one two level wit
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
  have h4 : excess (join kinds graph one two level wit) =
      excess (enter kinds (enter kinds graph one level wit)
        two level wit) +
        (match seek (enter kinds (enter kinds graph one
            level wit) two level wit).edges one,
          seek (enter kinds (enter kinds graph one
            level wit) two level wit).edges two with
          | some ea, some eb => if ea = eb then 0 else 1
          | _, _ => 0) := h3
  rw [h4, h2, h1]
  rfl

/-- Painting a list of edges changes neither the sum
    of the edge sizes nor the edge count: the recursion
    only ever grows the colors of the first edge holding
    the term. -/
theorem paintedgesexcess [DecidableEq Sym] :
    ∀ (l : List (Edge Sym)) (term : Term Sym)
      (color : Color Sym),
      ((paintedges l term color).map
        (fun e => e.terms.length)).sum =
        (l.map (fun e => e.terms.length)).sum ∧
        (paintedges l term color).length = l.length
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: es, term, color => by
      obtain ⟨ih1, ih2⟩ := paintedgesexcess es term color
      by_cases h : term ∈ e.terms
      · constructor
        · simp only [paintedges, h, ↓reduceIte, List.map_cons,
            List.sum_cons, ih1]
        · simp only [paintedges, h, ↓reduceIte,
            List.length_cons, ih2]
      · constructor
        · simp only [paintedges, h, ↓reduceIte, List.map_cons,
            List.sum_cons, ih1]
        · simp only [paintedges, h, ↓reduceIte,
            List.length_cons, ih2]

/-- Painting changes no excess: it changes colors only,
    and the edge terms and the edge count stand. -/
theorem paintexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (color : Color Sym)
    (level wit : Sym) :
    excess (paint kinds graph term color level wit) =
      excess graph := by
  obtain ⟨h1, h2⟩ := paintedgesexcess graph.edges term color
  rw [show excess (paint kinds graph term color level
      wit) =
      ((paintedges graph.edges term color).map
        (fun e => e.terms.length)).sum -
        (paintedges graph.edges term color).length from rfl,
    h1, h2]
  rfl

/-- Entering a list of terms, one after another: the
    fold of the enter operation over the list. -/
def enterall [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (terms : List (Term Sym))
    (level wit : Sym) : Graph Sym :=
  terms.foldl (fun g t => enter kinds g t level wit) graph

/-- The log after entering a list: the old log followed
    by one entry per listed term, in list order. -/
theorem enteralllog [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym),
      (enterall kinds graph terms level wit).log =
        graph.log ++ terms.map (fun t =>
          (⟨kinds.enter, [t], level, wit⟩ : Entry Sym)) := by
  induction terms with
  | nil =>
      intro graph
      simp only [enterall, List.foldl_nil, List.map_nil,
        List.append_nil]
  | cons t ts ih =>
      intro graph
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1, ih, enterlog]
      simp [List.append_assoc]

/-- Entering a list keeps the levels standing. -/
theorem enteralllevels [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym),
      (enterall kinds graph terms level wit).levels =
        graph.levels := by
  induction terms with
  | nil => intro graph; rfl
  | cons t ts ih =>
      intro graph
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1, ih, enterlevels]

/-- Entering a list keeps every edge standing as a
    member: an old edge is never removed, only new
    singleton edges are appended. -/
theorem enteralledges [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym) (edge : Edge Sym),
      edge ∈ graph.edges →
        edge ∈ (enterall kinds graph terms level wit).edges := by
  induction terms with
  | nil => intro graph edge hedge; exact hedge
  | cons t ts ih =>
      intro graph edge hedge
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1]
      apply ih
      by_cases hs : seek graph.edges t = none
      · have h2 : (enter kinds graph t level wit).edges =
            graph.edges ++ [{ terms := [t], colors := [] }] := by
          simp only [enter, hs]
        rw [h2]
        exact List.mem_append_left _ hedge
      · have h2 : (enter kinds graph t level wit).edges =
            graph.edges := by
          cases hso : seek graph.edges t with
          | none => exact absurd hso hs
          | some found => simp only [enter, hso]
        rw [h2]
        exact hedge

/-- Entering a list keeps every collected term
    collected. -/
theorem enterallkeeps [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym) (term : Term Sym),
      collected graph term →
        collected (enterall kinds graph terms level wit)
          term := by
  induction terms with
  | nil => intro graph term hcol; exact hcol
  | cons t ts ih =>
      intro graph term hcol
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1]
      apply ih
      exact (entercollected kinds graph t level wit
        term).mpr (Or.inl hcol)

/-- Every listed term is collected after entering the
    list. -/
theorem enterallcollected [DecidableEq Sym]
    (kinds : Kinds Sym) (terms : List (Term Sym))
    (level wit : Sym) :
    ∀ (graph : Graph Sym) (term : Term Sym),
      term ∈ terms →
        collected (enterall kinds graph terms level wit)
          term := by
  induction terms with
  | nil => intro graph term hmem; cases hmem
  | cons t ts ih =>
      intro graph term hmem
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1]
      cases List.mem_cons.mp hmem with
      | inl heq =>
          apply enterallkeeps
          rw [heq]
          exact (entercollected kinds graph t level wit
            t).mpr (Or.inr rfl)
      | inr hts =>
          exact ih _ term hts

/-- Equivalence after entering a list: the old
    equivalence, or the two terms are one term standing
    in the list. Entering collects each listed term in
    its own singleton edge, so two distinct listed terms
    do not stand together unless they already did. -/
theorem enterallsame [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym) (one two : Term Sym),
      same (enterall kinds graph terms level wit) one two ↔
        same graph one two ∨ (one = two ∧ one ∈ terms) := by
  induction terms with
  | nil =>
      intro graph one two
      constructor
      · intro h
        exact Or.inl h
      · intro h
        cases h with
        | inl h => exact h
        | inr h => cases h.2
  | cons t ts ih =>
      intro graph one two
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1, ih, entersame]
      constructor
      · intro h
        cases h with
        | inl h =>
            cases h with
            | inl h => exact Or.inl h
            | inr h =>
                exact Or.inr ⟨h.1.trans h.2.symm,
                  List.mem_cons.mpr (Or.inl h.1)⟩
        | inr h =>
            exact Or.inr ⟨h.1,
              List.mem_cons.mpr (Or.inr h.2)⟩
      · intro h
        cases h with
        | inl h => exact Or.inl (Or.inl h)
        | inr h =>
            cases List.mem_cons.mp h.2 with
            | inl e1 =>
                exact Or.inl (Or.inr ⟨e1, h.1.symm.trans e1⟩)
            | inr e2 =>
                exact Or.inr ⟨h.1, e2⟩

/-- Entering a list preserves validity. -/
theorem enterallvalid [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym), Valid kinds graph →
      Valid kinds (enterall kinds graph terms level wit) := by
  induction terms with
  | nil => intro graph valid; exact valid
  | cons t ts ih =>
      intro graph valid
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1]
      exact ih _ (entervalid kinds graph valid t level wit)

/-- Entering a list changes no excess. -/
theorem enterallexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (terms : List (Term Sym)) (level wit : Sym) :
    ∀ (graph : Graph Sym),
      excess (enterall kinds graph terms level wit) =
        excess graph := by
  induction terms with
  | nil => intro graph; rfl
  | cons t ts ih =>
      intro graph
      have h1 : enterall kinds graph (t :: ts) level wit =
          enterall kinds (enter kinds graph t level wit) ts
            level wit := rfl
      rw [h1, ih, enterexcess]

/-- Whether a level already stands recorded on the
    graph: a standing level with the same name, the same
    terms, and the same scope. -/
def haslevel (graph : Graph Sym) (level : Level Sym) :
    Prop :=
  ∃ old ∈ graph.levels, old.name = level.name ∧
    old.terms = level.terms ∧ old.scope = level.scope

/-- The record operation: the level's terms are entered
    first; when a level of the same name, the same
    terms, and the same scope already stands, nothing is
    appended; otherwise the level is appended to the
    levels and one entry is appended to the log, its
    terms field the bound of the level's state read on
    the entered graph at this moment. -/
noncomputable def record [DecidableEq Sym]
    (kinds : Kinds Sym) (graph : Graph Sym)
    (level : Level Sym) (wit : Sym) : Graph Sym :=
  let entered := enterall kinds graph level.terms
    kinds.record wit
  if haslevel graph level then graph
  else
    { edges := entered.edges
      levels := entered.levels ++ [level]
      log := entered.log ++
        [{ kind := kinds.record
           terms := bound entered level
           level := level.name
           witness := wit }] }

/-- Recording a level that already stands appends
    nothing. -/
theorem recordstands [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym)
    (h : haslevel graph level) :
    record kinds graph level wit = graph := by
  unfold record
  split
  · rfl
  · exact absurd h (by assumption)

/-- A fresh recording, unfolded: the entered graph's
    edges, the level appended to the levels, and the
    entry appended to the entered log. -/
theorem recordelse [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym)
    (h : ¬ haslevel graph level) :
    record kinds graph level wit =
      { edges := (enterall kinds graph level.terms
          kinds.record wit).edges
        levels := (enterall kinds graph level.terms
          kinds.record wit).levels ++ [level]
        log := (enterall kinds graph level.terms
          kinds.record wit).log ++
          [{ kind := kinds.record
             terms := bound (enterall kinds graph
               level.terms kinds.record wit) level
             level := level.name
             witness := wit }] } := by
  unfold record
  split
  · exact absurd (by assumption) h
  · rfl

/-- The excess change of recording is zero: recording
    enters terms, which changes no excess, and the entry
    itself carries no edges. -/
theorem recordexcess [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym) :
    excess (record kinds graph level wit) = excess graph := by
  by_cases h : haslevel graph level
  · rw [recordstands kinds graph level wit h]
  · have hrec := recordelse kinds graph level wit h
    have h3 : excess (record kinds graph level wit) =
        excess (enterall kinds graph level.terms
          kinds.record wit) := by
      simp only [hrec, excess]
    rw [h3]
    exact enterallexcess kinds level.terms kinds.record
      wit graph

/-- The entry a fresh recording appends, as a value:
    the record kind, the bound read on the entered graph
    at the recording moment, the level's name, and the
    witness. -/
def entryof [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym) :
    Entry Sym :=
  { kind := kinds.record
    terms := bound (enterall kinds graph level.terms
      kinds.record wit) level
    level := level.name
    witness := wit }

/-- Recording preserves validity, for a level whose
    terms are distinct and whose scope holds of each of
    its terms. -/
theorem recordvalid [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (level : Level Sym) (wit : Sym)
    (hnodup : level.terms.Nodup)
    (hscope : ∀ t ∈ level.terms, level.scope t = true) :
    Valid kinds (record kinds graph level wit) := by
  by_cases h : haslevel graph level
  · rw [recordstands kinds graph level wit h]
    exact valid
  · have hentered : Valid kinds (enterall kinds graph
        level.terms kinds.record wit) :=
      enterallvalid kinds level.terms kinds.record wit
        graph valid
    have hrec := recordelse kinds graph level wit h
    have hededges : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by
      simp only [hrec]
    have hedlevels : (record kinds graph level wit).levels =
        graph.levels ++ [level] := by
      simp only [hrec,
        enteralllevels kinds level.terms kinds.record wit
          graph]
    have hedlog : (record kinds graph level wit).log =
        (enterall kinds graph level.terms kinds.record
          wit).log ++ [entryof kinds graph level wit] := by
      simp only [hrec, entryof]
    have hkindall : ∀ e ∈ [entryof kinds graph level wit],
        e.kind ≠ kinds.join := by
      intro e he
      rw [List.mem_singleton] at he
      rw [he]
      exact Ne.symm kinds.distinct.2.2.2.1
    refine
      { nonempty := ?_
        nodup := ?_
        disjoint := ?_
        cnodup := ?_
        levels := ?_
        exactone := ?_
        exacttwo := ?_
        edgenodup := ?_ }
    · intro e he
      rw [hededges] at he
      exact hentered.nonempty e he
    · intro e he
      rw [hededges] at he
      exact hentered.nodup e he
    · intro e1 he1 e2 he2 t ht1 ht2
      rw [hededges] at he1 he2
      exact hentered.disjoint e1 he1 e2 he2 t ht1 ht2
    · intro e he
      rw [hededges] at he
      exact hentered.cnodup e he
    · intro l hl
      rw [hedlevels] at hl
      cases List.mem_append.mp hl with
      | inl hold =>
          obtain ⟨hnd, hrest⟩ := valid.levels l hold
          refine ⟨hnd, fun t ht => ?_⟩
          obtain ⟨hcol, hsc⟩ := hrest t ht
          obtain ⟨e, he, hte⟩ := hcol
          exact ⟨⟨e, hededges.symm ▸
            enteralledges kinds level.terms kinds.record
              wit graph e he, hte⟩, hsc⟩
      | inr hnew =>
          have hl2 : level = l :=
            (List.mem_singleton.mp hnew).symm
          subst hl2
          refine ⟨hnodup, fun t ht => ?_⟩
          obtain ⟨e, he, hte⟩ :=
            enterallcollected kinds level.terms
              kinds.record wit graph t ht
          exact ⟨⟨e, hededges ▸ he, hte⟩, hscope t ht⟩
    · intro x y hsame
      obtain ⟨e, he, hx, hy⟩ := hsame
      have hsame2 : same (enterall kinds graph level.terms
          kinds.record wit) x y :=
        ⟨e, hededges ▸ he, hx, hy⟩
      have hreach := hentered.exactone x y hsame2
      rw [hedlog]
      exact reachmono kinds hreach
    · intro x y hchain
      rw [hedlog] at hchain
      have hchain2 := chainappend kinds hkindall hchain
      have hsame := hentered.exacttwo x y hchain2
      obtain ⟨e, he, hx, hy⟩ := hsame
      exact ⟨e, hededges.symm ▸ he, hx, hy⟩
    · rw [hededges]
      exact hentered.edgenodup

/-- The entry a fresh recording appends: it stands in
    the new log with the record kind, the level's name,
    and terms equal to the bound read at its moment. -/
theorem recordentry [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym)
    (h : ¬ haslevel graph level) :
    ∃ e ∈ (record kinds graph level wit).log,
      e.kind = kinds.record ∧ e.level = level.name ∧
        e.terms = bound (enterall kinds graph level.terms
          kinds.record wit) level := by
  refine ⟨{ kind := kinds.record
            terms := bound (enterall kinds graph
              level.terms kinds.record wit) level
            level := level.name
            witness := wit }, ?_, rfl, rfl, rfl⟩
  have hrec := recordelse kinds graph level wit h
  have hedlog : (record kinds graph level wit).log =
      (enterall kinds graph level.terms kinds.record
        wit).log ++
        [{ kind := kinds.record
           terms := bound (enterall kinds graph
             level.terms kinds.record wit) level
           level := level.name
           witness := wit }] := by
    simp only [hrec]
  rw [hedlog]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The log of a merge step: the old log with the one
    join entry appended, in every case. -/
theorem mergelog [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Term Sym)
    (level wit : Sym) :
    (merge kinds graph one two level wit).log =
      graph.log ++ [⟨kinds.join, [one, two], level, wit⟩] := by
  cases h1 : seek graph.edges one with
  | none => simp only [merge, h1]
  | some ea =>
      cases h2 : seek graph.edges two with
      | none => simp only [merge, h1, h2]
      | some eb =>
          by_cases hee : ea = eb
          · simp only [merge, h1, h2, hee, ↓reduceIte]
          · simp only [merge, h1, h2, hee, ↓reduceIte]

/-- The levels of a merge step stand. -/
theorem mergelevels [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (one two : Term Sym)
    (level wit : Sym) :
    (merge kinds graph one two level wit).levels =
      graph.levels := by
  cases h1 : seek graph.edges one with
  | none => simp only [merge, h1]
  | some ea =>
      cases h2 : seek graph.edges two with
      | none => simp only [merge, h1, h2]
      | some eb =>
          by_cases hee : ea = eb
          · simp only [merge, h1, h2, hee, ↓reduceIte]
          · simp only [merge, h1, h2, hee, ↓reduceIte]

/-- Edge transfer across a merge step: an old edge's
    terms and colors all stand together on one edge of
    the merged graph — the merged edge when the old edge
    is one of the two merged, and the old edge itself
    otherwise. -/
theorem mergeedges [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym)
    (edge : Edge Sym) (hedge : edge ∈ graph.edges)
    (x y : Term Sym) (hx : x ∈ edge.terms)
    (hy : y ∈ edge.terms) :
    ∃ e' ∈ (merge kinds graph one two level wit).edges,
      x ∈ e'.terms ∧ y ∈ e'.terms ∧
        ∀ c ∈ edge.colors, c ∈ e'.colors := by
  by_cases hcol1 : collected graph one
  · by_cases hcol2 : collected graph two
    · obtain ⟨ea, ha, heain, haine⟩ :=
        seekof graph.edges one hcol1
      obtain ⟨eb, hb, hebin, hbine⟩ :=
        seekof graph.edges two hcol2
      by_cases hee : ea = eb
      · have h2 : (merge kinds graph one two level
            wit).edges = graph.edges := by
          simp only [merge, ha, hb, hee, ↓reduceIte]
        exact ⟨edge, h2 ▸ hedge, hx, hy, fun c hc => hc⟩
      · have h2 : (merge kinds graph one two level
            wit).edges = joinEdges graph.edges one two := by
          simp only [merge, ha, hb, hee, ↓reduceIte]
        have hje : joinEdges graph.edges one two =
            (graph.edges.filter (fun e =>
              decide (one ∉ e.terms) &&
                decide (two ∉ e.terms))) ++
              [merged ea eb] := by
          simp only [joinEdges, ha, hb]
        by_cases hone : one ∈ edge.terms
        · have heea : edge = ea :=
            valid.disjoint edge hedge ea heain one hone haine
          refine ⟨merged ea eb, ?_, ?_, ?_, ?_⟩
          · rw [h2, hje]
            exact List.mem_append_right _ (by simp)
          · rw [heea] at hx
            exact List.mem_append_left _ hx
          · rw [heea] at hy
            exact List.mem_append_left _ hy
          · intro c hc
            rw [heea] at hc
            exact (memunion ea.colors eb.colors c).mpr
              (Or.inl hc)
        · by_cases htwo : two ∈ edge.terms
          · have heeb : edge = eb :=
              valid.disjoint edge hedge eb hebin two htwo
                hbine
            refine ⟨merged ea eb, ?_, ?_, ?_, ?_⟩
            · rw [h2, hje]
              exact List.mem_append_right _ (by simp)
            · rw [heeb] at hx
              exact List.mem_append_right _ hx
            · rw [heeb] at hy
              exact List.mem_append_right _ hy
            · intro c hc
              rw [heeb] at hc
              exact (memunion ea.colors eb.colors c).mpr
                (Or.inr hc)
          · refine ⟨edge, ?_, hx, hy, fun c hc => hc⟩
            rw [h2, hje]
            apply List.mem_append_left
            rw [List.mem_filter]
            exact ⟨hedge, by simp [hone, htwo]⟩
    · have hseek : seek graph.edges two = none := by
        by_cases hs : seek graph.edges two = none
        · exact hs
        · cases hso : seek graph.edges two with
          | none => rfl
          | some found =>
              obtain ⟨hfin, hfterm⟩ :=
                seeksome graph.edges two found hso
              exact absurd ⟨found, hfin, hfterm⟩ hcol2
      have h2 : (merge kinds graph one two level
          wit).edges = graph.edges := by
        simp only [merge, hseek]
        cases seek graph.edges one <;> rfl
      exact ⟨edge, h2 ▸ hedge, hx, hy, fun c hc => hc⟩
  · have hseek : seek graph.edges one = none := by
      by_cases hs : seek graph.edges one = none
      · exact hs
      · cases hso : seek graph.edges one with
        | none => rfl
        | some found =>
            obtain ⟨hfin, hfterm⟩ :=
              seeksome graph.edges one found hso
            exact absurd ⟨found, hfin, hfterm⟩ hcol1
    have h2 : (merge kinds graph one two level wit).edges =
        graph.edges := by
      simp only [merge, hseek]
    exact ⟨edge, h2 ▸ hedge, hx, hy, fun c hc => hc⟩

/- ## The growth relation

    One graph grows to another when the second graph's
    log has the first's as a prefix, the first's levels
    stand, every collected term stays collected, every
    equivalence stands, and every color of an old edge
    stands on the new edge holding the term. Section 8's
    drift exclusion is the statement that the four
    operations are the only steps, taken up by the run
    theorems below: every run of operations grows. -/

/-- The growth relation of section 8. -/
structure Growth (kinds : Kinds Sym) (g h : Graph Sym) :
    Prop where
  logpre : ∃ rest, h.log = g.log ++ rest
  levels : ∀ l ∈ g.levels, l ∈ h.levels
  collected : ∀ t, collected g t → collected h t
  same : ∀ x y, same g x y → same h x y
  colors : ∀ (edge : Edge Sym), edge ∈ g.edges →
    ∀ t ∈ edge.terms, ∃ e' ∈ h.edges, t ∈ e'.terms ∧
      ∀ c ∈ edge.colors, c ∈ e'.colors

/-- Growth is reflexive. -/
theorem growthrefl [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) : Growth kinds graph graph :=
  { logpre := ⟨[], by simp⟩
    levels := fun l hl => hl
    collected := fun t h => h
    same := fun x y h => h
    colors := fun edge hedge t ht =>
      ⟨edge, hedge, ht, fun c hc => hc⟩ }

/-- Growth is transitive. -/
theorem growthtrans [DecidableEq Sym] (kinds : Kinds Sym)
    {g h i : Graph Sym} (first : Growth kinds g h)
    (second : Growth kinds h i) : Growth kinds g i :=
  { logpre := by
      obtain ⟨r1, hr1⟩ := first.logpre
      obtain ⟨r2, hr2⟩ := second.logpre
      exact ⟨r1 ++ r2, by rw [hr2, hr1, List.append_assoc]⟩
    levels := fun l hl => second.levels l (first.levels l hl)
    collected := fun t ht =>
      second.collected t (first.collected t ht)
    same := fun x y hxy => second.same x y (first.same x y hxy)
    colors := by
      intro edge hedge t ht
      obtain ⟨e1, he1, ht1, hc1⟩ := first.colors edge hedge t ht
      obtain ⟨e2, he2, ht2, hc2⟩ := second.colors e1 he1 t ht1
      exact ⟨e2, he2, ht2, fun c hc => hc2 c (hc1 c hc)⟩ }

/-- Entering grows the graph. -/
theorem entergrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (level wit : Sym) :
    Growth kinds graph (enter kinds graph term level wit) :=
  { logpre := ⟨[⟨kinds.enter, [term], level, wit⟩],
      enterlog kinds graph term level wit⟩
    levels := by
      rw [enterlevels]
      exact fun l hl => hl
    collected := fun t h =>
      (entercollected kinds graph term level wit t).mpr
        (Or.inl h)
    same := fun x y h =>
      (entersame kinds graph term level wit x y).mpr
        (Or.inl h)
    colors := by
      intro edge hedge t ht
      by_cases hs : seek graph.edges term = none
      · have h2 : (enter kinds graph term level wit).edges =
            graph.edges ++ [{ terms := [term], colors := [] }] := by
          simp only [enter, hs]
        exact ⟨edge, h2 ▸ List.mem_append_left _ hedge, ht,
          fun c hc => hc⟩
      · have h2 : (enter kinds graph term level wit).edges =
            graph.edges := by
          cases hso : seek graph.edges term with
          | none => exact absurd hso hs
          | some found => simp only [enter, hso]
        exact ⟨edge, h2 ▸ hedge, ht, fun c hc => hc⟩ }

/-- Painting grows the graph. -/
theorem paintgrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (term : Term Sym) (color : Color Sym)
    (level wit : Sym) :
    Growth kinds graph (paint kinds graph term color
      level wit) :=
  { logpre := ⟨[⟨kinds.paint, [term], level, wit⟩], rfl⟩
    levels := fun l hl => hl
    collected := fun t h =>
      (paintcollected kinds graph term color level wit
        t).mpr h
    same := fun x y h =>
      (paintsame kinds graph term color level wit x y).mpr h
    colors := by
      intro edge hedge t ht
      obtain ⟨new, hnew, hterms, hcolors⟩ :=
        paintedgescover graph.edges term color edge hedge
      exact ⟨new, hnew, hterms ▸ ht, hcolors⟩ }

/-- Recording grows the graph. -/
theorem recordgrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (level : Level Sym) (wit : Sym) :
    Growth kinds graph (record kinds graph level wit) := by
  by_cases h : haslevel graph level
  · rw [recordstands kinds graph level wit h]
    exact growthrefl kinds graph
  · have hrec := recordelse kinds graph level wit h
    have hededges : (record kinds graph level wit).edges =
        (enterall kinds graph level.terms kinds.record
          wit).edges := by
      simp only [hrec]
    have hedlevels : (record kinds graph level wit).levels =
        graph.levels ++ [level] := by
      simp only [hrec,
        enteralllevels kinds level.terms kinds.record wit
          graph]
    have hedlog : (record kinds graph level wit).log =
        (enterall kinds graph level.terms kinds.record
          wit).log ++ [entryof kinds graph level wit] := by
      simp only [hrec, entryof]
    refine
      { logpre := ?_
        levels := ?_
        collected := ?_
        same := ?_
        colors := ?_ }
    · refine ⟨level.terms.map (fun t =>
        (⟨kinds.enter, [t], kinds.record, wit⟩ :
          Entry Sym)) ++
        [entryof kinds graph level wit], ?_⟩
      rw [hedlog, enteralllog]
      simp [List.append_assoc]
    · intro l hl
      rw [hedlevels]
      exact List.mem_append_left _ hl
    · intro t hcol
      obtain ⟨e, he, hte⟩ := hcol
      exact ⟨e, hededges ▸ enteralledges kinds level.terms
        kinds.record wit graph e he, hte⟩
    · intro x y hxy
      obtain ⟨e, he, hx, hy⟩ :=
        (enterallsame kinds level.terms kinds.record wit
          graph x y).mpr (Or.inl hxy)
      exact ⟨e, hededges ▸ he, hx, hy⟩
    · intro edge hedge t ht
      exact ⟨edge, hededges ▸ enteralledges kinds
        level.terms kinds.record wit graph edge hedge, ht,
        fun c hc => hc⟩

/-- A merge step grows the graph, on a valid graph. -/
theorem mergegrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    Growth kinds graph (merge kinds graph one two
      level wit) :=
  { logpre := ⟨[⟨kinds.join, [one, two], level, wit⟩],
      mergelog kinds graph one two level wit⟩
    levels := by
      rw [mergelevels]
      exact fun l hl => hl
    collected := by
      intro t hcol
      obtain ⟨e, he, hte⟩ := hcol
      obtain ⟨e', he', hte', -, -⟩ := mergeedges kinds graph
        valid one two level wit e he t t hte hte
      exact ⟨e', he', hte'⟩
    same := by
      intro x y hxy
      obtain ⟨e, he, hx, hy⟩ := hxy
      obtain ⟨e', he', hx', hy', -⟩ := mergeedges kinds
        graph valid one two level wit e he x y hx hy
      exact ⟨e', he', hx', hy'⟩
    colors := by
      intro edge hedge t ht
      obtain ⟨e', he', ht', -, hc'⟩ := mergeedges kinds
        graph valid one two level wit edge hedge t t ht ht
      exact ⟨e', he', ht', hc'⟩ }

/-- The join operation grows the graph, on a valid
    graph. -/
theorem joingrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (one two : Term Sym) (level wit : Sym) :
    Growth kinds graph (join kinds graph one two
      level wit) := by
  have hv1 := entervalid kinds graph valid one level wit
  have hv2 := entervalid kinds _ hv1 two level wit
  exact growthtrans kinds
    (entergrows kinds graph one level wit)
    (growthtrans kinds
      (entergrows kinds (enter kinds graph one level wit)
        two level wit)
      (mergegrows kinds _ hv2 one two level wit))

/- ## Operations and runs

    An operation is one of the four of section 8, as
    data. A run is a list of operations folded over a
    graph. The joins of a run are its effective joins:
    the join operations whose merge step merges, counted
    at their moments. A run is ready when it starts on a
    valid graph and every record step in it records a
    level whose terms are distinct and in scope — the
    standing hypotheses of the record operation, carried
    along the run. -/

/-- One of the four operations of section 8, as data. -/
inductive Op (Sym : Type) where
  | enter (term : Term Sym) (level wit : Sym)
  | join (one two : Term Sym) (level wit : Sym)
  | record (level : Level Sym) (wit : Sym)
  | paint (term : Term Sym) (color : Color Sym)
      (level wit : Sym)

/-- Applying one operation to a graph. -/
noncomputable def apply [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (op : Op Sym) : Graph Sym :=
  match op with
  | .enter t l w => enter kinds graph t l w
  | .join a b l w => join kinds graph a b l w
  | .record lv w => record kinds graph lv w
  | .paint t c l w => paint kinds graph t c l w

/-- A run of operations, folded from the left. -/
noncomputable def run [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (ops : List (Op Sym)) : Graph Sym :=
  ops.foldl (apply kinds) graph

/-- A run splits over an appended list of operations. -/
theorem runappend [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (first second : List (Op Sym)) :
    run kinds graph (first ++ second) =
      run kinds (run kinds graph first) second :=
  List.foldl_append

/-- One step of a run: running an operation and then
    the rest is running the rest from the applied
    graph. -/
theorem runcons [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (op : Op Sym)
    (rest : List (Op Sym)) :
    run kinds graph (op :: rest) =
      run kinds (apply kinds graph op) rest := rfl

/-- The effective joins of a run: each join operation
    counts its effective join count at its moment, and
    the other operations count nothing. -/
noncomputable def joins [DecidableEq Sym] (kinds : Kinds Sym) :
    Graph Sym → List (Op Sym) → Nat
  | _, [] => 0
  | g, .enter t l w :: rest =>
      joins kinds (enter kinds g t l w) rest
  | g, .join a b l w :: rest =>
      eff kinds g a b l w + joins kinds (join kinds g a b l w) rest
  | g, .record lv w :: rest =>
      joins kinds (record kinds g lv w) rest
  | g, .paint t c l w :: rest =>
      joins kinds (paint kinds g t c l w) rest

/-- The effective joins of a run split over an appended
    list: the joins of the first part, plus the joins of
    the second part counted from the graph the first
    part reaches. -/
theorem joinsappend [DecidableEq Sym] (kinds : Kinds Sym) :
    ∀ (graph : Graph Sym) (first second : List (Op Sym)),
      joins kinds graph (first ++ second) =
        joins kinds graph first +
          joins kinds (run kinds graph first) second := by
  intro graph first
  induction first generalizing graph with
  | nil =>
      intro second
      simp only [List.nil_append, joins, run, List.foldl_nil,
        Nat.zero_add]
  | cons op rest ih =>
      intro second
      cases op with
      | enter t l w =>
          have h1 : joins kinds graph
              ((Op.enter t l w :: rest) ++ second) =
              joins kinds (enter kinds graph t l w)
                (rest ++ second) := rfl
          rw [h1, ih, run]
          rfl
      | join a b l w =>
          have h1 : joins kinds graph
              ((Op.join a b l w :: rest) ++ second) =
              eff kinds graph a b l w +
                joins kinds (join kinds graph a b l w)
                  (rest ++ second) := rfl
          rw [h1, ih]
          have h2 : run kinds graph
              (Op.join a b l w :: rest) =
              run kinds (join kinds graph a b l w) rest := rfl
          have h3 : joins kinds graph
              (Op.join a b l w :: rest) =
              eff kinds graph a b l w +
                joins kinds (join kinds graph a b l w)
                  rest := rfl
          rw [h2, h3, Nat.add_assoc]
      | record lv w =>
          have h1 : joins kinds graph
              ((Op.record lv w :: rest) ++ second) =
              joins kinds (record kinds graph lv w)
                (rest ++ second) := rfl
          rw [h1, ih, run]
          rfl
      | paint t c l w =>
          have h1 : joins kinds graph
              ((Op.paint t c l w :: rest) ++ second) =
              joins kinds (paint kinds graph t c l w)
                (rest ++ second) := rfl
          rw [h1, ih, run]
          rfl

/-- A ready run: a valid start, and every record step
    recording a level whose terms are distinct and in
    its scope, at its moment. -/
inductive Ready (kinds : Kinds Sym) [DecidableEq Sym] :
    Graph Sym → List (Op Sym) → Prop where
  | done {graph : Graph Sym} (valid : Valid kinds graph) :
      Ready kinds graph []
  | more {graph : Graph Sym} (valid : Valid kinds graph)
      (op : Op Sym)
      (step : match op with
        | .record level _ => level.terms.Nodup ∧
            ∀ t ∈ level.terms, level.scope t = true
        | _ => True)
      {rest : List (Op Sym)}
      (tail : Ready kinds (apply kinds graph op) rest) :
      Ready kinds graph (op :: rest)

/-- A ready run starts on a valid graph. -/
theorem readystart [DecidableEq Sym] (kinds : Kinds Sym)
    {graph : Graph Sym} {ops : List (Op Sym)}
    (ready : Ready kinds graph ops) : Valid kinds graph := by
  cases ready with
  | done valid => exact valid
  | more valid _ _ _ => exact valid

/-- One operation grows its graph, on a valid graph. -/
theorem opgrows [DecidableEq Sym] (kinds : Kinds Sym)
    (graph : Graph Sym) (valid : Valid kinds graph)
    (op : Op Sym) :
    Growth kinds graph (apply kinds graph op) := by
  cases op with
  | enter t l w => exact entergrows kinds graph t l w
  | join a b l w => exact joingrows kinds graph valid a b l w
  | record lv w => exact recordgrows kinds graph lv w
  | paint t c l w => exact paintgrows kinds graph t c l w

/-- Every ready run ends on a valid graph. -/
theorem runvalid [DecidableEq Sym] (kinds : Kinds Sym)
    {graph : Graph Sym} {ops : List (Op Sym)}
    (ready : Ready kinds graph ops) :
    Valid kinds (run kinds graph ops) := by
  induction ready with
  | done valid => exact valid
  | more valid op step tail ih =>
      rw [runcons]
      exact ih

/-- Every ready run grows its graph. -/
theorem rungrows [DecidableEq Sym] (kinds : Kinds Sym)
    {graph : Graph Sym} {ops : List (Op Sym)}
    (ready : Ready kinds graph ops) :
    Growth kinds graph (run kinds graph ops) := by
  induction ready with
  | done valid => exact growthrefl kinds _
  | more valid op step tail ih =>
      rw [runcons]
      exact growthtrans kinds
        (opgrows kinds _ valid op) ih

/-- The excess theorem of a run: the excess after a
    ready run is the excess before it plus the run's
    effective joins. Each operation's excess change is
    its effective join count — zero for enter, record,
    and paint, and the merge count for join — so the
    total is the accumulation of the effective joins at
    their moments. -/
theorem runexcess [DecidableEq Sym] (kinds : Kinds Sym)
    {graph : Graph Sym} {ops : List (Op Sym)}
    (ready : Ready kinds graph ops) :
    excess (run kinds graph ops) =
      excess graph + joins kinds graph ops := by
  induction ops generalizing graph with
  | nil =>
      cases ready with
      | done valid => rfl
  | cons op rest ih =>
      cases ready with
      | more valid opf step tail =>
          rw [runcons, ih tail]
          cases op with
          | enter t l w =>
              have h1 : joins kinds graph
                  (Op.enter t l w :: rest) =
                  joins kinds (apply kinds graph
                    (Op.enter t l w)) rest := rfl
              have h2 : excess (apply kinds graph
                  (Op.enter t l w)) = excess graph :=
                enterexcess kinds graph t l w
              rw [h1, h2]
          | join a b l w =>
              have h1 : joins kinds graph
                  (Op.join a b l w :: rest) =
                  eff kinds graph a b l w +
                    joins kinds (apply kinds graph
                      (Op.join a b l w)) rest := rfl
              have h2 : excess (apply kinds graph
                  (Op.join a b l w)) =
                  excess graph + eff kinds graph a b l w :=
                joinexcess kinds graph valid a b l w
              rw [h1, h2, Nat.add_assoc]
          | record lv w =>
              have h1 : joins kinds graph
                  (Op.record lv w :: rest) =
                  joins kinds (apply kinds graph
                    (Op.record lv w)) rest := rfl
              have h2 : excess (apply kinds graph
                  (Op.record lv w)) = excess graph :=
                recordexcess kinds graph lv w
              rw [h1, h2]
          | paint t c l w =>
              have h1 : joins kinds graph
                  (Op.paint t c l w :: rest) =
                  joins kinds (apply kinds graph
                    (Op.paint t c l w)) rest := rfl
              have h2 : excess (apply kinds graph
                  (Op.paint t c l w)) = excess graph :=
                paintexcess kinds graph t c l w
              rw [h1, h2]
