import Behavior

namespace Behavior

/-- Evidence is reusable; the authority-bearing claim includes its scope. -/
structure Binding (Scope Evidence : Type) where
  scope : Scope
  evidence : Evidence
  deriving DecidableEq

def bound {Scope Evidence : Type} [DecidableEq Scope] [DecidableEq Evidence]
    (expected loaded : Binding Scope Evidence) : Bool :=
  decide (expected = loaded)

theorem boundexact {Scope Evidence : Type} [DecidableEq Scope] [DecidableEq Evidence]
    (expected loaded : Binding Scope Evidence) :
    bound expected loaded = true ↔ expected = loaded := by simp [bound]

theorem differentScope {Scope Evidence : Type} [DecidableEq Scope] [DecidableEq Evidence]
    {expected loaded : Binding Scope Evidence} (different : expected.scope ≠ loaded.scope) :
    bound expected loaded = false := by
  cases h : bound expected loaded
  · rfl
  · exact (different (congrArg Binding.scope ((boundexact _ _).mp h))).elim

def BoundLog {Scope Evidence Record : Type}
    (binding : Binding Scope Evidence) (log : List (Binding Scope Evidence × Record)) : Prop :=
  ∀ entry ∈ log, entry.1 = binding

theorem extendBound {Scope Evidence Record : Type} [DecidableEq Scope] [DecidableEq Evidence]
    {binding loaded : Binding Scope Evidence} {log : List (Binding Scope Evidence × Record)}
    (old : BoundLog binding log) (matched : bound binding loaded = true) (entry : Record) :
    BoundLog binding (log ++ [(loaded, entry)]) := by
  intro candidate h
  rcases List.mem_append.mp h with h | h
  · exact old candidate h
  · have eq := List.mem_singleton.mp h
    exact (congrArg Prod.fst eq).trans ((boundexact _ _).mp matched).symm

def sync {S C A O : Type} (m : Machine S A O) (env : O → C → A → C → Prop) :
    Machine (S × C) A (O × C) :=
  ⟨fun p => (m.observe p.1, p.2), fun p a q =>
    m.move p.1 a q.1 ∧ env (m.observe p.1) p.2 a q.2⟩

theorem syncbisim {S C A O : Type} {m : Machine S A O} {rel : S → S → Prop}
    (law : Bisim m rel) (env : O → C → A → C → Prop) :
    Bisim (sync m env) (fun x y => rel x.1 y.1 ∧ x.2 = y.2) := by
  intro x y h
  obtain ⟨obs, moveLeft, moveRight⟩ := law _ _ h.1
  refine ⟨Prod.ext obs h.2, ?_, ?_⟩
  · intro a x' step
    obtain ⟨y', move, linked⟩ := moveLeft a x'.1 step.1
    exact ⟨(y', x'.2), ⟨move, by rw [← obs, ← h.2]; exact step.2⟩, linked, rfl⟩
  · intro a y' step
    obtain ⟨x', move, linked⟩ := moveRight a y'.1 step.1
    exact ⟨(x', y'.2), ⟨move, by rw [obs, h.2]; exact step.2⟩, linked, rfl⟩

theorem scopedTableJoin {Sym S A O C Scope Evidence : Type}
    [DecidableEq Sym] [DecidableEq O] [DecidableEq Scope] [DecidableEq Evidence]
    {table : Table S A O} {read : Term Sym → S}
    {states : List S} {actions : List A} {key : S → Nat}
    (statecover : ∀ x, x ∈ states) (actioncover : ∀ a, a ∈ actions)
    (passed : verify table states actions key = true)
    {expected loaded : Binding Scope Evidence}
    (matched : bound expected loaded = true)
    {kinds : Kinds Sym} {graph : Graph Sym}
    (valid : Valid kinds graph)
    (checked : Checks table.machine read kinds graph.log)
    {x y : Term Sym} {level witness : Sym} (equals : key (read x) = key (read y))
    {left right : Term Sym}
    (linked : same (join kinds graph x y level witness) left right)
    (env : O → C → A → C → Prop) (context : C) :
    loaded = expected ∧ Same (sync table.machine env) (read left, context) (read right, context) := by
  refine ⟨((boundexact _ _).mp matched).symm, ?_⟩
  exact substitute (syncbisim (coarsest table) env)
    ⟨tablejoin statecover actioncover passed valid checked equals linked, rfl⟩

#print axioms scopedTableJoin
#print axioms boundexact
#print axioms differentScope
#print axioms extendBound
#print axioms syncbisim
end Behavior
