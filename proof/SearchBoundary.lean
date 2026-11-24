import Binding

namespace Behavior.SearchBoundary

structure Qualified {S A O : Type} (m : Machine S A O) (root : S) where
  state : S
  correct : Same m root state

def candidate {S A O : Type} {m : Machine S A O} {root : S}
    (old : Qualified m root) {target : S} (step : Same m old.state target) :
    Qualified m root :=
  ⟨target, fun acts obs => (old.correct acts obs).trans (step acts obs)⟩

inductive Progress {S A O Axis : Type} {m : Machine S A O} {root : S}
    (cost : S → Axis → Nat) :
    Qualified m root → Qualified m root → Prop where
  | stay (now) : Progress cost now now
  | lower (now next) : (∀ i, cost next.state i ≤ cost now.state i) →
      Progress cost now next

theorem nonworsening {S A O Axis : Type} {m : Machine S A O} {root : S}
    {cost : S → Axis → Nat} {old new : Qualified m root}
    (step : Progress cost old new) (i : Axis) :
    cost new.state i ≤ cost old.state i := by
  cases step with
  | stay => exact Nat.le_refl _
  | lower _ law => exact law i

inductive History {S A O Axis : Type} {m : Machine S A O} {root : S}
    (cost : S → Axis → Nat) :
    Qualified m root → Qualified m root → Prop where
  | begin (now) : History cost now now
  | append : History cost old prior → Progress cost prior next → History cost old next

theorem historyNonworsening {S A O Axis : Type} {m : Machine S A O} {root : S}
    {cost : S → Axis → Nat} {old new : Qualified m root}
    (h : History cost old new) (i : Axis) : cost new.state i ≤ cost old.state i := by
  induction h with
  | begin => exact Nat.le_refl _
  | append _ tail ih => exact Nat.le_trans (nonworsening tail i) ih

def bounded {State : Type} (step : State → Option State) : Nat → State → State × Nat
  | 0, state => (state, 0)
  | fuel + 1, state =>
    match step state with
    | none => (state, 1)
    | some rest =>
      let (last, ticks) := bounded step fuel rest
      (last, ticks + 1)

theorem boundedTicks {State : Type} (step : State → Option State) (fuel : Nat) (initial : State) :
    (bounded step fuel initial).2 ≤ fuel := by
  induction fuel generalizing initial with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold bounded
    split
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · rename_i rest h
      simpa using Nat.succ_le_succ (ih rest)

theorem boundedSound {S A O : Type} {m : Machine S A O} {root : S}
    (step : Qualified m root → Option (Qualified m root)) (fuel : Nat)
    (initial : Qualified m root) : Same m root (bounded step fuel initial).1.state :=
  (bounded step fuel initial).1.correct

theorem boundedProgress {S A O Axis : Type} {m : Machine S A O} {root : S}
    (cost : S → Axis → Nat)
    (step : Qualified m root → Option (Qualified m root))
    (localProgress : ∀ old next, step old = some next → Progress cost old next)
    (fuel : Nat) (initial : Qualified m root) (i : Axis) :
    cost (bounded step fuel initial).1.state i ≤ cost initial.state i := by
  induction fuel generalizing initial with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold bounded
    split
    · exact Nat.le_refl _
    · rename_i next h
      exact Nat.le_trans (ih next) (nonworsening (localProgress initial next h) i)

#print axioms boundedProgress
#print axioms candidate
#print axioms nonworsening
#print axioms historyNonworsening
#print axioms boundedTicks
#print axioms boundedSound
end Behavior.SearchBoundary
