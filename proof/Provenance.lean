import FuelCredit

namespace Behavior.SearchBoundary

def Ordered {N : Type} (depth : N → Nat) (premise : N → N → Prop) : Prop :=
  ∀ child parent, premise child parent → depth parent < depth child

inductive ProvenancePath {N : Type} (premise : N → N → Prop) : N → N → Prop where
  | single : premise node dependency → ProvenancePath premise node dependency
  | extend : premise node dependency → ProvenancePath premise dependency ancestor →
      ProvenancePath premise node ancestor

theorem pathDecreases {N : Type} {depth : N → Nat} {premise : N → N → Prop}
    (ordered : Ordered depth premise) {x y : N} (path : ProvenancePath premise x y) :
    depth y < depth x := by
  induction path with
  | single edge => exact ordered _ _ edge
  | extend edge _ ih => exact Nat.lt_trans ih (ordered _ _ edge)

theorem noCycle {N : Type} {depth : N → Nat} {premise : N → N → Prop}
    (ordered : Ordered depth premise) (x : N) : ¬ ProvenancePath premise x x :=
  fun path => Nat.lt_irrefl _ (pathDecreases ordered path)

theorem shorten {N : Type} [DecidableEq N] {depth : N → Nat} {premise : N → N → Prop}
    (ordered : Ordered depth premise) (node : N) (newDepth : Nat)
    (lowers : newDepth ≤ depth node) (parents : N → Prop)
    (localProof : ∀ p, parents p → p ≠ node ∧ depth p < newDepth) :
    Ordered (fun x => if x = node then newDepth else depth x)
      (fun x p => if x = node then parents p else premise x p) := by
  intro child parent edge
  by_cases h : child = node
  · obtain ⟨ne, lt⟩ := localProof parent (by simpa [h] using edge)
    simpa [h, ne] using lt
  · have lt := ordered _ _ (by simpa [h] using edge)
    by_cases p : parent = node
    · subst parent
      simpa [h] using Nat.lt_of_le_of_lt lowers lt
    · simpa [h, p] using lt

#print axioms pathDecreases
#print axioms noCycle
#print axioms shorten
end Behavior.SearchBoundary
