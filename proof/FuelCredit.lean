import SearchBoundary

namespace Behavior.SearchBoundary

structure Account (ceiling : Nat) where
  spent : Nat
  available : Nat
  reserve : Nat
  conserved : spent + available + reserve ≤ ceiling

def Account.pay {ceiling : Nat} (a : Account ceiling) : Option (Account ceiling) :=
  match h : a.available with
  | 0 => none
  | n + 1 =>
    some ⟨a.spent + 1, n, a.reserve, by
      have hc := a.conserved
      omega⟩

def Account.credit {ceiling : Nat} (a : Account ceiling) (requested : Nat) :
    Account ceiling :=
  let r := min requested a.reserve
  ⟨a.spent, a.available + r, a.reserve - r, by
    have hc := a.conserved
    have hr : r ≤ a.reserve := Nat.min_le_right _ _
    omega⟩

theorem lifetime {ceiling : Nat} (a : Account ceiling) : a.spent ≤ ceiling := by
  have hc := a.conserved
  omega

theorem creditSpendsNothing {ceiling : Nat} (a : Account ceiling) (requested : Nat) :
    (a.credit requested).spent = a.spent := rfl

theorem paySpent {ceiling : Nat} {a b : Account ceiling} (paid : a.pay = some b) :
    b.spent = a.spent + 1 := by
  unfold Account.pay at paid
  split at paid
  · contradiction
  · exact congrArg Account.spent (Option.some.inj paid).symm

theorem noMint {ceiling : Nat} (a : Account ceiling) (n : Nat) :
    (a.credit n).available + (a.credit n).reserve = a.available + a.reserve := by
  change a.available + min n a.reserve + (a.reserve - min n a.reserve) =
    a.available + a.reserve
  have h := Nat.min_le_right n a.reserve
  omega

#print axioms lifetime
#print axioms creditSpendsNothing
#print axioms paySpent
#print axioms noMint
end Behavior.SearchBoundary
