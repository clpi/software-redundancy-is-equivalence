import Ops

namespace Behavior

structure Machine (S A O : Type) where
  observe : S → O
  move : S → A → S → Prop

inductive Walk {S A O : Type} (machine : Machine S A O) :
    S → List A → List O → Prop where
  | stop : Walk machine state [] [machine.observe state]
  | next : machine.move state action target →
      Walk machine target actions observations →
      Walk machine state (action :: actions) (machine.observe state :: observations)

def Bisim {S A O : Type} (machine : Machine S A O) (rel : S → S → Prop) : Prop :=
  ∀ x y, rel x y →
    machine.observe x = machine.observe y ∧
    (∀ a x', machine.move x a x' → ∃ y', machine.move y a y' ∧ rel x' y') ∧
    (∀ a y', machine.move y a y' → ∃ x', machine.move x a x' ∧ rel x' y')

theorem forward {S A O : Type} {machine : Machine S A O} {rel : S → S → Prop}
    (law : Bisim machine rel) {x y : S} (related : rel x y)
    {actions : List A} {observations : List O}
    (witness : Walk machine x actions observations) :
    Walk machine y actions observations := by
  induction witness generalizing y with
  | @stop x =>
    have h := (law x y related).1
    rw [h]
    exact .stop
  | @next x a x' actions observations step _ ih =>
    have h := law x y related
    obtain ⟨y', step', linked⟩ := h.2.1 a x' step
    rw [h.1]
    exact .next step' (ih linked)

theorem flip {S A O : Type} {machine : Machine S A O} {rel : S → S → Prop}
    (law : Bisim machine rel) : Bisim machine (fun x y => rel y x) := by
  intro x y h
  have h := law y x h
  exact ⟨h.1.symm, h.2.2, h.2.1⟩

def Same {S A O : Type} (machine : Machine S A O) (x y : S) : Prop :=
  ∀ actions observations, Walk machine x actions observations ↔
    Walk machine y actions observations

theorem substitute {S A O : Type} {machine : Machine S A O} {rel : S → S → Prop}
    (law : Bisim machine rel) {x y : S} (h : rel x y) : Same machine x y := by
  intro actions observations
  exact ⟨forward law h, forward (flip law) h⟩

def Checks {Sym S A O : Type} (machine : Machine S A O) (read : Term Sym → S)
    (kinds : Kinds Sym) (log : List (Entry Sym)) : Prop :=
  ∀ entry ∈ log, entry.kind = kinds.join →
    ∀ left ∈ entry.terms, ∀ right ∈ entry.terms, Same machine (read left) (read right)

theorem chain {Sym S A O : Type} {machine : Machine S A O} {read : Term Sym → S}
    {kinds : Kinds Sym} {log : List (Entry Sym)}
    (checked : Checks machine read kinds log) {x y : Term Sym}
    (linked : Chain kinds log x y) : Same machine (read x) (read y) := by
  induction linked with
  | @step x y h =>
    obtain ⟨entry, member, kind, left, right⟩ := h
    exact checked entry member kind x left y right
  | trans _ _ left right =>
    intro actions observations
    exact (left actions observations).trans (right actions observations)

theorem sound {Sym S A O : Type} {machine : Machine S A O} {read : Term Sym → S}
    {kinds : Kinds Sym} {graph : Graph Sym}
    (valid : Valid kinds graph) (checked : Checks machine read kinds graph.log)
    {x y : Term Sym} (linked : same graph x y) : Same machine (read x) (read y) := by
  cases valid.exactone x y linked with
  | inl equal => subst y; intro _ _; exact Iff.rfl
  | inr path => exact chain checked path

theorem checkedappend {Sym S A O : Type} {machine : Machine S A O} {read : Term Sym → S}
    {kinds : Kinds Sym} {old fresh : List (Entry Sym)}
    (first : Checks machine read kinds old) (next : Checks machine read kinds fresh) :
    Checks machine read kinds (old ++ fresh) := by
  intro entry member kind
  cases List.mem_append.mp member with
  | inl previous => exact first entry previous kind
  | inr appended => exact next entry appended kind

theorem checkedjoin {Sym S A O : Type} [DecidableEq Sym]
    {machine : Machine S A O} {read : Term Sym → S} {graph : Graph Sym}
    (kinds : Kinds Sym) (x y : Term Sym) (level witness : Sym)
    (checked : Checks machine read kinds graph.log)
    (accepted : Same machine (read x) (read y)) :
    Checks machine read kinds (join kinds graph x y level witness).log := by
  unfold join
  rw [mergelog, enterlog, enterlog]
  intro entry member kind a am b bm
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with ((old | entered) | entered) | appended
  · exact checked entry old kind a am b bm
  · rw [entered] at kind
    exact (kinds.distinct.1 kind).elim
  · rw [entered] at kind
    exact (kinds.distinct.1 kind).elim
  · rw [appended] at am bm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at am bm
    rcases am with rfl | rfl <;> rcases bm with rfl | rfl
    · intro _ _; exact Iff.rfl
    · exact accepted
    · intro actions observations; exact (accepted actions observations).symm
    · intro _ _; exact Iff.rfl

theorem joinsubstitute {Sym S A O : Type} [DecidableEq Sym]
    {machine : Machine S A O} {read : Term Sym → S} {graph : Graph Sym}
    {kinds : Kinds Sym}
    (valid : Valid kinds graph) (checked : Checks machine read kinds graph.log)
    {x y : Term Sym} {level witness : Sym}
    (accepted : Same machine (read x) (read y)) {left right : Term Sym}
    (linked : same (join kinds graph x y level witness) left right) :
    Same machine (read left) (read right) :=
  sound (joinvalid kinds graph valid x y level witness)
    (checkedjoin kinds x y level witness checked accepted) linked

structure Table (S A O : Type) where
  observe : S → O
  next : S → A → Option S

def Table.machine {S A O : Type} (table : Table S A O) : Machine S A O :=
  ⟨table.observe, fun x a y => table.next x a = some y⟩

def verify {S A O : Type} [DecidableEq O] (table : Table S A O)
    (states : List S) (actions : List A) (key : S → Nat) : Bool :=
  states.all fun x => states.all fun y =>
    if key x = key y then
      decide (table.observe x = table.observe y) &&
        actions.all (fun a =>
          decide (Option.map key (table.next x a) = Option.map key (table.next y a)))
    else true

theorem matchmove {S : Type} (key : S → Nat) {one two : Option S}
    (matchkey : Option.map key one = Option.map key two) {x : S}
    (here : one = some x) : ∃ y, two = some y ∧ key x = key y := by
  cases two with
  | none => simp [here] at matchkey
  | some y =>
    exact ⟨y, rfl, by simpa [here] using matchkey⟩

theorem checkedtable {S A O : Type} [DecidableEq O] {table : Table S A O}
    {states : List S} {actions : List A} {key : S → Nat}
    (statecover : ∀ x, x ∈ states) (actioncover : ∀ a, a ∈ actions)
    (passed : verify table states actions key = true) :
    Bisim table.machine (fun x y => key x = key y) := by
  intro x y heq
  have hx := List.all_eq_true.mp passed x (statecover x)
  have hy := List.all_eq_true.mp hx y (statecover y)
  simp only [heq, if_true, Bool.and_eq_true, decide_eq_true_eq] at hy
  refine ⟨hy.1, ?_, ?_⟩
  · intro a x' h
    have hk := List.all_eq_true.mp hy.2 a (actioncover a)
    exact matchmove key (of_decide_eq_true hk) h
  · intro a y' h
    have hk := List.all_eq_true.mp hy.2 a (actioncover a)
    obtain ⟨x', hit, link⟩ := matchmove key (of_decide_eq_true hk).symm h
    exact ⟨x', hit, link.symm⟩

theorem tablejoin {Sym S A O : Type} [DecidableEq Sym] [DecidableEq O]
    {table : Table S A O} {read : Term Sym → S}
    {states : List S} {actions : List A} {key : S → Nat}
    (statecover : ∀ x, x ∈ states) (actioncover : ∀ a, a ∈ actions)
    (passed : verify table states actions key = true)
    {kinds : Kinds Sym} {graph : Graph Sym}
    (valid : Valid kinds graph) (checked : Checks table.machine read kinds graph.log)
    {x y : Term Sym} {level witness : Sym} (equals : key (read x) = key (read y))
    {left right : Term Sym}
    (linked : same (join kinds graph x y level witness) left right) :
    Same table.machine (read left) (read right) :=
  joinsubstitute valid checked (substitute (checkedtable statecover actioncover passed) equals) linked

theorem walktail {S A O : Type} {machine : Machine S A O}
    {x : S} {a : A} {rest : List A} {head : O} {tail : List O}
    (h : Walk machine x (a :: rest) (head :: tail)) :
    ∃ y, machine.move x a y ∧ Walk machine y rest tail := by
  cases h with
  | next step more => exact ⟨_, step, more⟩

theorem singleobs {S A O : Type} {machine : Machine S A O} {x : S} {o : O}
    (h : Walk machine x [] [o]) : machine.observe x = o := by
  cases h
  rfl

theorem sameflip {S A O : Type} {machine : Machine S A O} {x y : S}
    (h : Same machine x y) : Same machine y x :=
  fun acts obs => (h acts obs).symm

theorem samemove {S A O : Type} {table : Table S A O} {x y x' : S} {a : A}
    (h : Same table.machine x y) (step : table.machine.move x a x') :
    ∃ y', table.machine.move y a y' ∧ Same table.machine x' y' := by
  obtain ⟨y', step', _⟩ := walktail ((h [a]
      [table.machine.observe x, table.machine.observe x']).mp (.next step .stop))
  refine ⟨y', step', ?_⟩
  intro acts obs
  constructor
  · intro more
    obtain ⟨target, move, next⟩ :=
      walktail ((h (a :: acts) (table.machine.observe x :: obs)).mp (.next step more))
    have identity : y' = target := Option.some.inj (step'.symm.trans move)
    exact identity ▸ next
  · intro more
    obtain ⟨target, move, next⟩ :=
      walktail ((h (a :: acts) (table.machine.observe y :: obs)).mpr (.next step' more))
    have identity : x' = target := Option.some.inj (step.symm.trans move)
    exact identity ▸ next

theorem coarsest {S A O : Type} (table : Table S A O) :
    Bisim table.machine (Same table.machine) := by
  intro x y h
  refine ⟨(singleobs ((h [] [table.machine.observe x]).mp .stop)).symm, ?_, ?_⟩
  · intro a x' step
    exact samemove h step
  · intro a y' step
    obtain ⟨x', move, link⟩ := samemove (sameflip h) step
    exact ⟨x', move, sameflip link⟩

def control : Table Bool Unit Unit :=
  ⟨fun _ => (), fun x _ => if x then some true else none⟩

theorem emptyactions : verify control [false, true] [] (fun _ => 0) = true := by decide

theorem allactions : verify control [false, true] [()] (fun _ => 0) = false := by decide

theorem continuationdiffers : ¬ Same control.machine false true := by
  intro h
  have yes : Walk control.machine true [()] [(), ()] := .next rfl .stop
  obtain ⟨_, missed, _⟩ := walktail ((h _ _).mpr yes)
  cases missed

#print axioms coarsest
#print axioms emptyactions
#print axioms allactions
#print axioms continuationdiffers
#print axioms checkedtable
#print axioms tablejoin
#print axioms forward
#print axioms flip
#print axioms substitute
#print axioms chain
#print axioms sound
#print axioms checkedappend
#print axioms checkedjoin
#print axioms joinsubstitute
end Behavior
