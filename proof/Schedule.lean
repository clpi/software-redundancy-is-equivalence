/-
  The scheduler of algorithm.md section 21, gaps nine to
  thirteen: bounded witness-driven saturation over the
  resolution run's own rule table, with per-epoch ephemeral
  provenance. This file implements the two rulings of
  2026-11-24 as recorded in the program record of the
  equivalence generalization: saturation restricted to the
  witnessed cone, scored by bidirectional distance
  reduction, with per-rule fuel under exponential backoff,
  instantiation-depth tracking, a rank beam with bridge
  steps, and a flat provenance arena whose only persistent
  state is the global rule table.

  Four states are kept distinct: the rulings are settled
  intent; this file is implemented behavior; what the
  family gate checks at a landed pin is verified behavior;
  the supplied reference implementation (saved verbatim in
  the program's scratch, executed as the first control of
  the scheduler step, its congruence-credit test passing)
  is the semantic source this file ports — its semantics,
  not its language. Credit arithmetic here is exact
  rational arithmetic at the reference's own constants
  (decay 17/20, bridge bonus 3/2, cone-collision doubling,
  deposit floor 1/10000); the reference's binary floating
  point rounding is a representation artifact and is not
  reproduced. This toolchain carries no public rational
  type, so the file carries its own: a numerator and a
  positive denominator, compared and matched by cross
  multiplication, never normalized — equality of values
  is the cross-multiplication test, not pair identity.

  Rule identifiers are the caller's indices into the rule
  table, exactly as in the reference. The two sentinel
  rules sit at the top of the sixteen-bit rule range, as
  in the reference, so one range check skips them in
  crediting.
-/

namespace Sched

/-- An exact rational: a numerator and a denominator.
    Every denominator this file builds is positive —
    literals have denominator one or a named positive
    constant, and the operations multiply or preserve
    denominators — so cross multiplication decides
    equality and order. -/
structure Q where
  num : Int
  den : Nat
deriving DecidableEq

instance (n : Nat) : OfNat Q n :=
  ⟨{ num := n, den := 1 }⟩

/-- Build a rational from a numerator and a positive
    denominator. -/
def q (n : Int) (d : Nat) : Q :=
  { num := n, den := d }

/-- Addition on the pair representation. -/
def qadd (x y : Q) : Q :=
  { num := x.num * y.den + y.num * x.den, den := x.den * y.den }

/-- Multiplication on the pair representation. -/
def qmul (x y : Q) : Q :=
  { num := x.num * y.num, den := x.den * y.den }

/-- Division by a positive count, on the pair
    representation: the share of a credit split evenly
    across that many premises. -/
def qdivn (x : Q) (n : Nat) : Q :=
  { num := x.num, den := x.den * n }

/-- Order by cross multiplication. -/
def qle (x y : Q) : Bool :=
  x.num * y.den ≤ y.num * x.den

/-- Strict order by cross multiplication. -/
def qlt (x y : Q) : Bool :=
  x.num * y.den < y.num * x.den

/-- Value equality by cross multiplication. -/
def qbeq (x y : Q) : Bool :=
  x.num * y.den == y.num * x.den

/-- The smaller of two rationals under the order. -/
def qmin (x y : Q) : Q :=
  if qle x y then x else y

theorem qminle (x y : Q) : qle (qmin x y) y = true := by
  unfold qmin
  split
  · assumption
  · simp only [qle, decide_eq_true_eq]
    exact Int.le_refl _

/-- The witness sentinel rule: anchors a derivation at a
    witnessed node, depth zero. -/
def wit : Nat := 65535

/-- The congruence sentinel rule: a derivation step that
    closes over a child merge, crediting an outer merge
    back through it to an inner bridge rule. -/
def cong : Nat := 65534

/-- The bridge flag: the step temporarily raised the cost
    when it fired. -/
def bridgebit : Nat := 1

/-- The multi-premise flag: premises beyond the second
    live in the overflow slab. -/
def multibit : Nat := 2

/-- One derivation node of the arena: rule, depth, first
    premise, second premise (or overflow offset when the
    multi-premise flag is set), flags. Flat and dense: a
    node's identifier is its position in the arena. -/
structure Node where
  rule : Nat
  depth : Nat
  first : Nat
  second : Nat
  flags : Nat
deriving DecidableEq

/-- The base sentinel node: every pre-existing node of a
    prior epoch shares this one identifier, zero. -/
def base : Node :=
  { rule := wit, depth := 0, first := 0, second := 0, flags := 0 }

/-- The per-epoch provenance arena: a flat vector of
    derivation nodes, a flat overflow slab for premises
    beyond two, the link from each local node to its
    derivation, and the epoch's per-rule credit deltas.
    Nothing here persists past the epoch close. -/
structure Arena where
  nodes : List Node
  over : List Nat
  link : List Nat
  delta : List Q

/-- A fresh arena at the given rule count: the base
    sentinel alone in the node vector, no links, zeroed
    credit deltas. -/
def fresh (rules : Nat) : Arena :=
  { nodes := [base], over := [], link := [],
    delta := List.replicate rules 0 }

/-- Reset between witness rows: the node vector returns
    to the base sentinel alone, the slab and the links
    clear, the deltas zero. Capacity is a representation
    matter of the reference; the list model keeps the
    observable state only. -/
def reset (a : Arena) : Arena :=
  { nodes := [base], over := [], link := [],
    delta := List.replicate a.delta.length 0 }

theorem resetnodes (a : Arena) : (reset a).nodes = [base] := rfl

theorem resetlen (a : Arena) :
    (reset a).delta.length = a.delta.length := by
  simp [reset]

/-- The node at an identifier, defaulting to the base
    sentinel for an identifier the arena does not hold,
    as the reference defaults an unlinked node to base. -/
def nodeof (a : Arena) (i : Nat) : Node :=
  a.nodes[i]?.getD base

/-- The derivation linked to a local node, if any. -/
def linkof (a : Arena) (loc : Nat) : Option Nat :=
  a.link[loc]?

/-- Write a value at a position of a list, inside the
    list's length; outside it the list is unchanged. -/
def put : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: put xs n v

theorem putlen : (put l i v).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ n => simp [put, ih]

theorem getput : ∀ (l : List α) (i : Nat) (v : α),
    i < l.length → (put l i v)[i]? = some v
  | [], i, _, h => by simp at h
  | _ :: _, 0, v, _ => rfl
  | _ :: xs, n + 1, v, h => by
    simp only [put, List.length_cons, Nat.add_lt_add_iff_right] at h ⊢
    rw [List.getElem?_cons_succ]
    exact getput xs n v h

/-- Extend a list of naturals with zeros until a position
    exists in it. -/
def pad (l : List Nat) (i : Nat) : List Nat :=
  l ++ List.replicate (i + 1 - l.length) 0

/-- The depth a new derivation would carry: zero for a
    witness anchor, else one past the deepest premise. -/
def newdepth (a : Arena) (rule : Nat) (ps : List Nat) : Nat :=
  if rule = wit then 0
  else ps.foldl (fun m p => max m (nodeof a p).depth) 0 + 1

/-- The stored form of a premise list: first premise,
    second premise or overflow offset, flags, and the
    grown overflow slab. -/
def stored (over : List Nat) (ps : List Nat) (bridge : Bool) :
    Nat × Nat × Nat × List Nat :=
  let f : Nat := if bridge then bridgebit else 0
  match ps with
  | [] => (0, 0, f, over)
  | [p] => (p, 0, f, over)
  | [p, q] => (p, q, f, over)
  | p :: rest => (p, over.length, f + multibit,
      over ++ [rest.length] ++ rest)

/-- The append half of a record step: the new node takes
    the next dense identifier, the arena's length. -/
def recordgo (a : Arena) (loc rule : Nat) (ps : List Nat)
    (bridge : Bool) (nd : Nat) : Arena × Nat :=
  let (one, two, fl, over') := stored a.over ps bridge
  let node : Node :=
    { rule := rule, depth := nd, first := one, second := two,
      flags := fl }
  let id := a.nodes.length
  ({ a with nodes := a.nodes ++ [node], over := over', link := put (pad a.link loc) loc id }, id)

/-- Record a derivation for a local node in the arena,
    under the first-parent-wins minimum-depth rule: a
    re-derivation that is not strictly shallower is
    refused and the existing derivation stands. The
    provenance graph is therefore acyclic even over
    cyclic graphs, and memory is one node per newly
    allocated node. -/
def record (a : Arena) (loc rule : Nat) (ps : List Nat)
    (bridge : Bool) : Arena × Nat :=
  let nd := newdepth a rule ps
  match linkof a loc with
  | some old =>
    if old ≠ 0 ∧ (nodeof a old).depth ≤ nd then (a, old)
    else recordgo a loc rule ps bridge nd
  | none => recordgo a loc rule ps bridge nd

theorem recordfresh (rules loc rule : Nat) (ps : List Nat)
    (bridge : Bool) :
    ((record (fresh rules) loc rule ps bridge).1.nodes).length
      = (fresh rules).nodes.length + 1 := by
  simp [record, recordgo, linkof, fresh]

/-- First-parent-wins: when a local node already links to
    a derivation no deeper than the new offer, the record
    step returns that derivation and leaves the arena
    untouched. -/
theorem recordkeeps (a : Arena) (loc rule : Nat)
    (ps : List Nat) (bridge : Bool) (old : Nat)
    (hlink : linkof a loc = some old) (hbase : old ≠ 0)
    (hdepth : (nodeof a old).depth ≤ newdepth a rule ps) :
    record a loc rule ps bridge = (a, old) := by
  unfold record
  rw [hlink]
  simp [hbase, hdepth]

/-- The persistent global rule table: the only provenance
    state that survives an epoch close. One row per rule:
    merge credit, allocations, fires — the reference's
    twenty-four bytes per rule, as values. -/
structure Stats where
  credit : Q
  allocs : Nat
  fires : Nat
deriving DecidableEq

/-- A rule table over a fixed rule count. -/
structure Table where
  rows : List Stats

/-- A fresh table of zeroed rows. -/
def tablefresh (rules : Nat) : Table :=
  { rows := List.replicate rules { credit := 0, allocs := 0, fires := 0 } }

/-- The row of a rule, if the table holds it. -/
def rowof (t : Table) (rule : Nat) : Option Stats :=
  t.rows[rule]?

/-- Record a rule firing and the growth it allocated;
    growth counts at least one, as in the reference, so
    no later division can see a zero. -/
def fire (t : Table) (rule growth : Nat) : Table :=
  match rowof t rule with
  | some s =>
    { rows := put t.rows rule { s with fires := s.fires + 1, allocs := s.allocs + max growth 1 } }
  | none => t

/-- The exploit term of the scheduling score: merge
    credit per allocation. The reference's full score
    adds a real-valued exploration term over the same
    three statistics; the statistics are the persistent
    state, and they are exact here. -/
def exploit (t : Table) (rule : Nat) : Q :=
  match rowof t rule with
  | some s => if s.allocs = 0 then 0 else qdivn s.credit s.allocs
  | none => 0

/-- Flush an epoch's credit deltas into the table: the
    one write by which provenance outlives its epoch.
    Fires and allocations are untouched. -/
def flush (t : Table) (a : Arena) : Table :=
  { rows := List.zipWith (fun s d => { s with credit := qadd s.credit d }) t.rows a.delta }

theorem flushlen (t : Table) (a : Arena)
    (h : a.delta.length = t.rows.length) :
    (flush t a).rows.length = t.rows.length := by
  simp [flush, List.length_zipWith, h]

/-- Deposit credit at a node during the backward walk:
    nothing lands on the base sentinel, nothing below
    the floor lands at all, and the accumulated credit
    at a node is capped at the merge's total reward, so
    a node where parallel paths reconverge cannot farm
    the reward repeatedly. -/
def deposit (pend : List Q) (cap : Q) (id : Nat)
    (amt : Q) : List Q :=
  if id = 0 ∨ qlt amt (q 1 10000) then pend
  else put pend id (qmin (qadd (pend[id]?.getD 0) amt) cap)

theorem depositcap (pend : List Q) (cap : Q)
    (id : Nat) (amt : Q) (h : id < pend.length)
    (hcap : qle (pend[id]?.getD 0) cap = true) :
    qle ((deposit pend cap id amt)[id]?.getD 0) cap = true := by
  unfold deposit
  split
  · exact hcap
  · rw [getput pend id _ h]
    simp [qminle]

/-- The premises a derivation node propagates credit to:
    the overflow tail when the multi-premise flag is set,
    else the stored premises that are not the base
    sentinel. -/
def premises (a : Arena) (n : Node) : List Nat :=
  if n.flags &&& multibit ≠ 0 then
    n.first :: (a.over.drop (n.second + 1)).take
      (a.over[n.second]?.getD 0)
  else
    [n.first, n.second].filter (fun p => p ≠ 0)

/-- Spread one node's decayed credit evenly across its
    premises, as the reference splits it. -/
def spread (a : Arena) (cap : Q) (n : Node)
    (pend : List Q) (amt : Q) : List Q :=
  let ps := premises a n
  if ps.length = 0 then pend
  else ps.foldl (fun p qq => deposit p cap qq (qdivn amt ps.length)) pend

/-- Settle one depth level of the backward walk: every
    node at this depth holding pending credit is credited
    to its rule — sentinel rules are skipped by the range
    check against the delta vector, bridge nodes at the
    bonus — and its decayed credit spreads to its
    premises, which all sit at strictly smaller depths in
    an arena built by the record step. -/
def settle (a : Arena) (cap : Q) (d : Nat) :
    List Q × List Q → List Q × List Q :=
  (List.range a.nodes.length).foldl (fun st id =>
    let n := nodeof a id
    let amt := st.1[id]?.getD 0
    if n.depth = d ∧ amt ≠ 0 then
      let bonus : Q := if n.flags &&& bridgebit ≠ 0 then q 3 2 else 1
      let delta' := if n.rule < st.2.length then
          put st.2 n.rule (qadd (st.2[n.rule]?.getD 0) (qmul amt bonus))
        else st.2
      (spread a cap n st.1 (qmul amt (q 17 20)), delta')
    else st)

/-- The backward credit walk, in descending depth order:
    settle the deepest level first, down to the anchors. -/
def walk (a : Arena) (cap : Q) :
    Nat → List Q × List Q → List Q × List Q
  | 0, st => settle a cap 0 st
  | d + 1, st => walk a cap d (settle a cap (d + 1) st)

/-- Assign a merge's credit: the total reward is the
    heuristic reduction itself, doubled when the forward
    and backward witness cones collide; half lands on
    each colliding node and walks backward. A merge that
    does not reduce the heuristic earns nothing. The
    deltas accumulate into the arena's epoch deltas. -/
def credit (a : Arena) (n1 n2 : Nat) (dh : Q)
    (joined : Bool) : Arena :=
  if qle dh 0 then a
  else
    let total := if joined then qmul dh 2 else dh
    let pend0 := List.replicate a.nodes.length 0
    let pend := deposit (deposit pend0 total n1 (qdivn total 2))
      total n2 (qdivn total 2)
    let (_, d') := walk a total a.nodes.length
      (pend, List.replicate a.delta.length 0)
    { a with delta := List.zipWith qadd a.delta d' }

/-- The reference's first control, carried into this
    tree: a bridge rule credited through a congruence
    merge. The bridge rule fires on the base sentinel,
    a simplification fires on its output, a congruence
    closure links the outer wrapper to the simplified
    child, and the wrapper collides with the backward
    witness cone at a heuristic reduction of ten, the
    cones joined. -/
def scen : Arena × Table :=
  let a0 := fresh 2
  let t0 := tablefresh 2
  let (a1, pb) := record a0 0 0 [0] true
  let t1 := fire t0 0 3
  let (a2, ps) := record a1 1 1 [pb] false
  let t2 := fire t1 1 1
  let (a3, pc) := record a2 2 cong [0, ps] false
  let a4 := credit a3 pc 0 10 true
  (a4, flush t2 a4)

/-- Row-by-row match under value equality of credits:
    the scenario's accounting test. -/
def rowsmatch (xs ys : List Stats) : Bool :=
  xs.length == ys.length &&
    (List.zipWith (fun s t =>
      qbeq s.credit t.credit && s.allocs == t.allocs &&
        s.fires == t.fires) xs ys).all id

/-- The scenario's accounting, exact: the simplification
    rule is credited 17/2 (the congruence node's full
    decayed share), the bridge rule 867/80 (that share
    decayed once more, at the bridge bonus), the
    congruence sentinel nothing; fires and allocations
    stand as fired. -/
theorem scentable : rowsmatch scen.2.rows
    [ { credit := q 867 80, allocs := 3, fires := 1 },
      { credit := q 17 2, allocs := 1, fires := 1 } ] = true := by
  decide

/-- The scenario's arena holds the base sentinel and the
    three recorded derivations, and resets to the base
    sentinel alone. -/
theorem scenarena : scen.1.nodes.length = 4 ∧
    (reset scen.1).nodes = [base] := by
  constructor
  · decide
  · rfl

/-- A saturation candidate: the rule it would fire, its
    bidirectional score, its instantiation depth, and
    the two flags the bounded design reads — bridge step,
    and membership in the witnessed cone. -/
structure Cand where
  rule : Nat
  gain : Int
  depth : Nat
  bridge : Bool
  cone : Bool
deriving DecidableEq

/-- The bidirectional score of applying a rule that takes
    a node from one place to another: the forward distance
    reduction toward the witnessed class plus the backward
    distance reduction, the two cones' readings summed. -/
def score (fwd back : Nat → Nat) (n m : Nat) : Int :=
  ((fwd n : Int) - (fwd m : Int)) +
    ((back n : Int) - (back m : Int))

theorem scoreparts (fwd back : Nat → Nat) (n m : Nat) :
    score fwd back n m =
      ((fwd n : Int) - (fwd m : Int)) +
        ((back n : Int) - (back m : Int)) := rfl

/-- Choose the better of two candidates by score; ties
    keep the earlier one, so the visiting order is the
    caller's fixed order among equals. -/
def better (b d : Cand) : Cand :=
  if d.gain > b.gain then d else b

theorem bettergain (b d : Cand) :
    b.gain ≤ (better b d).gain ∧ d.gain ≤ (better b d).gain ∧
      (better b d = b ∨ better b d = d) := by
  unfold better
  split <;> simp_all <;> omega

/-- The best candidate of a nonempty list, by score. -/
def pick : List Cand → Option Cand
  | [] => none
  | c :: cs => some (cs.foldl better c)

theorem foldpick (b : Cand) (cs : List Cand) :
    ∀ r, cs.foldl better b = r →
      (r = b ∨ r ∈ cs) ∧ b.gain ≤ r.gain ∧
        ∀ d ∈ cs, d.gain ≤ r.gain := by
  induction cs generalizing b with
  | nil => intro r hr; simp at hr; simp [← hr]
  | cons c cs ih =>
    intro r hr
    have hb := bettergain b c
    have hi := ih (b := better b c) r hr
    obtain ⟨hmem, hge, hmax⟩ := hi
    refine ⟨?_, ?_, ?_⟩
    · cases hmem with
      | inl h =>
        cases hb.2.2 with
        | inl hb1 => exact Or.inl (h.trans hb1)
        | inr hb2 =>
          exact Or.inr (by rw [h.trans hb2]; exact List.mem_cons_self)
      | inr h => exact Or.inr (List.mem_cons_of_mem _ h)
    · exact Int.le_trans hb.1 hge
    · intro d hd
      cases List.mem_cons.mp hd with
      | inl h => rw [h]; exact Int.le_trans hb.2.1 hge
      | inr h => exact hmax d h

/-- The picked candidate is a member of its list. -/
theorem pickmem {cs : List Cand} {c : Cand} :
    pick cs = some c → c ∈ cs := by
  cases cs with
  | nil => simp [pick]
  | cons x xs =>
    intro h
    simp only [pick, Option.some.injEq] at h
    have hf := foldpick x xs c h
    cases hf.1 with
    | inl hh => rw [hh]; exact List.mem_cons_self
    | inr hh => exact List.mem_cons_of_mem _ hh

/-- The picked candidate's score is at least every
    candidate's: selection is by the bidirectional score,
    not by position. -/
theorem pickmax {cs : List Cand} {c d : Cand} :
    pick cs = some c → d ∈ cs → d.gain ≤ c.gain := by
  cases cs with
  | nil => simp
  | cons x xs =>
    intro h hd
    simp only [pick, Option.some.injEq] at h
    have hf := foldpick x xs c h
    cases List.mem_cons.mp hd with
    | inl hh => rw [hh]; exact hf.2.1
    | inr hh => exact hf.2.2 d hh

/-- The rank of a candidate: how many candidates of the
    list score strictly above it. -/
def rank (cs : List Cand) (c : Cand) : Nat :=
  (cs.filter (fun d => c.gain < d.gain)).length

/-- The beam: every bridge candidate survives, whatever
    its rank — the valley problem's mitigation — and every
    other survivor stands within the beam width by rank.
    Ties share a rank, so the beam may hold more than the
    width when scores tie at the boundary. -/
def beam (w : Nat) (cs : List Cand) : List Cand :=
  cs.filter (fun c => c.bridge || rank cs c < w)

theorem beambridge {w : Nat} {cs : List Cand} {c : Cand} :
    c ∈ cs → c.bridge = true → c ∈ beam w cs := by
  intro h hb
  simp [beam, List.mem_filter, h, hb]

theorem beamrank {w : Nat} {cs : List Cand} {c : Cand} :
    c ∈ beam w cs → c ∈ cs ∧ (c.bridge = true ∨ rank cs c < w) := by
  intro h
  simp only [beam, List.mem_filter] at h
  obtain ⟨hcs, hb⟩ := h
  refine ⟨hcs, ?_⟩
  rw [Bool.or_eq_true] at hb
  cases hb with
  | inl hh => exact Or.inl hh
  | inr hh => exact Or.inr (of_decide_eq_true hh)

/-- The scheduler state between passes: the persistent
    rule table, the per-rule fuel allowances, the per-rule
    counts of consecutive fires without a merge, and the
    base allowance every rule starts an epoch with. -/
structure Plan where
  table : Table
  fuel : List Nat
  stall : List Nat
  base : Nat

/-- A rule's remaining allowance. -/
def fuelof (p : Plan) (r : Nat) : Nat :=
  p.fuel[r]?.getD 0

/-- A rule's count of consecutive fires without a merge. -/
def stallof (p : Plan) (r : Nat) : Nat :=
  p.stall[r]?.getD 0

/-- Fire a rule under the scheduler: refused outright
    when the rule's allowance is spent. On a merge the
    rule's stall count clears and its allowance restores
    to the base; without a merge the stall count grows
    and the refreshed allowance is the base divided by
    two to the stall count — exponential backoff keyed
    on growth without merges. -/
def step (p : Plan) (r growth : Nat) (merged : Bool) :
    Option Plan :=
  if fuelof p r = 0 then none
  else some
    { table := fire p.table r growth,
      fuel := put p.fuel r
        (if merged then p.base else p.base / 2 ^ (stallof p r + 1)),
      stall := put p.stall r
        (if merged then 0 else stallof p r + 1),
      base := p.base }

theorem stepnone {p : Plan} {r growth : Nat} {merged : Bool} :
    fuelof p r = 0 → step p r growth merged = none := by
  intro h
  simp [step, h]

theorem stepfuel {p p' : Plan} {r growth : Nat}
    (h : step p r growth false = some p')
    (hr : r < p.fuel.length) :
    fuelof p' r = p.base / 2 ^ (stallof p r + 1) := by
  unfold step at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp [fuelof, getput p.fuel r _ hr]

/-- The backoff bound: after a fire without a merge, the
    refreshed allowance times two to the stall count does
    not exceed the base allowance — the allowance shrinks
    exponentially in consecutive unmerged fires, which is
    what caps a blowup class in order of the stall count
    of steps per witness. -/
theorem stepbound {p p' : Plan} {r growth : Nat}
    (h : step p r growth false = some p')
    (hr : r < p.fuel.length) :
    fuelof p' r * 2 ^ (stallof p r + 1) ≤ p.base := by
  rw [stepfuel h hr]
  exact Nat.div_mul_le_self _ _

theorem stepmerge {p p' : Plan} {r growth : Nat}
    (h : step p r growth true = some p')
    (hr : r < p.fuel.length) (hs : r < p.stall.length) :
    fuelof p' r = p.base ∧ stallof p' r = 0 := by
  unfold step at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact ⟨by simp [fuelof, getput p.fuel r _ hr],
      by simp [stallof, getput p.stall r _ hs]⟩

/-- One bounded pass over the candidate pool: the beam
    first, then the three gates of the bounded design —
    the witnessed cone, the instantiation-depth cap, and
    the rule's fuel. The pass is a selection; the run
    applies what it returns and reports merges and growth
    back through the step function. -/
def sweep (p : Plan) (cap w : Nat) (cs : List Cand) :
    List Cand :=
  (beam w cs).filter (fun c =>
    c.cone && (c.depth ≤ cap) && (fuelof p c.rule ≠ 0))

/-- Everything a pass returns passed every gate: it is a
    pool member, in the cone, within the depth cap, and
    its rule had fuel. -/
theorem sweepgates {p : Plan} {cap w : Nat} {cs : List Cand}
    {c : Cand} :
    c ∈ sweep p cap w cs →
      c ∈ cs ∧ c.cone = true ∧ c.depth ≤ cap ∧
        fuelof p c.rule ≠ 0 := by
  intro h
  simp only [sweep, List.mem_filter] at h
  obtain ⟨hb, hg⟩ := h
  have hbeam := beamrank hb
  rw [Bool.and_eq_true, Bool.and_eq_true] at hg
  obtain ⟨⟨hcone, hdepth⟩, hfuel⟩ := hg
  exact ⟨hbeam.1, hcone, of_decide_eq_true hdepth,
    of_decide_eq_true hfuel⟩

end Sched
