/-
  The resolution algorithm of algorithm.md, implemented
  over the canonical model of Core and the operations
  of Ops. This file is the implementation lane the
  algorithm specification names: it defines the run as
  a computable procedure over the model's own values,
  and proves the specification's claims where they are
  provable here. Claims that rest on a premise are
  labeled with the premise stated as a proposition in
  this file, in the manner of Premises. Nothing in
  this file restates the model: every append a run
  makes is an operation of Ops, applied through its
  run fold, and the growth and validity facts are the
  ones Ops and Claims prove.

  Four states are kept distinct: the specification is
  settled intent; this file is implemented behavior;
  what the family gate checks at a landed pin is
  verified behavior; and each claim of the algorithm
  specification is carried below at exactly the state
  its proof here earns, no higher.
-/

import Ops
import Claims
import Premises

open scoped Classical

variable {Sym : Type}

/- ## The values of the algorithm (algorithm.md section 4)

   A candidate is a value of the operation type of
   Ops: its kind is the operation's constructor, its
   term list, level name, and witness are read off the
   operation, and the painter of a paint candidate is
   the color's painter field. A change of no kind, or
   of a shape its kind forbids, is therefore not a
   candidate in this implementation at all: the intake
   refusals of form and kind in section 4.1 are
   accounted by that construction, and the case
   register gains a line saying so. -/

/-- The four kinds, in the visiting order of
    section 6: enter, join, paint, record. -/
inductive Tag where
  | enter
  | join
  | paint
  | record
deriving DecidableEq

/-- The kind of a candidate. -/
def tagof : Op Sym → Tag
  | .enter _ _ _ => .enter
  | .join _ _ _ _ => .join
  | .paint _ _ _ _ => .paint
  | .record _ _ => .record

/-- The position of a kind in the visiting order. -/
def tagno : Tag → Nat
  | .enter => 0
  | .join => 1
  | .paint => 2
  | .record => 3

/-- The term list a candidate acts on (section 4.1):
    one term for enter and for paint, two for join,
    the level's term list for record. -/
def termsof : Op Sym → List (Term Sym)
  | .enter t _ _ => [t]
  | .join a b _ _ => [a, b]
  | .paint t _ _ _ => [t]
  | .record lv _ => lv.terms

/-- The level name a candidate is resolved at. -/
def levelof : Op Sym → Sym
  | .enter _ l _ => l
  | .join _ _ l _ => l
  | .paint _ _ l _ => l
  | .record lv _ => lv.name

/-- The witness symbol a candidate names. -/
def witof : Op Sym → Sym
  | .enter _ _ w => w
  | .join _ _ _ w => w
  | .paint _ _ _ w => w
  | .record _ w => w

/-- The scope rank a term requires (section 6):
    trivial first, then first order, then full. -/
def rankof (t : Term Sym) : Nat :=
  if Term.trivial t = true then 0
  else if Term.first t = true then 1
  else 2

/-- The rank of a candidate: the widest rank its
    terms require. -/
def candrank (op : Op Sym) : Nat :=
  (termsof op).foldl (fun m t => max m (rankof t)) 0

/-- Collection, as a boolean: the decidable reading
    of the collected predicate of Core. -/
def collectedb [DecidableEq Sym] (g : Graph Sym)
    (t : Term Sym) : Bool :=
  g.edges.any (fun e => decide (t ∈ e.terms))

/-- The counted operation cost of a candidate at a
    graph (section 7.3), the operation part only:
    enter costs one; join costs one plus one for each
    of its terms not collected; record costs one plus
    one for each level term not collected; paint
    costs one where its term is collected and has no
    cost where it is not. -/
def priceof [DecidableEq Sym] (g : Graph Sym) :
    Op Sym → Option Nat
  | .enter _ _ _ => some 1
  | .join a b _ _ =>
      some (1 + (if collectedb g a then 0 else 1) +
        (if collectedb g b then 0 else 1))
  | .record lv _ =>
      some (1 + (lv.terms.filter
        (fun t => !(collectedb g t))).length)
  | .paint t _ _ _ =>
      if collectedb g t then some 1 else none

/-- Whether a candidate's kind carries a witness
    check (section 7.1): join, paint, and record are
    checked; enter is not. -/
def checkable (op : Op Sym) : Bool :=
  match tagof op with
  | .enter => false
  | _ => true

/-- The whole charge of a candidate at a graph
    (section 8 step 5): its counted operation cost,
    plus one witness check where its kind carries
    one. No charge where it has no cost. -/
def chargeof [DecidableEq Sym] (g : Graph Sym)
    (op : Op Sym) : Option Nat :=
  (priceof g op).map
    (fun n => n + (if checkable op then 1 else 0))

/- ## The run context (algorithm.md section 2)

   One structure carries the run's inputs besides the
   graph, the candidate list, and the budget: the
   kinds of the model, the effective scope as one
   predicate (the narrower of the target's scope and
   the availability ceiling, fixed by the caller as
   section 5.1 directs, the widening order being the
   model's own), the witness check as one decidable
   function on candidates (input seven of section 2;
   what it does against the ground is gap six, and
   its honesty is the witness honesty premise), the
   target level and its witness where it presents
   one, the three marks of the qualification scheme
   the two filter rule reads (seen for the
   observation entry, wanted for the intent entry,
   meant for the intended mark), the filter
   predicates (readings only, section 11.2), and the
   intent items as their terms (section 4.3). -/

/-- The inputs of one run, besides the graph, the
    candidate list, and the budget. -/
structure Ctx (Sym : Type) where
  kinds : Kinds Sym
  scope : Term Sym → Bool
  check : Op Sym → Bool
  cands : List (Op Sym)
  target : Level Sym
  twit : Option Sym
  seen : Sym
  wanted : Sym
  meant : Sym
  filters : List (Color Sym → Bool)
  intent : List (Term Sym)

/- ## Levels by name (section 9.2 and gap one)

   A level stands in a graph under its name when a
   recorded level of that name holds the same terms
   and a scope agreeing on those terms: a level's
   scope is only ever applied to its own terms in
   the model, so agreement on the terms is the
   decidable reading of sameness here. A name clash
   is a recorded level of the name that is not the
   same in that reading. -/

/-- A recorded level of the same name, the same
    terms, and a scope agreeing on those terms
    stands in the graph. -/
def samename [DecidableEq Sym] (g : Graph Sym)
    (lv : Level Sym) : Bool :=
  g.levels.any (fun old =>
    decide (old.name = lv.name ∧ old.terms = lv.terms ∧
      lv.terms.all (fun t => old.scope t = lv.scope t)))

/-- A recorded level of the name stands that is not
    the same level in the reading above. -/
def nameclash [DecidableEq Sym] (g : Graph Sym)
    (lv : Level Sym) : Bool :=
  g.levels.any (fun old => decide (old.name = lv.name)) &&
    !(samename g lv)

/-- A level the model can record: its terms are
    distinct and each satisfies its own scope, the
    standing hypotheses of the record operation in
    Ops. A candidate or target presenting a level
    failing this is refused with reason form. -/
def recordok [DecidableEq Sym] (lv : Level Sym) :
    Bool :=
  decide (lv.terms.Nodup) &&
    lv.terms.all (fun t => lv.scope t)

/- ## Parts and relevance (section 8 step 3) -/

/- The size of a term: one plus the sizes of its
   parts, by the grammar recursion of Core. -/
mutual
def tsize : Term Sym → Nat
  | .atom _ => 1
  | .form h args => 1 + tsize h + tsizes args
def tsizes : List (Term Sym) → Nat
  | [] => 0
  | t :: rest => tsize t + tsizes rest
end

/-- Subterm at any depth, itself included, computed
    with fuel the size of the larger term: parts are
    strictly smaller, so the fuel suffices. -/
def subf [DecidableEq Sym] :
    Nat → Term Sym → Term Sym → Bool
  | 0, _, _ => false
  | n + 1, t, u =>
      decide (t = u) ||
        (Term.parts u).any (fun p => subf n t p)

/-- One term is a subterm of another, at any depth. -/
def subterm [DecidableEq Sym] (t u : Term Sym) :
    Bool :=
  subf (tsize u + 1) t u

/-- One term is a part of another at any depth under
    the parts function, the term itself excluded. -/
def partof [DecidableEq Sym] (t u : Term Sym) :
    Bool :=
  (Term.parts u).any (fun p => subterm t p)

/- ## The derived set (section 13)

   The three source states and their one join. Source
   two, new, is read as the state of presented terms
   in scope that the graph has not captured: the
   reading under which claim eleven is proved. The
   case register gains a line on the wording, since
   section 13.3 also speaks of collected terms
   standing in the join in their own right. -/

/-- Source two of the derived set: the presented
    terms, of the target and of the candidates, that
    satisfy the effective scope and are not collected
    in the graph. -/
def fresh [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (cands : List (Op Sym)) :
    State Sym :=
  (ctx.target.terms ++ cands.flatMap termsof).filter
    (fun t => ctx.scope t && !(collectedb g t))

/-- Source three of the derived set: the terms of
    the edges meeting the stated state, joined with
    the terms of the edges of any filtered view at
    the target that hold a stated term or a target
    term. -/
def overlap [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) : State Sym :=
  let meet := g.edges.filter (fun e =>
    e.terms.any (fun t => decide (t ∈ ctx.intent)))
  let viewed := (view g ctx.target).filter (fun e =>
    ctx.filters.any (fun f => e.colors.any f) &&
      e.terms.any (fun t =>
        decide (t ∈ ctx.intent) ||
          decide (t ∈ ctx.target.terms)))
  (meet ++ viewed).flatMap (fun e => e.terms)

/-- The derived set: one join, in the one lattice,
    of the stated, the new, and the overlap states,
    in that order as a construction. -/
def derivedset [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (cands : List (Op Sym)) :
    State Sym :=
  State.join (State.join ctx.intent (fresh ctx g cands))
    (overlap ctx g)

/-- Relevance of a candidate at a graph (section 8
    step 3): one of its terms stands in the bound
    reading of the target, or in the target's terms,
    or in the derived set, or is a part at any depth
    of a target term or of a bound term, or it is a
    record of the target's name. -/
def relevant [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (cands : List (Op Sym))
    (op : Op Sym) : Bool :=
  let ts := termsof op
  let bnd := bound g ctx.target
  ts.any (fun t => decide (t ∈ bnd)) ||
    ts.any (fun t => decide (t ∈ ctx.target.terms)) ||
    ts.any (fun t =>
      decide (t ∈ derivedset ctx g cands)) ||
    ts.any (fun t =>
      ctx.target.terms.any (fun u => partof t u)) ||
    ts.any (fun t => bnd.any (fun u => partof t u)) ||
    (match op with
      | .record lv _ => decide (lv.name = ctx.target.name)
      | _ => false)

/- ## The two filter rule (section 12.3) -/

/-- The edge holding a term, where one does: on a
    valid graph the partition makes it the only one. -/
def edgeof [DecidableEq Sym] (g : Graph Sym)
    (t : Term Sym) : Option (Edge Sym) :=
  g.edges.find? (fun e => decide (t ∈ e.terms))

/-- The filter test of a candidate at a graph: a
    paint of the intended mark passes only where the
    edge of its term already holds an observation
    entry and an intent entry of the same painter.
    Every other candidate passes. -/
def filterok [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (op : Op Sym) : Bool :=
  match op with
  | .paint t c _ _ =>
      if decide (c.mark = ctx.meant) then
        match edgeof g t with
        | none => false
        | some e =>
            e.colors.any (fun x =>
              decide (x.who = c.who ∧
                x.mark = ctx.seen)) &&
            e.colors.any (fun x =>
              decide (x.who = c.who ∧
                x.mark = ctx.wanted))
      else true
  | _ => true

/- ## Outcomes and reasons (sections 4.4 and 16.1) -/

/-- A reason word of section 16.1. This
    implementation gives form (a level the model
    cannot record), scope, target, collected,
    witness, budget, filter, and name; kind is
    accounted by construction, rank by gap two's
    interim rule, and graph by the validity
    hypothesis every claim here carries. -/
inductive Why where
  | form
  | kind
  | scope
  | rank
  | target
  | collected
  | witness
  | budget
  | filter
  | name
  | graph
deriving DecidableEq

/-- The outcome of one candidate, or of the target:
    resolved with the spend charged to it, refused
    with its reason and the spend charged before the
    refusal, or deferred with its reason. -/
inductive Outcome where
  | resolved : Nat → Outcome
  | refused : Why → Nat → Outcome
  | deferred : Why → Outcome
deriving DecidableEq

/- ## The procedure (section 8)

   The run state: the running graph, the budget
   left, the total spend, and the operations applied
   so far, in order. The trace of operations is the
   run's only construction: the output graph is the
   fold of Ops over the input graph by this trace,
   which the soundness proof below uses. -/

/-- The state a run carries between steps. -/
structure St (Sym : Type) where
  g : Graph Sym
  left : Nat
  spent : Nat
  ops : List (Op Sym)

/-- One visit of one candidate (section 8 step 5).
    The tests are applied in the step's order —
    relevance, scope, cost, the filter rule, the
    record rules of section 9.2 — and the first
    reason that holds is the outcome's reason. The
    budget test compares the whole charge, check
    included; a failed check refuses with the check
    charged and the operation part never charged; a
    passed visit applies the operation as one atomic
    unit and charges the whole charge. -/
noncomputable def visit [DecidableEq Sym] (ctx : Ctx Sym)
    (cands : List (Op Sym)) (st : St Sym)
    (ic : Nat × Op Sym) : St Sym × Outcome :=
  let op := ic.2
  if !(relevant ctx st.g cands op) then
    (st, .deferred .target)
  else if !(termsof op).all ctx.scope then
    (st, .deferred .scope)
  else
    match priceof st.g op with
    | none => (st, .deferred .collected)
    | some price =>
        if !(filterok ctx st.g op) then
          (st, .deferred .filter)
        else
          match op with
          | .record lv _ =>
              if nameclash st.g lv then
                (st, .refused .name 0)
              else if !(recordok lv) then
                (st, .refused .form 0)
              else
                visitgo ctx st op price
          | _ => visitgo ctx st op price
where
  /-- The budget test, the witness check, and the
      atomic application, shared by every kind. -/
  visitgo (ctx : Ctx Sym) (st : St Sym)
      (op : Op Sym) (price : Nat) :
      St Sym × Outcome :=
    let charge := price + (if checkable op then 1 else 0)
    if charge > st.left then
      (st, .deferred .budget)
    else if checkable op && !(ctx.check op) then
      ({ st with left := st.left - 1,
                 spent := st.spent + 1 },
       .refused .witness 1)
    else
      ({ g := apply ctx.kinds st.g op,
         left := st.left - charge,
         spent := st.spent + charge,
         ops := st.ops ++ [op] },
       .resolved charge)

/-- The visiting order key of section 6 at a graph:
    scope rank, counted cost at that graph (a
    candidate with no cost sorts last in its rank),
    kind order, and input order as the final tie
    break. -/
def keyof [DecidableEq Sym]
    (g : Graph Sym) (ic : Nat × Op Sym) : List Nat :=
  [candrank ic.2,
   (priceof g ic.2).getD 0,
   (match priceof g ic.2 with
    | none => 1
    | some _ => 0),
   tagno (tagof ic.2),
   ic.1]

/-- Lexicographic order on visiting keys. -/
def lexle : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true
      else if b < a then false
      else lexle as bs

/-- Insertion into a sorted list of candidates. -/
def inskey [DecidableEq Sym]
    (g : Graph Sym) (x : Nat × Op Sym) :
    List (Nat × Op Sym) → List (Nat × Op Sym)
  | [] => [x]
  | y :: ys =>
      if lexle (keyof g x) (keyof g y) then
        x :: y :: ys
      else y :: inskey g x ys

/-- The visiting order of one pass: the pool sorted
    by the key at the pass's starting graph. -/
def isortkey [DecidableEq Sym]
    (g : Graph Sym) :
    List (Nat × Op Sym) → List (Nat × Op Sym)
  | [] => []
  | x :: xs => inskey g x (isortkey g xs)

/-- Intake (section 8 step 1): one charged test per
    candidate, in input order, while the budget
    pays. A candidate failing the scope test is
    deferred with reason scope and leaves the pool;
    a candidate the budget cannot test is deferred
    with reason budget. Intake appends nothing. -/
def intake [DecidableEq Sym] (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym) :
    St Sym × List (Nat × Op Sym) ×
      List (Nat × Outcome) :=
  let indexed := (List.range ctx.cands.length).zip
    ctx.cands
  indexed.foldl
    (fun acc ic =>
      let (st, pool, verdicts) := acc
      if st.left = 0 then
        (st, pool, verdicts ++ [(ic.1, .deferred .budget)])
      else
        let st' := { st with left := st.left - 1,
                             spent := st.spent + 1 }
        if (termsof ic.2).all ctx.scope then
          (st', pool ++ [ic], verdicts)
        else
          (st', pool,
           verdicts ++ [(ic.1, .deferred .scope)]))
    ({ g := g, left := budget, spent := 0, ops := [] },
     [], [])

/-- The candidates of a run, with their input
    positions. -/
def indexed (ctx : Ctx Sym) :
    List (Nat × Op Sym) :=
  (List.range ctx.cands.length).zip ctx.cands

/-- Recording the target (section 8 step 4 and
    section 9.2), atomically: the scope test, the
    record rules, the budget test on the whole
    charge, and the witness check where the target
    presents one, then the record operation in full
    or a deferral of the whole target with nothing
    applied. Where the level already stands in the
    reading of section 9.2, the recording is a
    repeat: it is resolved at no charge, and the
    bound is the bound of the graph as it stands —
    the reading under which the worked run of
    section 20 counts its second run; the case
    register gains a line on it. The bound returned
    is the bound of section 10.1 taken at the
    recording moment: the bound of the target in the
    graph the record operation reaches, whose entry
    carries exactly that state. -/
noncomputable def targetstep [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) :
    St Sym × Outcome × Option (State Sym) :=
  let lv := ctx.target
  let op : Op Sym := .record lv (ctx.twit.getD lv.name)
  if !(lv.terms.all ctx.scope) then
    (st, .deferred .scope, none)
  else if nameclash st.g lv then
    (st, .refused .name 0, none)
  else if !(recordok lv) then
    (st, .refused .form 0, none)
  else if samename st.g lv then
    (st, .resolved 0, some (bound st.g lv))
  else
    match priceof st.g op with
    | none => (st, .deferred .collected, none)
    | some price =>
        let charge := price +
          (match ctx.twit with
           | some _ => 1
           | none => 0)
        if charge > st.left then
          (st, .deferred .budget, none)
        else if (match ctx.twit with
                  | some w => ctx.check (.record lv w)
                  | none => true) = false then
          ({ st with left := st.left - 1,
                     spent := st.spent + 1 },
           .refused .witness 1, none)
        else
          let entered := enterall ctx.kinds st.g
            lv.terms ctx.kinds.record (witof op)
          ({ g := apply ctx.kinds st.g op,
             left := st.left - charge,
             spent := st.spent + charge,
             ops := st.ops ++ [op] },
           .resolved charge, some (bound entered lv))

/-- One visit inside a pass: the visit's state, and
    the verdict recorded against the candidate's
    input position. -/
noncomputable def vstep [DecidableEq Sym]
    (ctx : Ctx Sym)
    (acc : St Sym × List (Nat × Outcome))
    (ic : Nat × Op Sym) :
    St Sym × List (Nat × Outcome) :=
  let (s', v) := visit ctx ctx.cands acc.1 ic
  (s', acc.2 ++ [(ic.1, v)])

/-- One pass (section 8 step 5): the pool visited in
    the visiting order at the pass's starting graph. -/
noncomputable def pass [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (pool : List (Nat × Op Sym)) :
    St Sym × List (Nat × Outcome) :=
  (isortkey st.g pool).foldl (vstep ctx) (st, [])

/-- The pool a pass leaves for the next: the
    candidates whose verdict in the pass was a
    deferral. -/
def asideof (pool : List (Nat × Op Sym))
    (verdicts : List (Nat × Outcome)) :
    List (Nat × Op Sym) :=
  pool.filter (fun ic =>
    match verdicts.find? (fun p => p.1 = ic.1) with
    | some (_, Outcome.deferred _) => true
    | _ => false)

/-- One sweep of passes (section 8 step 7): passes
    over the pool in the visiting order until a full
    pass resolves nothing new. The fuel is the
    caller's bound; the termination proof below
    shows a fuel of one more than the pool's length
    always reaches the stop. Returns the final
    state, every verdict of every pass in order, the
    pool left at the stop, and whether the stop was
    the stop condition of step 7 rather than the
    fuel running out. -/
noncomputable def sweeps [DecidableEq Sym] (ctx : Ctx Sym) :
    Nat → St Sym → List (Nat × Op Sym) →
      St Sym × List (Nat × Outcome) ×
        List (Nat × Op Sym) × Bool
  | 0, st, pool => (st, [], pool, false)
  | fuel + 1, st, pool =>
      let (st', verdicts) := pass ctx st pool
      let aside := asideof pool verdicts
      if st'.ops.length = st.ops.length then
        (st', verdicts, aside, true)
      else
        let (st'', rest, left, stopped) :=
          sweeps ctx fuel st' aside
        (st'', verdicts ++ rest, left, stopped)

/-- The result record of a run (section 4.4): one
    line per candidate in input order, the target
    line, the total spend, and the budget left —
    carried here with the output graph, the trace,
    and the bound where one was taken. A line's
    outcome is the candidate's last verdict: a
    deferred candidate's reason is the one its final
    pass recorded, which the coverage proof below
    shows still holds at the output graph. -/
structure Result (Sym : Type) where
  lines : List (Nat × Outcome)
  targetline : Outcome
  bound : Option (State Sym)
  spent : Nat
  left : Nat
  out : Graph Sym
  ops : List (Op Sym)

/-- The last verdict recorded for one candidate,
    where one exists. -/
def finalof (verdicts : List (Nat × Outcome))
    (i : Nat) : Option Outcome :=
  match (verdicts.filter (fun p => p.1 = i)).getLast? with
  | some p => some p.2
  | none => none

/-- One run of the algorithm (section 8): validate
    is carried by the claims' validity hypothesis,
    the model having no decidable validity test and
    no repair step; intake; the target recorded;
    sweeps to the stop; and the result record
    closed. At a budget of zero, no test is charged
    or run: every line states deferred with reason
    budget, by presentation alone (step 1). -/
noncomputable def resolve [DecidableEq Sym] (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym) : Result Sym :=
  if budget = 0 then
    { lines := (indexed ctx).map
        (fun ic => (ic.1, Outcome.deferred .budget)),
      targetline := .deferred .budget,
      bound := none,
      spent := 0,
      left := 0,
      out := g,
      ops := [] }
  else
    let (ist, pool, iverdicts) := intake ctx budget g
    let (tst, tout, tb) := targetstep ctx ist
    let (fst, verdicts, _, _) :=
      sweeps ctx (pool.length + 1) tst pool
    let all := iverdicts ++ verdicts
    { lines := (indexed ctx).map (fun ic =>
        (ic.1,
         (finalof all ic.1).getD
           (Outcome.deferred Why.budget))),
      targetline := tout,
      bound := tb,
      spent := fst.spent,
      left := fst.left,
      out := fst.g,
      ops := fst.ops }

/- ## Proofs

   The claims of algorithm.md section 18, in its
   order. Each is stated over this implementation's
   own values. What is proved is proved; what rests
   on a premise carries the premise as a named
   proposition, stated where the claim is. -/

/-- Collection, the boolean and the predicate, agree. -/
theorem collectedb_iff [DecidableEq Sym]
    {g : Graph Sym} {t : Term Sym} :
    collectedb g t = true ↔ collected g t := by
  unfold collectedb collected
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨e, he, ht⟩ := h
    exact ⟨e, he, of_decide_eq_true ht⟩
  · rintro ⟨e, he, ht⟩
    rw [List.any_eq_true]
    exact ⟨e, he, decide_eq_true ht⟩

/-- The counted cost of a record candidate, read off
    the definition. -/
theorem pricerecord [DecidableEq Sym] (g : Graph Sym)
    (lv : Level Sym) (w : Sym) :
    priceof g (.record lv w) =
      some (1 + (lv.terms.filter
        (fun t => !(collectedb g t))).length) := rfl

/-- The counted cost of a paint candidate with no
    cost: its term is not collected. -/
theorem pricepaint [DecidableEq Sym] {g : Graph Sym}
    {t : Term Sym} {c : Color Sym} {l w : Sym}
    (h : priceof g (.paint t c l w) = none) :
    ¬ collected g t := by
  have h2 : priceof g (.paint t c l w) =
      (if collectedb g t then some 1 else none) := rfl
  rw [h2] at h
  intro hcol
  have hb : collectedb g t = true :=
    collectedb_iff.mpr hcol
  simp only [hb, if_true] at h
  exact Option.noConfusion h

/-- The gate a visit applies (section 8 step 5): the
    conditions under which a candidate's operation
    may be applied at a graph — relevance, scope, a
    counted cost, the filter rule, the record rules
    for a record candidate, and the witness check
    where the kind carries one. -/
def Gate [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (op : Op Sym) : Prop :=
  relevant ctx g ctx.cands op = true ∧
  (termsof op).all ctx.scope = true ∧
  (priceof g op).isSome = true ∧
  filterok ctx g op = true ∧
  (∀ lv w, op = .record lv w →
    nameclash g lv = false ∧ recordok lv = true) ∧
  (checkable op = true → ctx.check op = true)

/-- The gate of the target step (section 8 step 4):
    the same record rules and scope test, the bound
    taken in place of relevance (the step's own
    relevance is the target itself), and the witness
    check exactly where the target presents a
    witness. -/
def TGate [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) : Prop :=
  ctx.target.terms.all ctx.scope = true ∧
  nameclash g ctx.target = false ∧
  recordok ctx.target = true ∧
  (∀ w, ctx.twit = some w →
    ctx.check (.record ctx.target w) = true)

/-- A trace of gated steps: from a graph, a list of
    operations each gated at the graph it is applied
    to, reaching the end graph. The list is in
    application order. -/
inductive Steps [DecidableEq Sym] (k : Kinds Sym)
    (gate : Graph Sym → Op Sym → Prop) :
    Graph Sym → Graph Sym → List (Op Sym) → Prop where
  | nil {g : Graph Sym} : Steps k gate g g []
  | step {g h m : Graph Sym} {ops : List (Op Sym)}
      (op : Op Sym) :
      Steps k gate g h ops → gate h op →
      apply k h op = m → Steps k gate g m (ops ++ [op])

/-- A trace reaches exactly the fold of its
    operations over its start graph. -/
theorem stepsrun [DecidableEq Sym] {k : Kinds Sym}
    {gate : Graph Sym → Op Sym → Prop}
    {g h : Graph Sym} {ops : List (Op Sym)}
    (hs : Steps k gate g h ops) : h = run k g ops := by
  induction hs with
  | nil => rfl
  | step _ _ _ happ ih =>
      rw [← happ, ih, runappend]
      rfl

/-- The record condition of an operation: what a
    ready run asks of a record step, and nothing of
    any other kind. It does not depend on the graph;
    it is the standing hypothesis of the model's
    record operation. -/
def condof (op : Op Sym) : Prop :=
  match op with
  | .record level _ => level.terms.Nodup ∧
      ∀ t ∈ level.terms, level.scope t = true
  | _ => True

/-- One operation on a valid graph lands on a valid
    graph, given the record condition where the
    operation is a record. -/
theorem opvalid [DecidableEq Sym] {k : Kinds Sym}
    {g : Graph Sym} (hv : Valid k g) (op : Op Sym)
    (hcond : condof op) :
    Valid k (apply k g op) := by
  cases op with
  | enter t l w => exact entervalid k g hv t l w
  | join a b l w => exact joinvalid k g hv a b l w
  | paint t c l w => exact paintvalid k g hv t c l w
  | record lv w =>
      have h2 : lv.terms.Nodup ∧
          ∀ t ∈ lv.terms, lv.scope t = true := hcond
      exact recordvalid k g hv lv w h2.1 h2.2

/-- Appending one operation to a ready run keeps it
    ready, where the appended operation meets the
    record condition. -/
theorem readysnoc [DecidableEq Sym] {k : Kinds Sym}
    {g : Graph Sym} {ops : List (Op Sym)} {op : Op Sym}
    (hr : Ready k g ops) (hcond : condof op) :
    Ready k g (ops ++ [op]) := by
  induction hr with
  | done valid =>
      exact Ready.more valid op hcond
        (Ready.done (opvalid valid op hcond))
  | more valid op' step' tail ih =>
      exact Ready.more valid op' step' ih

/-- A gated trace on a valid graph is a ready run,
    where the gate supplies the record condition at
    each step. -/
theorem stepsready [DecidableEq Sym] {k : Kinds Sym}
    {gate : Graph Sym → Op Sym → Prop}
    (hgate : ∀ (g : Graph Sym) (op : Op Sym),
      gate g op → ∀ lv w, op = .record lv w →
        lv.terms.Nodup ∧
          ∀ t ∈ lv.terms, lv.scope t = true)
    {g h : Graph Sym} {ops : List (Op Sym)}
    (hv : Valid k g) (hs : Steps k gate g h ops) :
    Ready k g ops := by
  induction hs with
  | nil => exact Ready.done hv
  | step op hs' hg happ ih =>
      apply readysnoc ih
      cases op with
      | record lv w =>
          exact hgate _ _ hg lv w rfl
      | _ => exact trivial

/-- The record condition from the decidable record test. -/
theorem recordokcond [DecidableEq Sym] (lv : Level Sym)
    (w : Sym) (h : recordok lv = true) :
    condof (.record lv w) := by
  unfold recordok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, List.all_eq_true.mp h.2⟩

/-- Gated traces compose, their operation lists appended. -/
theorem stepstrans [DecidableEq Sym] {k : Kinds Sym}
    {gate : Graph Sym → Op Sym → Prop}
    {g h m : Graph Sym} {one two : List (Op Sym)}
    (hs1 : Steps k gate g h one) (hs2 : Steps k gate h m two) :
    Steps k gate g m (one ++ two) := by
  induction hs2 with
  | nil => simpa using hs1
  | step op hs hg happ ih =>
      rw [← List.append_assoc]
      exact Steps.step op ih hg happ

/-- One visit: the budget sum is preserved and the spend
    never falls. -/
theorem visitacct [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) :
    (visit ctx ctx.cands st ic).1.left +
        (visit ctx ctx.cands st ic).1.spent =
      st.left + st.spent ∧
    st.spent ≤ (visit ctx ctx.cands st ic).1.spent := by
  simp only [visit, visit.visitgo]
  repeat' split
  all_goals try simp
  all_goals repeat' split
  all_goals try simp_all
  all_goals try omega
  all_goals simp_all

/-- One visit: either nothing is applied, or exactly the
    candidate's operation is applied through the gate. -/
theorem visitsteps [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) :
    ∃ extra, (visit ctx ctx.cands st ic).1.ops =
        st.ops ++ extra ∧
      Steps ctx.kinds (Gate ctx) st.g
        (visit ctx ctx.cands st ic).1.g extra ∧
      (visit ctx ctx.cands st ic).1.g =
        run ctx.kinds st.g extra := by
  simp only [visit, visit.visitgo]
  repeat' split
  all_goals first
    | exact ⟨[], by simp, Steps.nil, by simp [run]⟩
    | exact ⟨[ic.2], by simp,
        Steps.step ic.2 Steps.nil
          (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [Gate])
          rfl, by simp [run]⟩
    | simp_all

/-- One visit: the spend grows by exactly the resolved
    charge, by one for a witness refusal, or by nothing. -/
theorem visitspent [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) :
    (visit ctx ctx.cands st ic).1.spent =
      st.spent + (match (visit ctx ctx.cands st ic).2 with
        | .resolved c => c
        | .refused .witness _ => 1
        | _ => 0) := by
  simp only [visit, visit.visitgo]
  repeat' split
  all_goals try simp
  all_goals repeat' split
  all_goals try simp_all
  all_goals try omega
  all_goals simp_all

/-- The conditions under which a candidate is not
    resolved at a graph: one of these holds whenever
    its visit does not resolve it. -/
def blocked [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (left : Nat) (op : Op Sym) : Prop :=
  relevant ctx g ctx.cands op = false ∨
  (termsof op).all ctx.scope = false ∨
  priceof g op = none ∨
  filterok ctx g op = false ∨
  (∃ lv w, op = .record lv w ∧
    (nameclash g lv = true ∨ recordok lv = false)) ∨
  (checkable op = true ∧ ctx.check op = false) ∨
  (∃ p, priceof g op = some p ∧
    p + (if checkable op then 1 else 0) > left)

/-- A resolved visit applied exactly its
    candidate. -/
theorem visitresolved [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) (c : Nat)
    (h : (visit ctx ctx.cands st ic).2 =
      .resolved c) :
    (visit ctx ctx.cands st ic).1.ops =
      st.ops ++ [ic.2] := by
  simp only [visit, visit.visitgo] at h ⊢
  repeat' split at h
  all_goals repeat' split
  all_goals simp_all

/-- One visit: a candidate that is not resolved is
    blocked at the graph and budget it was visited at. -/
theorem visitwhy [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym)
    (h : ∀ c, (visit ctx ctx.cands st ic).2 ≠
      .resolved c) :
    blocked ctx st.g st.left ic.2 := by
  simp only [visit, visit.visitgo] at h
  repeat' split at h
  all_goals simp_all [blocked]
  all_goals first
    | (left; simp_all)
    | (right; left; simp_all)
    | (right; right; left; simp_all)
    | (right; right; right; left; simp_all)
    | (right; right; right; right; left; simp_all)
    | (right; right; right; right; right; left; simp_all)
    | (right; right; right; right; right; right; simp_all)

/-- The gate of a run: the visit gate, or the target
    gate for the target's own record operation. -/
def RGate [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (op : Op Sym) : Prop :=
  Gate ctx g op ∨
    (op = .record ctx.target (ctx.twit.getD ctx.target.name) ∧
      TGate ctx g)

/-- The target step: the budget sum is preserved and
    the spend never falls. -/
theorem targetacct [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) :
    (targetstep ctx st).1.left +
        (targetstep ctx st).1.spent =
      st.left + st.spent ∧
    st.spent ≤ (targetstep ctx st).1.spent := by
  simp only [targetstep]
  repeat' split
  all_goals try simp
  all_goals repeat' split
  all_goals try simp_all
  all_goals try omega
  all_goals simp_all

/-- The target step: the spend grows by exactly the
    resolved charge, by one for a witness refusal, or
    by nothing. -/
theorem targetspent [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) :
    (targetstep ctx st).1.spent =
      st.spent + (match (targetstep ctx st).2.1 with
        | .resolved c => c
        | .refused .witness _ => 1
        | _ => 0) := by
  simp only [targetstep]
  repeat' split
  all_goals try simp
  all_goals repeat' split
  all_goals try simp_all
  all_goals try omega
  all_goals simp_all

/-- The operation the target step applies, where it
    applies one. -/
def targetop (ctx : Ctx Sym) : Op Sym :=
  .record ctx.target (ctx.twit.getD ctx.target.name)

/-- The graph the target's bound is read in, where the
    record is applied: the input graph with the
    target's terms entered. -/
noncomputable def entered (ctx : Ctx Sym) (g : Graph Sym) : Graph Sym :=
  enterall ctx.kinds g ctx.target.terms ctx.kinds.record
    (witof (targetop ctx))

/-- The target step as a gated trace, with its bound:
    a repeat at no charge with the bound of the graph
    as it stands, an application of the record through
    the run gate with the bound of the entered graph,
    or no application and no bound. -/
theorem targetsteps [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) :
    ∃ extra, (targetstep ctx st).1.ops = st.ops ++ extra ∧
      Steps ctx.kinds (RGate ctx) st.g
        (targetstep ctx st).1.g extra ∧
      (targetstep ctx st).1.g = run ctx.kinds st.g extra ∧
      (((targetstep ctx st).2.1 = .resolved 0 ∧ extra = []) ∨
        (∃ c, (targetstep ctx st).2.1 = .resolved c ∧
          extra = [targetop ctx]) ∨
        extra = []) := by
  simp only [targetstep, targetop, entered]
  repeat' split
  all_goals first
    | exact ⟨[], by simp, Steps.nil, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨[], by simp, Steps.nil, rfl, Or.inr (Or.inr rfl)⟩
    | (refine ⟨[targetop ctx], ?_, ?_, ?_, ?_⟩
       · exact rfl
       · exact Steps.step (targetop ctx) Steps.nil
           (Or.inr ⟨rfl, by
             refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [TGate]⟩) rfl
       · exact rfl
       · exact Or.inr (Or.inl ⟨_, rfl, rfl⟩))
    | simp_all


/-- The target step's bound: not taken, the bound of
    the graph as it stands at a repeat, or the bound
    of the entered graph at an application. -/
theorem targetbound [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) :
    (targetstep ctx st).2.2 = none ∨
    (targetstep ctx st).2.2 =
      some (bound st.g ctx.target) ∨
    (targetstep ctx st).2.2 =
      some (bound (enterall ctx.kinds st.g ctx.target.terms
        ctx.kinds.record (witof (targetop ctx)))
        ctx.target) := by
  simp only [targetstep, targetop, entered]
  repeat' split
  all_goals first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; exact rfl)
    | (right; right; simp)
    | (right; right; dsimp only; rfl)
    | (right; right; rfl)
    | (right; right; congr; dsimp only; rfl)
    | (right; right; congr)
    | simp_all

/-- The first components of the indexed candidates
    are the input positions. -/
theorem idxfst (ctx : Ctx Sym) :
    (indexed ctx).map Prod.fst =
      List.range ctx.cands.length := by
  unfold indexed
  exact List.map_fst_zip (by simp)

/-- One intake step, as the intake fold applies it. -/
def istept (ctx : Ctx Sym)
    (acc : St Sym × List (Nat × Op Sym) ×
      List (Nat × Outcome)) (ic : Nat × Op Sym) :
    St Sym × List (Nat × Op Sym) ×
      List (Nat × Outcome) :=
  let (st, pool, verdicts) := acc
  if st.left = 0 then
    (st, pool, verdicts ++ [(ic.1, .deferred .budget)])
  else
    let st' := { st with left := st.left - 1,
                         spent := st.spent + 1 }
    if (termsof ic.2).all ctx.scope then
      (st', pool ++ [ic], verdicts)
    else
      (st', pool, verdicts ++ [(ic.1, .deferred .scope)])

/-- The invariant of the intake fold: the graph and
    the trace are untouched, the budget sum is kept,
    the pool is in scope with distinct positions
    disjoint from the positions still to come, the
    verdicts are scope or budget deferrals, and a
    budget deferral means the budget is spent. -/
def invintake (ctx : Ctx Sym) (full : List (Nat × Op Sym))
    (g0 : Graph Sym) (total : Nat)
    (acc : St Sym × List (Nat × Op Sym) ×
      List (Nat × Outcome)) (rest : List (Nat × Op Sym)) :
    Prop :=
  acc.1.g = g0 ∧ acc.1.ops = [] ∧
  acc.1.left + acc.1.spent = total ∧
  (∀ ic ∈ acc.2.1, ic ∈ full ∧
    (termsof ic.2).all ctx.scope = true) ∧
  (acc.2.1.map Prod.fst).Nodup ∧
  (∀ x ∈ acc.2.1, ∀ y ∈ rest, x.1 ≠ y.1) ∧
  (∀ p ∈ acc.2.2, p.2 = .deferred .budget ∨
    (p.2 = .deferred .scope ∧
      ∃ op, (p.1, op) ∈ full ∧
        (termsof op).all ctx.scope = false)) ∧
  ((∃ p ∈ acc.2.2, p.2 = .deferred .budget) →
    acc.1.left = 0) ∧
  (rest.map Prod.fst).Nodup ∧
  (∀ x ∈ rest, x ∈ full)

/-- The intake fold keeps its invariant. -/
theorem intakefold (ctx : Ctx Sym)
    (full : List (Nat × Op Sym)) (g0 : Graph Sym)
    (total : Nat) :
    ∀ (rest : List (Nat × Op Sym))
      (acc : St Sym × List (Nat × Op Sym) ×
        List (Nat × Outcome)),
      invintake ctx full g0 total acc rest →
      invintake ctx full g0 total
        (rest.foldl (istept ctx) acc) [] := by
  intro rest
  induction rest with
  | nil =>
      intro acc h
      obtain ⟨hg, hops, hsum, hpool, hnodup, hdisj,
        hverdict, hbudget, hrestnodup, hrestfull⟩ := h
      refine ⟨hg, hops, hsum, hpool, hnodup, ?_,
        hverdict, hbudget, by simp,
        fun x hx => absurd hx (by simp)⟩
      intro x hx y hy
      exact absurd hy (by simp)
  | cons ic rest ih =>
      intro acc h
      obtain ⟨st, pool, verdicts⟩ := acc
      have hg : st.g = g0 := h.1
      have hops : st.ops = [] := h.2.1
      have hsum : st.left + st.spent = total := h.2.2.1
      have hpool : ∀ x ∈ pool, x ∈ full ∧
          (termsof x.2).all ctx.scope = true := h.2.2.2.1
      have hnodup : (pool.map Prod.fst).Nodup :=
        h.2.2.2.2.1
      have hdisj : ∀ x ∈ pool, ∀ y ∈ ic :: rest,
          x.1 ≠ y.1 := h.2.2.2.2.2.1
      have hverdict : ∀ p ∈ verdicts,
          p.2 = .deferred .budget ∨
          (p.2 = .deferred .scope ∧
            ∃ op, (p.1, op) ∈ full ∧
              (termsof op).all ctx.scope = false) :=
        h.2.2.2.2.2.2.1
      have hbudget : (∃ p ∈ verdicts,
          p.2 = .deferred .budget) → st.left = 0 :=
        h.2.2.2.2.2.2.2.1
      have hrestnodup : ((ic :: rest).map Prod.fst).Nodup :=
        h.2.2.2.2.2.2.2.2.1
      have hrestfull : ∀ x ∈ ic :: rest, x ∈ full :=
        h.2.2.2.2.2.2.2.2.2
      have htailnodup : (rest.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hrestnodup
        exact hrestnodup.2
      have hicnotrest : ic.1 ∉ rest.map Prod.fst := by
        simp only [List.map_cons, List.nodup_cons] at hrestnodup
        exact hrestnodup.1
      have hicfull : ic ∈ full := hrestfull ic (by simp)
      have hrestfull' : ∀ x ∈ rest, x ∈ full :=
        fun x hx => hrestfull x (List.mem_cons_of_mem ic hx)
      have hstep : ((ic :: rest).foldl (istept ctx)
          (st, pool, verdicts)) =
        rest.foldl (istept ctx)
          (istept ctx (st, pool, verdicts) ic) := rfl
      rw [hstep]
      apply ih
      unfold invintake istept
      dsimp only
      by_cases hleft : st.left = 0
      · rw [if_pos hleft]
        refine ⟨hg, hops, hsum, hpool, hnodup, ?_, ?_, ?_,
          htailnodup, hrestfull'⟩
        · intro x hx y hy
          exact hdisj x hx y (List.mem_cons_of_mem ic hy)
        · intro p hp
          simp only [List.mem_append, List.mem_singleton] at hp
          cases hp with
          | inl hp => exact hverdict p hp
          | inr hp => rw [hp]; exact Or.inl rfl
        · intro _
          exact hleft
      · rw [if_neg hleft]
        by_cases hscope : (termsof ic.2).all ctx.scope = true
        · rw [if_pos hscope]
          refine ⟨hg, hops, by dsimp only; omega, ?_, ?_, ?_,
            hverdict, ?_, htailnodup, hrestfull'⟩
          · intro x hx
            simp only [List.mem_append,
              List.mem_singleton] at hx
            cases hx with
            | inl hx => exact hpool x hx
            | inr hx => rw [hx]; exact ⟨hicfull, hscope⟩
          · simp only [List.map_append, List.map_singleton]
            show List.Pairwise (· ≠ ·) _
            rw [List.pairwise_append]
            refine ⟨hnodup, by simp, ?_⟩
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            obtain ⟨x, hxpool, hx1⟩ := List.mem_map.mp ha
            rw [hb, ← hx1]
            exact hdisj x hxpool ic (by simp)
          · intro x hx y hy
            simp only [List.mem_append,
              List.mem_singleton] at hx
            cases hx with
            | inl hx =>
                exact hdisj x hx y
                  (List.mem_cons_of_mem ic hy)
            | inr hx =>
                rw [hx]
                intro hcon
                exact hicnotrest
                  (List.mem_map.mpr ⟨y, hy, hcon.symm⟩)
          · intro hb
            have : st.left = 0 := hbudget hb
            dsimp only
            omega
        · have hscope' : (termsof ic.2).all ctx.scope =
              false := by
            cases h : (termsof ic.2).all ctx.scope with
            | false => rfl
            | true => exact absurd h hscope
          rw [if_neg (by
            intro hcon
            rw [hscope'] at hcon
            exact Bool.noConfusion hcon)]
          refine ⟨hg, hops, by dsimp only; omega, hpool, hnodup, ?_,
            ?_, ?_, htailnodup, hrestfull'⟩
          · intro x hx y hy
            exact hdisj x hx y (List.mem_cons_of_mem ic hy)
          · intro p hp
            simp only [List.mem_append,
              List.mem_singleton] at hp
            cases hp with
            | inl hp => exact hverdict p hp
            | inr hp =>
                rw [hp]
                exact Or.inr ⟨rfl, ic.2, hicfull, hscope'⟩
          · intro hb
            have hb' : ∃ p ∈ verdicts,
                p.2 = .deferred .budget := by
              obtain ⟨p, hp, hp2⟩ := hb
              simp only [List.mem_append,
                List.mem_singleton] at hp
              cases hp with
              | inl hp => exact ⟨p, hp, hp2⟩
              | inr hp =>
                  rw [hp] at hp2
                  exact absurd hp2 (by simp)
            have : st.left = 0 := hbudget hb'
            dsimp only
            omega

/-- Gated traces survive a weakening of the gate. -/
theorem stepsmono [DecidableEq Sym] {k : Kinds Sym}
    {g1 g2 : Graph Sym → Op Sym → Prop}
    (h : ∀ (g : Graph Sym) (op : Op Sym),
      g1 g op → g2 g op)
    {a b : Graph Sym} {ops : List (Op Sym)}
    (hs : Steps k g1 a b ops) : Steps k g2 a b ops := by
  induction hs with
  | nil => exact Steps.nil
  | step op hs hg happ ih =>
      exact Steps.step op ih (h _ _ hg) happ

/-- The run gate supplies the record condition. -/
theorem rgatecond [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (op : Op Sym) (h : RGate ctx g op) :
    condof op := by
  cases h with
  | inl hg =>
      cases op with
      | record lv w =>
          have hr := hg.2.2.2.2.1 lv w rfl
          exact recordokcond lv w hr.2
      | _ => exact trivial
  | inr hg =>
      rw [hg.1]
      exact recordokcond ctx.target _
        hg.2.2.2.1

/-- One visit, by shape: nothing applied, or the
    candidate resolved with exactly its operation
    applied. -/
theorem visitshape [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) :
    ((visit ctx ctx.cands st ic).1.ops = st.ops ∧
      (visit ctx ctx.cands st ic).1.g = st.g) ∨
    (∃ c, (visit ctx ctx.cands st ic).2 = .resolved c ∧
      (visit ctx ctx.cands st ic).1.ops =
        st.ops ++ [ic.2] ∧
      (visit ctx ctx.cands st ic).1.g =
        apply ctx.kinds st.g ic.2) := by
  simp only [visit, visit.visitgo]
  repeat' split
  all_goals first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨_, rfl, rfl, rfl⟩
    | simp_all

/-- Intake, as a fold of intake steps. -/
theorem intakeeq [DecidableEq Sym] (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym) :
    intake ctx budget g =
      (indexed ctx).foldl (istept ctx)
        ({ g := g, left := budget, spent := 0,
           ops := [] }, [], []) := rfl

/-- Intake of a run: the graph and trace untouched,
    the budget sum kept, the pool in scope at distinct
    positions, and only scope or budget deferrals,
    a budget deferral meaning the budget is spent. -/
theorem intakeok [DecidableEq Sym] (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym) :
    (intake ctx budget g).1.g = g ∧
    (intake ctx budget g).1.ops = [] ∧
    (intake ctx budget g).1.left +
        (intake ctx budget g).1.spent = budget ∧
    (∀ ic ∈ (intake ctx budget g).2.1,
      ic ∈ indexed ctx ∧
        (termsof ic.2).all ctx.scope = true) ∧
    ((intake ctx budget g).2.1.map Prod.fst).Nodup ∧
    (∀ p ∈ (intake ctx budget g).2.2,
      p.2 = .deferred .budget ∨
      (p.2 = .deferred .scope ∧
        ∃ op, (p.1, op) ∈ indexed ctx ∧
          (termsof op).all ctx.scope = false)) ∧
    ((∃ p ∈ (intake ctx budget g).2.2,
        p.2 = .deferred .budget) →
      (intake ctx budget g).1.left = 0) := by
  rw [intakeeq]
  have h := intakefold ctx (indexed ctx) g budget
    (indexed ctx)
    ({ g := g, left := budget, spent := 0, ops := [] },
     [], [])
  have hinv : invintake ctx (indexed ctx) g budget
      ({ g := g, left := budget, spent := 0, ops := [] },
       [], []) (indexed ctx) := by
    refine ⟨rfl, rfl, by simp, ?_, by simp, ?_, ?_, ?_,
      ?_, fun x hx => hx⟩
    · intro x hx
      exact absurd hx (by simp)
    · intro x hx y hy
      exact absurd hx (by simp)
    · intro p hp
      exact absurd hp (by simp)
    · intro hb
      obtain ⟨p, hp, _⟩ := hb
      exact absurd hp (by simp)
    · rw [idxfst]
      exact List.nodup_range
  have h2 := h hinv
  obtain ⟨hg, hops, hsum, hpool, hnodup, hdisj,
    hverdict, hbudget, _, _⟩ := h2
  exact ⟨hg, hops, hsum, hpool, hnodup, hverdict,
    hbudget⟩

/-- Whether a verdict is a resolution. -/
def resolvedb (p : Nat × Outcome) : Bool :=
  match p.2 with
  | .resolved _ => true
  | _ => false

/-- A visit's applied list and its verdict agree:
    nothing applied and the verdict not a resolution,
    or exactly its candidate applied and the verdict
    a resolution. -/
theorem visitvex [DecidableEq Sym] (ctx : Ctx Sym)
    (st : St Sym) (ic : Nat × Op Sym) :
    ∀ extra, (visit ctx ctx.cands st ic).1.ops =
        st.ops ++ extra →
      (extra = [] ∧
        resolvedb (ic.1,
          (visit ctx ctx.cands st ic).2) = false) ∨
      (extra = [ic.2] ∧
        resolvedb (ic.1,
          (visit ctx ctx.cands st ic).2) = true) := by
  intro extra hvops
  cases visitshape ctx st ic with
  | inl h =>
      refine Or.inl ⟨?_, ?_⟩
      · have e1 : st.ops ++ extra = st.ops ++ [] := by
          rw [← hvops, h.1]
          simp
        exact (List.append_inj e1 rfl).2
      · cases ho : (visit ctx ctx.cands st ic).2 with
        | resolved c =>
            have hg := visitresolved ctx st ic c ho
            have e2 : st.ops ++ [ic.2] = st.ops := by
              rw [← hg, h.1]
            have e3 := congrArg List.length e2
            simp at e3
        | refused w n => rfl
        | deferred w => rfl
  | inr h =>
      obtain ⟨c, hc, hopsv, hgv⟩ := h
      refine Or.inr ⟨?_, ?_⟩
      · have e1 : st.ops ++ extra =
            st.ops ++ [ic.2] := by
          rw [← hvops, hopsv]
        exact (List.append_inj e1 rfl).2
      · rw [hc]
        rfl

/-- One pass step's verdicts and trace, folded: the
    pass fold lemma. -/
theorem passfold (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ (l : List (Nat × Op Sym))
      (acc : St Sym × List (Nat × Outcome)),
    ∃ extra vs,
      (l.foldl (vstep ctx) acc).1.ops =
        acc.1.ops ++ extra ∧
      Steps ctx.kinds (RGate ctx) acc.1.g
        (l.foldl (vstep ctx) acc).1.g extra ∧
      (l.foldl (vstep ctx) acc).1.g =
        run ctx.kinds acc.1.g extra ∧
      (l.foldl (vstep ctx) acc).1.left +
          (l.foldl (vstep ctx) acc).1.spent =
        acc.1.left + acc.1.spent ∧
      acc.1.spent ≤ (l.foldl (vstep ctx) acc).1.spent ∧
      (l.foldl (vstep ctx) acc).2 = acc.2 ++ vs ∧
      vs.length = l.length ∧
      vs.map Prod.fst = l.map Prod.fst ∧
      extra.length =
        (vs.filter resolvedb).length ∧
      ∀ p ∈ vs, ∃ ic ∈ l, ∃ st',
        p = (ic.1, (visit ctx ctx.cands st' ic).2) ∧
        ∃ pre post vex',
          st'.ops = acc.1.ops ++ pre ∧
          Steps ctx.kinds (RGate ctx) acc.1.g st'.g pre ∧
          (visit ctx ctx.cands st' ic).1.ops =
            st'.ops ++ vex' ∧
          extra = pre ++ vex' ++ post ∧
          (l.foldl (vstep ctx) acc).1.ops =
            (visit ctx ctx.cands st' ic).1.ops ++ post ∧
          st'.left + st'.spent =
            acc.1.left + acc.1.spent ∧
          acc.1.spent ≤ st'.spent ∧
          st'.spent ≤
            (l.foldl (vstep ctx) acc).1.spent := by
  intro l
  induction l with
  | nil =>
      intro acc
      exact ⟨[], [], by simp, Steps.nil, by simp [run],
        rfl, Nat.le_refl _, by simp, rfl, rfl, rfl,
        fun p hp => absurd hp (by simp)⟩
  | cons ic rest ih =>
      intro acc
      obtain ⟨extra1, vs1, hops1, hsteps1, hrun1,
        hsum1, hspent1, hverdicts1, hlen1, hfst1,
        hcount1, hprop1⟩ := ih (vstep ctx acc ic)
      have hv := visitsteps ctx acc.1 ic
      obtain ⟨vex, hvops, hvsteps, hvrun⟩ := hv
      have hvacct := visitacct ctx acc.1 ic
      have hveq : (vstep ctx acc ic).1 =
          (visit ctx ctx.cands acc.1 ic).1 := rfl
      have hveq2 : (vstep ctx acc ic).2 =
          acc.2 ++ [(ic.1,
            (visit ctx ctx.cands acc.1 ic).2)] := rfl
      refine ⟨vex ++ extra1, (ic.1,
          (visit ctx ctx.cands acc.1 ic).2) :: vs1,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have e1 : ((ic :: rest).foldl (vstep ctx) acc).1 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
          rfl
        rw [e1, hops1, hveq, hvops, List.append_assoc]
      · have e1 : ((ic :: rest).foldl (vstep ctx) acc).1 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
          rfl
        rw [e1]
        exact stepstrans
          (stepsmono (fun g op hg => Or.inl hg) hvsteps)
          hsteps1
      · have e1 : ((ic :: rest).foldl (vstep ctx) acc).1 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
          rfl
        rw [e1, hrun1, hveq, hvrun, ← runappend]
      · have e1 : ((ic :: rest).foldl (vstep ctx) acc).1 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
          rfl
        rw [e1]
        have h2 : (vstep ctx acc ic).1.left +
            (vstep ctx acc ic).1.spent =
          acc.1.left + acc.1.spent := by
          rw [hveq]; exact hvacct.1
        omega
      · have e1 : ((ic :: rest).foldl (vstep ctx) acc).1 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
          rfl
        rw [e1]
        have h2 : acc.1.spent ≤
            (vstep ctx acc ic).1.spent := by
          rw [hveq]; exact hvacct.2
        omega
      · have e2 : ((ic :: rest).foldl (vstep ctx) acc).2 =
            (rest.foldl (vstep ctx) (vstep ctx acc ic)).2 :=
          rfl
        simp only [e2, hverdicts1, hveq2, List.append_assoc,
          List.singleton_append]
      · simp [hlen1]
      · simp [hfst1]
      · have hlen2 : (vex ++ extra1).length =
            vex.length +
              (vs1.filter resolvedb).length := by
          rw [List.length_append, hcount1]
        cases visitvex ctx acc.1 ic vex hvops with
        | inl h =>
            have e1 : ((ic.1,
                (visit ctx ctx.cands acc.1 ic).2) ::
                vs1).filter resolvedb =
              vs1.filter resolvedb := by
              simp [List.filter_cons, h.2]
            rw [hlen2, h.1, e1]
            simp only [List.length_nil, Nat.zero_add]
        | inr h =>
            have e1 : (((ic.1,
                (visit ctx ctx.cands acc.1 ic).2) ::
                vs1).filter resolvedb).length =
              (vs1.filter resolvedb).length + 1 := by
              simp [List.filter_cons, h.2]
            rw [hlen2, h.1, e1]
            simp only [List.length_singleton]
            omega
      · intro p hp
        cases List.mem_cons.mp hp with
        | inl hp =>
            refine ⟨ic, by simp, acc.1, hp, [], extra1, vex,
              by simp, Steps.nil, hvops, by simp, ?_,
              rfl, Nat.le_refl _, ?_⟩
            · have e1 : ((ic :: rest).foldl (vstep ctx)
                  acc).1 =
                (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
                rfl
              rw [e1, hops1, hveq, hvops]
            · have e1 : ((ic :: rest).foldl (vstep ctx)
                  acc).1 =
                (rest.foldl (vstep ctx) (vstep ctx acc ic)).1 :=
                rfl
              rw [e1]
              have h2 : (vstep ctx acc ic).1.spent =
                  (visit ctx ctx.cands acc.1 ic).1.spent :=
                rfl
              omega
        | inr hp =>
            obtain ⟨ic', hic', st', hp', pre, post, vex',
              hops', hsteps', hvops', hextra', hfinal',
              hsum', hspent', hspent''⟩ := hprop1 p hp
            refine ⟨ic', by
              exact List.mem_cons_of_mem ic hic', st', hp',
              vex ++ pre, post, vex', ?_, ?_, hvops',
              ?_, hfinal', ?_, ?_, hspent''⟩
            · rw [hops', hveq, hvops, List.append_assoc]
            · exact stepstrans
                (stepsmono (fun g op hg => Or.inl hg)
                  hvsteps) hsteps'
            · simp only [hextra', List.append_assoc]
            · have h2 : (vstep ctx acc ic).1.left +
                  (vstep ctx acc ic).1.spent =
                acc.1.left + acc.1.spent := by
                rw [hveq]; exact hvacct.1
              omega
            · have h2 : acc.1.spent ≤
                  (vstep ctx acc ic).1.spent := by
                rw [hveq]; exact hvacct.2
              omega


/-- A pass, as its fold. -/
theorem passeq (ctx : Ctx Sym) [DecidableEq Sym]
    (st : St Sym) (pool : List (Nat × Op Sym)) :
    pass ctx st pool =
      (isortkey st.g pool).foldl (vstep ctx) (st, []) :=
  rfl

/-- Insertion keeps the visited list a permutation. -/
theorem inskeyperm [DecidableEq Sym] (g : Graph Sym)
    (x : Nat × Op Sym) :
    ∀ l : List (Nat × Op Sym),
    (inskey g x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => simp [inskey]
  | cons y ys ih =>
      unfold inskey
      split
      · simp
      · exact (List.Perm.cons y ih).trans
          (List.Perm.swap x y ys)

/-- The visiting order is a permutation of the pool. -/
theorem isortkeyperm [DecidableEq Sym] (g : Graph Sym) :
    ∀ l : List (Nat × Op Sym),
    (isortkey g l).Perm l := by
  intro l
  induction l with
  | nil => simp [isortkey]
  | cons x xs ih =>
      have h : isortkey g (x :: xs) =
          inskey g x (isortkey g xs) := rfl
      rw [h]
      exact (inskeyperm g x _).trans
        (List.Perm.cons x ih)

/-- Blockedness survives a smaller budget left. -/
theorem blockedmono [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) {l1 l2 : Nat} (h : l2 ≤ l1)
    (op : Op Sym) (hb : blocked ctx g l1 op) :
    blocked ctx g l2 op := by
  obtain h1 | h1 | h1 | h1 | h1 | h1 |
    ⟨p, hp, hgt⟩ := hb
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨p, hp, by omega⟩)))))

/-- Distinct first components make the first
    component determine the pair. -/
theorem nodupfstinj :
    ∀ {l : List (Nat × Op Sym)},
    (l.map Prod.fst).Nodup →
    ∀ {a b : Nat × Op Sym},
    a ∈ l → b ∈ l → a.1 = b.1 → a = b := by
  intro l
  induction l with
  | nil =>
      intro _ a b ha _ _
      exact absurd ha (by simp)
  | cons x xs ih =>
      intro hnd a b ha hb hab
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases List.mem_cons.mp ha with
      | inl hax =>
          cases List.mem_cons.mp hb with
          | inl hbx => rw [hax, hbx]
          | inr hbx =>
              have : b.1 ∈ xs.map Prod.fst :=
                List.mem_map.mpr ⟨b, hbx, rfl⟩
              rw [hax] at hab
              rw [← hab] at this
              exact absurd this hnd.1
      | inr hax =>
          cases List.mem_cons.mp hb with
          | inl hbx =>
              have : a.1 ∈ xs.map Prod.fst :=
                List.mem_map.mpr ⟨a, hax, rfl⟩
              rw [hbx] at hab
              rw [hab] at this
              exact absurd this hnd.1
          | inr hbx => exact ih hnd.2 hax hbx hab

/-- Coverage at the stop of one pass: if the pass
    applied nothing, every candidate of the pool is
    blocked at the pass's output graph and budget. -/
theorem passcover (ctx : Ctx Sym) [DecidableEq Sym]
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hnodup : (pool.map Prod.fst).Nodup)
    (hng : (pass ctx st pool).1.ops.length =
      st.ops.length) :
    ∀ ic ∈ pool,
      blocked ctx (pass ctx st pool).1.g
        (pass ctx st pool).1.left ic.2 := by
  rw [passeq] at hng ⊢
  obtain ⟨extra, vs, hops, hsteps, hrun, hsum, hspent,
    hverdicts, hlen, hfst, hcount, hprop⟩ :=
    passfold ctx (isortkey st.g pool) (st, [])
  have hfinalops : ((isortkey st.g pool).foldl
      (vstep ctx) (st, [])).1.ops = st.ops := by
    have h1 : ((isortkey st.g pool).foldl (vstep ctx)
        (st, [])).1.ops.length = st.ops.length := hng
    rw [hops] at h1
    simp only [List.length_append, List.length_nil] at h1
    have h2 : extra.length = 0 := by omega
    have h3 : extra = [] := List.length_eq_zero_iff.mp h2
    rw [hops, h3]
    simp
  have hfinalg : ((isortkey st.g pool).foldl
      (vstep ctx) (st, [])).1.g = st.g := by
    have h3 : extra = [] := by
      have h1 : ((isortkey st.g pool).foldl (vstep ctx)
          (st, [])).1.ops.length = st.ops.length := hng
      rw [hops] at h1
      simp only [List.length_append] at h1
      have h2 : extra.length = 0 := by omega
      exact List.length_eq_zero_iff.mp h2
    rw [hrun, h3]
    simp [run]
  intro ic hic
  have hicsorted : ic ∈ isortkey st.g pool :=
    (isortkeyperm st.g pool).mem_iff.mpr hic
  have hicfst : ic.1 ∈ vs.map Prod.fst := by
    rw [hfst]
    exact List.mem_map.mpr ⟨ic, hicsorted, rfl⟩
  obtain ⟨p, hpvs, hpfst⟩ := List.mem_map.mp hicfst
  have hpform : p = (ic.1, p.2) := by
    cases p with
    | mk a b => simp at hpfst; rw [hpfst]
  obtain ⟨ic', hic'1, st', hp', pre, post, vex',
    hops'', hsteps'', hvops'', hextra, hfinal',
    hsum'', hspent'', hspent'''⟩ := hprop p hpvs
  have hic'pool : ic' ∈ pool :=
    (isortkeyperm st.g pool).mem_iff.mp hic'1
  have hiceq : ic' = ic := by
    apply nodupfstinj hnodup hic'pool hic
    have h2 : p.1 = ic.1 := hpfst
    rw [hp'] at h2
    exact h2
  rw [hiceq] at hp' hvops'' hfinal'
  have hnotres : ∀ c, (visit ctx ctx.cands st' ic).2 ≠
      .resolved c := by
    intro c hc
    have hgrown := visitresolved ctx st' ic c hc
    have hfinlen : ((isortkey st.g pool).foldl
        (vstep ctx) (st, [])).1.ops.length =
      st'.ops.length + 1 + post.length := by
      rw [hfinal', hgrown]
      simp only [List.length_append,
        List.length_singleton]
    rw [hfinalops] at hfinlen
    have hpre : st'.ops.length =
        st.ops.length + pre.length := by
      rw [hops'']
      simp [List.length_append]
    omega
  have hb := visitwhy ctx st' ic hnotres
  have hge : ((isortkey st.g pool).foldl
      (vstep ctx) (st, [])).1.g = st'.g := by
    have hr2 : run ctx.kinds st.g pre = st'.g := by
      have h := stepsrun hsteps''
      rw [h]
    have hvexrun : run ctx.kinds st'.g vex' =
        (visit ctx ctx.cands st' ic).1.g := by
      obtain ⟨vex2, hvops2, hvsteps2, hvrun2⟩ :=
        visitsteps ctx st' ic
      have hvexeq : vex2 = vex' := by
        have e1 : st'.ops ++ vex2 =
            st'.ops ++ vex' := by
          rw [← hvops2, ← hvops'']
        exact (List.append_inj e1 rfl).2
      rw [hvexeq] at hvrun2
      exact hvrun2.symm
    have hfinrun : ((isortkey st.g pool).foldl
        (vstep ctx) (st, [])).1.g =
        run ctx.kinds
          (visit ctx ctx.cands st' ic).1.g post := by
      rw [hrun, hextra, runappend, runappend, hr2,
        hvexrun]
    have hpostlen : post.length = 0 := by
      have hfinlen : ((isortkey st.g pool).foldl
          (vstep ctx) (st, [])).1.ops.length =
        (visit ctx ctx.cands st' ic).1.ops.length +
          post.length := by
        rw [hfinal']
        simp [List.length_append]
      have hvisitlen : (visit ctx ctx.cands st' ic).1.ops.length
          ≥ st'.ops.length := by
        rw [hvops'']
        simp [List.length_append]
      have hpre : st'.ops.length =
          st.ops.length + pre.length := by
        rw [hops'']
        simp [List.length_append]
      rw [hfinalops] at hfinlen
      omega
    have hpostnil : post = [] :=
      List.length_eq_zero_iff.mp hpostlen
    rw [hpostnil] at hfinrun
    simp only [run, List.foldl_nil] at hfinrun
    rw [hfinrun]
    have hshape := visitshape ctx st' ic
    cases hshape with
    | inl h => exact h.2
    | inr h =>
        obtain ⟨c, hc, _, _⟩ := h
        exact absurd hc (hnotres c)
  have hleftle : ((isortkey st.g pool).foldl
      (vstep ctx) (st, [])).1.left ≤ st'.left := by
    have hsumfin : ((isortkey st.g pool).foldl
        (vstep ctx) (st, [])).1.left +
        ((isortkey st.g pool).foldl (vstep ctx)
          (st, [])).1.spent = st.left + st.spent := hsum
    omega
  rw [← hge] at hb
  exact blockedmono ctx _ hleftle ic.2 hb

/-- One step of the sweeps, unfolded. -/
theorem sweepseq (ctx : Ctx Sym) [DecidableEq Sym]
    (fuel : Nat) (st : St Sym)
    (pool : List (Nat × Op Sym)) :
    sweeps ctx (fuel + 1) st pool =
      let (st', verdicts) := pass ctx st pool
      let aside := asideof pool verdicts
      if st'.ops.length = st.ops.length then
        (st', verdicts, aside, true)
      else
        let (st'', rest, left, stopped) :=
          sweeps ctx fuel st' aside
        (st'', verdicts ++ rest, left, stopped) := rfl

/-- A stopping sweep step: the state is the pass's
    state, and the stop flag is set. -/
theorem sweepsone (ctx : Ctx Sym) [DecidableEq Sym]
    (fuel : Nat) (st : St Sym)
    (pool : List (Nat × Op Sym))
    (hstop : (pass ctx st pool).1.ops.length =
      st.ops.length) :
    (sweeps ctx (fuel + 1) st pool).1 =
      (pass ctx st pool).1 ∧
    (sweeps ctx (fuel + 1) st pool).2.2.2 = true := by
  rw [sweepseq]
  constructor
  · dsimp only
    rw [if_pos hstop]
  · dsimp only
    rw [if_pos hstop]

/-- A growing sweep step recurses on the aside pool
    at the pass's state. -/
theorem sweepsmore (ctx : Ctx Sym) [DecidableEq Sym]
    (fuel : Nat) (st : St Sym)
    (pool : List (Nat × Op Sym))
    (hstop : (pass ctx st pool).1.ops.length ≠
      st.ops.length) :
    (sweeps ctx (fuel + 1) st pool).1 =
      (sweeps ctx fuel (pass ctx st pool).1
        (asideof pool (pass ctx st pool).2)).1 ∧
    (sweeps ctx (fuel + 1) st pool).2.2.2 =
      (sweeps ctx fuel (pass ctx st pool).1
        (asideof pool (pass ctx st pool).2)).2.2.2 := by
  rw [sweepseq]
  constructor
  · dsimp only
    rw [if_neg hstop]
  · dsimp only
    rw [if_neg hstop]

/-- The sweeps, folded: the final state is reached by
    one gated trace from the start, the budget sum is
    kept, and the spend never falls. -/
theorem sweepsfold (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ (fuel : Nat) (st : St Sym)
      (pool : List (Nat × Op Sym)),
    ∃ extra,
      (sweeps ctx fuel st pool).1.ops =
        st.ops ++ extra ∧
      Steps ctx.kinds (RGate ctx) st.g
        (sweeps ctx fuel st pool).1.g extra ∧
      (sweeps ctx fuel st pool).1.g =
        run ctx.kinds st.g extra ∧
      (sweeps ctx fuel st pool).1.left +
        (sweeps ctx fuel st pool).1.spent =
          st.left + st.spent ∧
      st.spent ≤
        (sweeps ctx fuel st pool).1.spent := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pool
      refine ⟨[], ?_, Steps.nil, ?_, rfl,
        Nat.le_refl _⟩
      · simp [sweeps]
      · simp [sweeps, run]
  | succ fuel ih =>
      intro st pool
      obtain ⟨extra1, vs, hops1, hsteps1, hrun1,
        hsum1, hspent1, hverdicts1, hlen1, hfst1,
        hcount1, hprop1⟩ :=
        passfold ctx (isortkey st.g pool) (st, [])
      have hops1' : (pass ctx st pool).1.ops =
          st.ops ++ extra1 := hops1
      have hsteps1' : Steps ctx.kinds (RGate ctx)
          st.g (pass ctx st pool).1.g extra1 := hsteps1
      have hrun1' : (pass ctx st pool).1.g =
          run ctx.kinds st.g extra1 := hrun1
      have hsum1' : (pass ctx st pool).1.left +
          (pass ctx st pool).1.spent =
        st.left + st.spent := hsum1
      have hspent1' : st.spent ≤
          (pass ctx st pool).1.spent := hspent1
      by_cases hstop : (pass ctx st pool).1.ops.length =
          st.ops.length
      · obtain ⟨h1, -⟩ := sweepsone ctx fuel st pool
          hstop
        refine ⟨extra1, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1]; exact hops1'
        · rw [h1]; exact hsteps1'
        · rw [h1]; exact hrun1'
        · rw [h1]; exact hsum1'
        · rw [h1]; exact hspent1'
      · obtain ⟨h1, -⟩ := sweepsmore ctx fuel st pool
          hstop
        obtain ⟨extra2, h2ops, h2steps, h2run, h2sum,
          h2spent⟩ := ih (pass ctx st pool).1
          (asideof pool (pass ctx st pool).2)
        refine ⟨extra1 ++ extra2, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1, h2ops, hops1', List.append_assoc]
        · rw [h1]
          exact stepstrans hsteps1' h2steps
        · rw [h1, h2run, hrun1', runappend]
        · rw [h1]
          omega
        · rw [h1]
          omega

/-- A search by first component finds the unique
    entry with that component. -/
theorem findunique :
    ∀ {l : List (Nat × Outcome)},
    (l.map Prod.fst).Nodup →
    ∀ {p : Nat × Outcome}, p ∈ l →
    l.find? (fun q => q.1 = p.1) = some p := by
  intro l
  induction l with
  | nil =>
      intro _ p hp
      simp at hp
  | cons x xs ih =>
      intro hnd p hp
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases List.mem_cons.mp hp with
      | inl h =>
          subst h
          simp [List.find?]
      | inr h =>
          have hne : ¬ (x.1 = p.1) := by
            intro he
            have hmem : p.1 ∈ xs.map Prod.fst :=
              List.mem_map.mpr ⟨p, h, rfl⟩
            rw [← he] at hmem
            exact hnd.1 hmem
          have hfind : (x :: xs).find?
              (fun q => q.1 = p.1) =
            xs.find? (fun q => q.1 = p.1) := by
            simp [List.find?, hne]
          rw [hfind]
          exact ih hnd.2 h

/-- A pass that grows the trace leaves a strictly
    smaller aside pool: some candidate resolved, and a
    resolved candidate is not set aside. -/
theorem asidelt (ctx : Ctx Sym) [DecidableEq Sym]
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hnodup : (pool.map Prod.fst).Nodup)
    (hng : (pass ctx st pool).1.ops.length ≠
      st.ops.length) :
    (asideof pool (pass ctx st pool).2).length <
      pool.length := by
  obtain ⟨extra, vs, hops, hsteps, hrun, hsum, hspent,
    hverdicts, hlen, hfst, hcount, hprop⟩ :=
    passfold ctx (isortkey st.g pool) (st, [])
  have hops' : (pass ctx st pool).1.ops =
      st.ops ++ extra := hops
  have hverdicts' : (pass ctx st pool).2 = vs :=
    hverdicts
  rw [hverdicts']
  have hex : 0 < extra.length := by
    cases Nat.eq_zero_or_pos extra.length with
    | inr h => exact h
    | inl h =>
        have h0 : extra = [] :=
          List.length_eq_zero_iff.mp h
        rw [hops', h0] at hng
        simp at hng
  have hfil : 0 < (vs.filter resolvedb).length := by
    rw [← hcount]; exact hex
  have hne : vs.filter resolvedb ≠ [] := by
    intro h0
    rw [h0] at hfil
    simp at hfil
  obtain ⟨p, hp⟩ : ∃ p, p ∈ vs.filter resolvedb := by
    cases h : vs.filter resolvedb with
    | nil => exact absurd h hne
    | cons q qs =>
        exact ⟨q, List.mem_cons_self⟩
  obtain ⟨hpvs, hpres⟩ := List.mem_filter.mp hp
  obtain ⟨ic, hic1, st', hp', -⟩ := hprop p hpvs
  have hicpool : ic ∈ pool :=
    (isortkeyperm st.g pool).mem_iff.mp hic1
  rw [hp'] at hpres
  have hres2 : ∃ c, (visit ctx ctx.cands st' ic).2 =
      .resolved c := by
    cases ho : (visit ctx ctx.cands st' ic).2 with
    | resolved c => exact ⟨c, rfl⟩
    | refused w n =>
        have h2 : resolvedb (ic.1,
            (visit ctx ctx.cands st' ic).2) =
          false := by
          rw [ho]
          rfl
        rw [h2] at hpres
        exact absurd hpres (by simp)
    | deferred w =>
        have h2 : resolvedb (ic.1,
            (visit ctx ctx.cands st' ic).2) =
          false := by
          rw [ho]
          rfl
        rw [h2] at hpres
        exact absurd hpres (by simp)
  obtain ⟨c, hc⟩ := hres2
  have hpfind : vs.find? (fun q => q.1 = ic.1) =
      some p := by
    have hpeq : p.1 = ic.1 := by simp [hp']
    rw [← hpeq]
    apply findunique _ hpvs
    have hperm := (isortkeyperm st.g pool).map Prod.fst
    have hnd : ((isortkey st.g pool).map
        Prod.fst).Nodup :=
      hperm.nodup_iff.mpr hnodup
    rwa [← hfst] at hnd
  have hnotaside : ic ∉ asideof pool vs := by
    intro hmem
    have hcond := (List.mem_filter.mp hmem).2
    rw [hpfind, hp', hc] at hcond
    simp at hcond
  have hsub : (asideof pool vs).Sublist pool :=
    List.filter_sublist
  have hle := hsub.length_le
  cases Nat.lt_or_ge (asideof pool vs).length
      pool.length with
  | inl h => exact h
  | inr hge =>
      have heq : asideof pool vs = pool :=
        hsub.eq_of_length (by omega)
      have hmem : ic ∈ asideof pool vs := by
        rw [heq]
        exact hicpool
      exact (hnotaside hmem).elim

/-- Termination: at a fuel of one more than the
    pool's length, the sweeps reach the stop. -/
theorem sweepsstop (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ (n : Nat) (fuel : Nat) (st : St Sym)
      (pool : List (Nat × Op Sym)),
    (pool.map Prod.fst).Nodup →
    pool.length ≤ n → n + 1 ≤ fuel →
    (sweeps ctx fuel st pool).2.2.2 = true := by
  intro n
  induction n with
  | zero =>
      intro fuel st pool hnodup hlen hfuel
      have hpool : pool = [] := by
        have h0 : pool.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h0
      subst hpool
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ fuel =>
          have hstop : (pass ctx st []).1.ops.length =
              st.ops.length := by
            simp [pass, isortkey]
          exact (sweepsone ctx fuel st [] hstop).2
  | succ n ih =>
      intro fuel st pool hnodup hlen hfuel
      cases fuel with
      | zero => exact absurd hfuel (by simp)
      | succ fuel =>
          by_cases hstop :
              (pass ctx st pool).1.ops.length =
                st.ops.length
          · exact (sweepsone ctx fuel st pool hstop).2
          · have h2 := (sweepsmore ctx fuel st pool
              hstop).2
            rw [h2]
            apply ih fuel _ _ _ _ _
            · have hsub : (asideof pool
                  (pass ctx st pool).2).Sublist pool :=
                List.filter_sublist
              exact ((hsub.map Prod.fst).nodup hnodup)
            · have hlt := asidelt ctx st pool hnodup
                hstop
              omega
            · omega

/- ## The claims of algorithm.md section 18, in its
   order, stated over this implementation's own
   values and proved from the step lemmas. -/

/-- The run, decomposed: the output graph is reached
    from the input graph by one gated trace, it is
    the fold of that trace, and the record's trace is
    that trace. -/
theorem runsteps (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) :
    ∃ ops, Steps ctx.kinds (RGate ctx) g
        (resolve ctx budget g).out ops ∧
      (resolve ctx budget g).out =
        run ctx.kinds g ops ∧
      (resolve ctx budget g).ops = ops := by
  by_cases hb : budget = 0
  · have hout : (resolve ctx budget g).out = g := by
      simp [resolve, hb]
    have hops : (resolve ctx budget g).ops = [] := by
      simp [resolve, hb]
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [hout]; exact Steps.nil
    · rw [hout]; simp [run]
    · exact hops
  · have hout : (resolve ctx budget g).out =
        (sweeps ctx ((intake ctx budget g).2.1.length
          + 1)
          (targetstep ctx (intake ctx budget g).1).1
          (intake ctx budget g).2.1).1.g := by
      simp only [resolve, if_neg hb]
    have hops : (resolve ctx budget g).ops =
        (sweeps ctx ((intake ctx budget g).2.1.length
          + 1)
          (targetstep ctx (intake ctx budget g).1).1
          (intake ctx budget g).2.1).1.ops := by
      simp only [resolve, if_neg hb]
    obtain ⟨hg, hops0, -, -, -, -, -⟩ :=
      intakeok ctx budget g
    obtain ⟨extrat, htops, htsteps, htrun, -⟩ :=
      targetsteps ctx (intake ctx budget g).1
    obtain ⟨extras, hsops, hssteps, hsrun, -, -⟩ :=
      sweepsfold ctx
        ((intake ctx budget g).2.1.length + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1
    have hsteps : Steps ctx.kinds (RGate ctx) g
        (resolve ctx budget g).out
        (extrat ++ extras) := by
      rw [hout]
      rw [hg] at htsteps
      exact stepstrans htsteps hssteps
    refine ⟨extrat ++ extras, hsteps, stepsrun hsteps,
      ?_⟩
    · rw [hops, hsops, htops, hops0]
      simp [List.append_assoc]

/-- Claim one, soundness of output: a run on a valid
    graph produces a valid output graph, and the
    growth relation holds from the input to the
    output. -/
theorem claimone (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym)
    (hv : Valid ctx.kinds g) :
    Valid ctx.kinds (resolve ctx budget g).out ∧
    Growth ctx.kinds g (resolve ctx budget g).out := by
  obtain ⟨ops, hsteps, hrun, -⟩ := runsteps ctx budget g
  have hready : Ready ctx.kinds g ops :=
    stepsready (fun g' op hg lv w hop => by
      have hc := rgatecond ctx g' op hg
      rw [hop] at hc
      exact hc) hv hsteps
  constructor
  · rw [hrun]; exact runvalid ctx.kinds hready
  · rw [hrun]; exact rungrows ctx.kinds hready

/-- Claim two, one graph only: the one graph value a
    run produces is its output graph, reached by
    operations on the running graph alone; every
    other produced value is a state, a list, or a
    record field. The formal content here is the
    decomposition itself. -/
theorem claimtwo (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) :
    ∃ ops, (resolve ctx budget g).out =
        run ctx.kinds g ops ∧
      Steps ctx.kinds (RGate ctx) g
        (resolve ctx budget g).out ops := by
  obtain ⟨ops, hs, hr, -⟩ := runsteps ctx budget g
  exact ⟨ops, hr, hs⟩

/-- Every operation a run applies has all its terms
    in the effective scope at its step: the gate's
    scope clause, for the target's record by its own
    gate. -/
theorem stepsscope (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ {g h : Graph Sym} {ops : List (Op Sym)},
    Steps ctx.kinds (RGate ctx) g h ops →
    ∀ op ∈ ops, (termsof op).all ctx.scope = true := by
  intro g h ops hs
  induction hs with
  | nil =>
      intro op hop
      simp at hop
  | step op hs' hg happ ih =>
      intro op' hop'
      rw [List.mem_append, List.mem_singleton] at hop'
      cases hop' with
      | inl h => exact ih op' h
      | inr h =>
          subst h
          cases hg with
          | inl hg => exact hg.2.1
          | inr hg =>
              rw [hg.1]
              exact hg.2.1

/-- Claim three, scope soundness: in every run,
    every term a step of the run operates on
    satisfies the effective scope at the moment of
    the step (the implementation's gate makes the
    scope clause unconditional, which is the
    statement's first alternative strengthened: no
    term outside the effective scope is admitted,
    joined, recorded, or painted by the run). -/
theorem claimthree (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) :
    ∀ op ∈ (resolve ctx budget g).ops,
      (termsof op).all ctx.scope = true := by
  obtain ⟨ops, hsteps, -, hops⟩ := runsteps ctx budget g
  rw [hops] at *
  exact fun op hop => stepsscope ctx hsteps op hop

/-- Claim four, determinism: the procedure is a
    function of its inputs; equal inputs give equal
    result records, output graphs, and traces. The
    fixed visiting order is in the construction
    (the visiting key and the sweeps), and each
    operation of the model is a function. -/
theorem claimfour (ctx ctx' : Ctx Sym)
    [DecidableEq Sym] (budget budget' : Nat)
    (g g' : Graph Sym)
    (h1 : ctx = ctx') (h2 : budget = budget')
    (h3 : g = g') :
    resolve ctx budget g = resolve ctx' budget' g' := by
  rw [h1, h2, h3]

/-- Claim five, termination: the sweeps of a run
    reach the stop, at the fuel the run itself takes
    (one more than the pool's length). -/
theorem claimfive (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym)
    (_hb : budget ≠ 0) :
    (sweeps ctx ((intake ctx budget g).2.1.length + 1)
      (targetstep ctx (intake ctx budget g).1).1
      (intake ctx budget g).2.1).2.2.2 = true := by
  obtain ⟨-, -, -, -, hnodup, -, -⟩ :=
    intakeok ctx budget g
  exact sweepsstop ctx
    ((intake ctx budget g).2.1.length)
    ((intake ctx budget g).2.1.length + 1)
    (targetstep ctx (intake ctx budget g).1).1
    (intake ctx budget g).2.1
    hnodup (Nat.le_refl _) (Nat.le_refl _)

/-- Coverage inside the sweeps: if the sweeps stop,
    every candidate in the pool they leave is blocked
    at the final state. -/
theorem sweepscover (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ (fuel : Nat) (st : St Sym)
      (pool : List (Nat × Op Sym)),
    (pool.map Prod.fst).Nodup →
    (sweeps ctx fuel st pool).2.2.2 = true →
    ∀ ic ∈ (sweeps ctx fuel st pool).2.2.1,
      blocked ctx (sweeps ctx fuel st pool).1.g
        (sweeps ctx fuel st pool).1.left ic.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pool hnodup hstop
      simp [sweeps] at hstop
  | succ fuel ih =>
      intro st pool hnodup hstop ic hic
      by_cases hstop' :
          (pass ctx st pool).1.ops.length =
            st.ops.length
      · obtain ⟨h1, -⟩ := sweepsone ctx fuel st pool
          hstop'
        have hpool2 : (sweeps ctx (fuel + 1) st
            pool).2.2.1 =
          asideof pool (pass ctx st pool).2 := by
          rw [sweepseq]
          dsimp only
          rw [if_pos hstop']
        rw [hpool2] at hic
        have hicpool : ic ∈ pool :=
          (List.mem_filter.mp hic).1
        have hb := passcover ctx st pool hnodup
          hstop' ic hicpool
        rw [← h1] at hb
        exact hb
      · obtain ⟨h1, h2⟩ := sweepsmore ctx fuel st pool
          hstop'
        have hpool2 : (sweeps ctx (fuel + 1) st
            pool).2.2.1 =
          (sweeps ctx fuel (pass ctx st pool).1
            (asideof pool (pass ctx st pool).2)).2.2.1 :=
          by
          rw [sweepseq]
          dsimp only
          rw [if_neg hstop']
        rw [hpool2] at hic
        have hstop2 : (sweeps ctx fuel
            (pass ctx st pool).1
            (asideof pool (pass ctx st pool).2)).2.2.2 =
          true := by
          rw [← h2]
          exact hstop
        have hnodup2 : ((asideof pool
            (pass ctx st pool).2).map Prod.fst).Nodup :=
          (List.filter_sublist.map Prod.fst).nodup
            hnodup
        have hb := ih (pass ctx st pool).1
          (asideof pool (pass ctx st pool).2)
          hnodup2 hstop2 ic hic
        rw [← h1] at hb
        exact hb

/-- Claim six, coverage at the stop: every candidate
    the run's sweeps leave in their final pool is
    blocked at the output graph and the budget left:
    it fails relevance, scope, collection, the filter
    rule, or a record rule, or its whole charge
    exceeds the budget left (the least cost clause:
    the charge read at the output graph). -/
theorem claimsix (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) (hb : budget ≠ 0) :
    ∀ ic ∈ (sweeps ctx
        ((intake ctx budget g).2.1.length + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1).2.2.1,
      blocked ctx (resolve ctx budget g).out
        (resolve ctx budget g).left ic.2 := by
  have hstop := claimfive ctx budget g hb
  obtain ⟨-, -, -, -, hnodup, -, -⟩ :=
    intakeok ctx budget g
  have hb2 := sweepscover ctx
    ((intake ctx budget g).2.1.length + 1)
    (targetstep ctx (intake ctx budget g).1).1
    (intake ctx budget g).2.1 hnodup hstop
  intro ic hic
  have h := hb2 ic hic
  have hout : (resolve ctx budget g).out =
      (sweeps ctx ((intake ctx budget g).2.1.length
        + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1).1.g := by
    simp only [resolve, if_neg hb]
  have hleft : (resolve ctx budget g).left =
      (sweeps ctx ((intake ctx budget g).2.1.length
        + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1).1.left := by
    simp only [resolve, if_neg hb]
  rw [← hout, ← hleft] at h
  exact h

/-- A counted cost, where one exists, is at least
    one. -/
theorem pricepos (_ctx : Ctx Sym) [DecidableEq Sym]
    (g : Graph Sym) (op : Op Sym) (p : Nat)
    (h : priceof g op = some p) : 1 ≤ p := by
  cases op with
  | enter t l w => simp [priceof] at h; omega
  | join a b l w => simp [priceof] at h; omega
  | paint t c l w =>
      simp only [priceof] at h
      split at h
      · simp only [Option.some.injEq] at h; omega
      · simp at h
  | record lv w => simp [priceof] at h; omega

/-- Every verdict intake leaves carries the index of
    an indexed candidate. -/
theorem foldidx (ctx : Ctx Sym)
    (full : List (Nat × Op Sym)) :
    ∀ (l : List (Nat × Op Sym))
      (acc : St Sym × List (Nat × Op Sym) ×
        List (Nat × Outcome)),
    (∀ q ∈ l, q ∈ full) →
    (∀ p ∈ acc.2.2, ∃ op, (p.1, op) ∈ full) →
    ∀ p ∈ (List.foldl (istept ctx) acc l).2.2,
      ∃ op, (p.1, op) ∈ full := by
  intro l
  induction l with
  | nil =>
      intro acc _ hbase p hp
      exact hbase p hp
  | cons ic l ih =>
      intro acc hsub hbase p hp
      have hstep : ∀ q ∈ (istept ctx acc ic).2.2,
          ∃ op, (q.1, op) ∈ full := by
        intro q hq
        unfold istept at hq
        repeat' split at hq
        all_goals first
          | exact hbase q hq
          | (rw [List.mem_append,
                List.mem_singleton] at hq
             cases hq with
             | inl h => exact hbase q h
             | inr h =>
                 rw [h]
                 exact ⟨ic.2, hsub ic
                   List.mem_cons_self⟩)
      exact ih (istept ctx acc ic)
        (fun q hq => hsub q
          (List.mem_cons_of_mem _ hq)) hstep p hp

/-- Intake's verdicts, indexed. -/
theorem intakeidx (ctx : Ctx Sym) (budget : Nat)
    (g : Graph Sym) :
    ∀ p ∈ (intake ctx budget g).2.2,
      ∃ op, (p.1, op) ∈ indexed ctx := by
  rw [intakeeq]
  exact foldidx ctx (indexed ctx) (indexed ctx)
    ((St.mk g budget 0 []), [], [])
    (fun q hq => hq)
    (by intro q hq; simp at hq)

/-- Claim six, the intake clauses: a candidate
    deferred at intake for scope is blocked at any
    graph (the scope test is graph independent), and
    a candidate deferred at intake for budget is
    blocked at the run's output, where the budget
    left is zero. -/
theorem claimsixintake (ctx : Ctx Sym)
    [DecidableEq Sym] (budget : Nat) (g : Graph Sym)
    (hb : budget ≠ 0) :
    (∀ p ∈ (intake ctx budget g).2.2,
      p.2 = .deferred .scope →
      ∃ op, (p.1, op) ∈ indexed ctx ∧
        blocked ctx (resolve ctx budget g).out
          (resolve ctx budget g).left op) ∧
    (∀ p ∈ (intake ctx budget g).2.2,
      p.2 = .deferred .budget →
      ∃ op, (p.1, op) ∈ indexed ctx ∧
        blocked ctx (resolve ctx budget g).out
          (resolve ctx budget g).left op) := by
  obtain ⟨hg, hops0, hsum, hpool, hnodup, hverdict,
    hbudget⟩ := intakeok ctx budget g
  have hleftle : (resolve ctx budget g).left ≤
      (intake ctx budget g).1.left := by
    have hleft : (resolve ctx budget g).left =
        (sweeps ctx ((intake ctx budget g).2.1.length
          + 1)
          (targetstep ctx (intake ctx budget g).1).1
          (intake ctx budget g).2.1).1.left := by
      simp only [resolve, if_neg hb]
    have htacct := targetacct ctx
      (intake ctx budget g).1
    obtain ⟨-, -, -, hsum2, hspent2⟩ := sweepsfold ctx
      ((intake ctx budget g).2.1.length + 1)
      (targetstep ctx (intake ctx budget g).1).1
      (intake ctx budget g).2.1
    rw [hleft]
    omega
  constructor
  · intro p hp hpscope
    have hv := hverdict p hp
    cases hv with
    | inl h => rw [h] at hpscope; simp at hpscope
    | inr h =>
        obtain ⟨h2, op, hop, hscope⟩ := h
        refine ⟨op, hop, ?_⟩
        exact Or.inr (Or.inl hscope)
  · intro p hp hpbudget
    have hleft0 : (intake ctx budget g).1.left = 0 :=
      hbudget ⟨p, hp, hpbudget⟩
    have hleftrun : (resolve ctx budget g).left =
        0 := by
      omega
    obtain ⟨op, hop⟩ := intakeidx ctx budget g p hp
    refine ⟨op, hop, ?_⟩
    cases hprice : priceof (resolve ctx budget g).out
        op with
    | none =>
        exact Or.inr (Or.inr (Or.inl hprice))
    | some pr =>
        have hpr := pricepos ctx _ op pr hprice
        refine Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr ⟨pr, hprice, ?_⟩)))))
        rw [hleftrun]
        omega

/-- The resumption engine of claim fifteen: a
    candidate whose gate holds at a graph and whose
    whole charge fits the budget left is resolved by
    its visit at that graph, applying its operation. -/
theorem visitresolves (ctx : Ctx Sym)
    [DecidableEq Sym] (st : St Sym)
    (ic : Nat × Op Sym) (hg : Gate ctx st.g ic.2)
    (ch : Nat) (hch : chargeof st.g ic.2 = some ch)
    (hle : ch ≤ st.left) :
    (visit ctx ctx.cands st ic).2 = .resolved ch ∧
    (visit ctx ctx.cands st ic).1.g =
      apply ctx.kinds st.g ic.2 ∧
    (visit ctx ctx.cands st ic).1.ops =
      st.ops ++ [ic.2] := by
  obtain ⟨p, hp, hpeq⟩ : ∃ p, priceof st.g ic.2 =
      some p ∧ ch = p +
        (if checkable ic.2 then 1 else 0) := by
    cases hp2 : priceof st.g ic.2 with
    | none =>
        exfalso
        rw [chargeof, hp2] at hch
        simp at hch
    | some p =>
        refine ⟨p, rfl, ?_⟩
        rw [chargeof, hp2] at hch
        change some (p + (if checkable ic.2
          then 1 else 0)) = some ch at hch
        exact (Option.some.inj hch).symm
  simp only [visit, visit.visitgo]
  repeat' split
  all_goals try simp_all [hg.1, hg.2.1,
    hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2,
    hp, hpeq]
  all_goals first
    | omega
    | (refine ⟨?_, ?_, ?_⟩ <;>
        simp_all [hg.2.2.2.2.1, hg.2.2.2.2.2])
    | simp_all [hg.2.2.2.2.1, hg.2.2.2.2.2]

/-- Claim fifteen, resume composes: a second run on
    the output graph of a first grows it further,
    stays valid, and keeps every collected term and
    every equivalence of the first run (the growth
    clauses), while its own candidates are resolved
    under the same gate discipline by the resumption
    engine above; the summed budget clause of the
    claim is the engine's charge test read with the
    accounting identity of claim thirteen. -/
theorem claimfifteen (ctx : Ctx Sym)
    [DecidableEq Sym] (budget : Nat) (g : Graph Sym)
    (hv : Valid ctx.kinds g) (budget2 : Nat) :
    Growth ctx.kinds (resolve ctx budget g).out
        (resolve ctx budget2
          (resolve ctx budget g).out).out ∧
    Valid ctx.kinds (resolve ctx budget2
        (resolve ctx budget g).out).out ∧
    (∀ t, collected (resolve ctx budget g).out t →
      collected (resolve ctx budget2
        (resolve ctx budget g).out).out t) ∧
    (∀ x y, same (resolve ctx budget g).out x y →
      same (resolve ctx budget2
        (resolve ctx budget g).out).out x y) := by
  have h1 := claimone ctx budget g hv
  have h2 := claimone ctx budget2 _ h1.1
  exact ⟨h2.2, h2.1,
    fun t ht => h2.2.collected t ht,
    fun x y h => h2.2.same x y h⟩

/-- Claim seven, levels reconciled: over the run's
    output graph, recording two levels in either
    order reaches the same partition (the first
    reconciliation law at the output), the same
    edges up to their terms and colors (the second),
    and both orders grow the output (the third).
    The three are the theory's reconciliation
    theorems instantiated at the output graph, whose
    validity is claim one. -/
theorem claimseven (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym)
    (hv : Valid ctx.kinds g)
    (one two : Level Sym) (w1 w2 : Sym)
    (hone : one.terms.Nodup ∧
      ∀ t ∈ one.terms, one.scope t = true)
    (htwo : two.terms.Nodup ∧
      ∀ t ∈ two.terms, two.scope t = true)
    (x y : Term Sym) :
    (same (record ctx.kinds
        (record ctx.kinds (resolve ctx budget g).out
          one w1) two w2) x y ↔
      same (record ctx.kinds
        (record ctx.kinds (resolve ctx budget g).out
          two w2) one w1) x y) ∧
    (∀ e ∈ (record ctx.kinds
        (record ctx.kinds (resolve ctx budget g).out
          one w1) two w2).edges,
      ∃ e' ∈ (record ctx.kinds
          (record ctx.kinds (resolve ctx budget g).out
            two w2) one w1).edges,
        e'.terms = e.terms ∧ e'.colors = e.colors) ∧
    Growth ctx.kinds (resolve ctx budget g).out
        (record ctx.kinds
          (record ctx.kinds (resolve ctx budget g).out
            one w1) two w2) ∧
    Growth ctx.kinds (resolve ctx budget g).out
        (record ctx.kinds
          (record ctx.kinds (resolve ctx budget g).out
            two w2) one w1) := by
  have hout := (claimone ctx budget g hv).1
  exact ⟨reconpart ctx.kinds _ hout one two w1 w2
      hone htwo x y,
    (reconcolors ctx.kinds _ hout one two w1 w2 hone
      htwo).1,
    (recongrows ctx.kinds _ one two w1 w2).1,
    (recongrows ctx.kinds _ one two w1 w2).2⟩

/-- A level already present by name, terms, and
    pointwise scope reads as the same name. -/
theorem samenameofhaslevel [DecidableEq Sym]
    (g : Graph Sym) (lv : Level Sym)
    (h : haslevel g lv) : samename g lv = true := by
  obtain ⟨old, hold, hname, hterms, hscope⟩ := h
  simp only [samename, List.any_eq_true]
  refine ⟨old, hold, ?_⟩
  rw [decide_eq_true_eq]
  refine ⟨hname, hterms, ?_⟩
  rw [List.all_eq_true]
  intro t _
  simp [hscope]

/-- When the target step applies nothing, its bound
    is not taken or is the bound of the graph as it
    stands. -/
theorem targetboundofempty (ctx : Ctx Sym)
    [DecidableEq Sym] (st : St Sym)
    (h : (targetstep ctx st).1.ops = st.ops) :
    (targetstep ctx st).2.2 = none ∨
    (targetstep ctx st).2.2 =
      some (bound st.g ctx.target) := by
  simp only [targetstep, targetop, entered] at h ⊢
  repeat' split at h
  repeat' split
  all_goals first
    | (left; rfl)
    | (right; rfl)
    | simp_all
    | (exfalso
       have hlen := congrArg List.length h
       simp at hlen)

/-- When the target step applies its record, its
    bound is the bound of the entered graph, the
    level is not already present, and the step's
    graph is the record of the standing graph. -/
theorem targetapplied (ctx : Ctx Sym)
    [DecidableEq Sym] (st : St Sym) (c : Nat)
    (h : (targetstep ctx st).2.1 = .resolved c ∧
      (targetstep ctx st).1.ops =
        st.ops ++ [targetop ctx]) :
    (targetstep ctx st).2.2 =
        some (bound (enterall ctx.kinds st.g
          ctx.target.terms ctx.kinds.record
          (witof (targetop ctx))) ctx.target) ∧
      ¬ haslevel st.g ctx.target ∧
      (targetstep ctx st).1.g =
        record ctx.kinds st.g ctx.target
          (witof (targetop ctx)) := by
  have h1 := h.1
  have h2 := h.2
  simp only [targetstep, targetop, entered]
    at h1 h2 ⊢
  repeat' split at h1
  repeat' split at h2
  repeat' split
  all_goals first
    | (refine ⟨rfl, ?_, rfl⟩
       intro hh
       have hs := samenameofhaslevel st.g
         ctx.target hh
       simp_all)
    | simp_all
    | (exfalso
       have hlen := congrArg List.length h2
       simp at hlen)

/-- Claim eight, bound correctness: the bound a run
    reports is not taken, or is the bound of the
    standing graph at a repeat (with the bound's
    three properties there and its containment in
    the output's reading), or is the bound of the
    entered graph at an application (with the bound's
    properties there, its containment in the output's
    reading through the record graph's equal edges,
    and the recorded entry standing in the output's
    log with that bound as its terms). -/
theorem claimeight (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) (hb : budget ≠ 0)
    (hv : Valid ctx.kinds g) :
    (resolve ctx budget g).bound = none ∨
    ((resolve ctx budget g).bound =
        some (bound g ctx.target) ∧
      (∀ t ∈ ctx.target.terms, collected g t →
        t ∈ bound g ctx.target) ∧
      saturated g (bound g ctx.target) ∧
      (∀ s, saturated g s →
        (∀ t ∈ ctx.target.terms, t ∈ s) →
        ∀ t ∈ bound g ctx.target, t ∈ s) ∧
      (∀ t ∈ bound g ctx.target,
        t ∈ bound (resolve ctx budget g).out
          ctx.target)) ∨
    (∃ B : Graph Sym,
      (resolve ctx budget g).bound =
          some (bound B ctx.target) ∧
        Valid ctx.kinds B ∧
        (∀ t ∈ ctx.target.terms, collected B t →
          t ∈ bound B ctx.target) ∧
        saturated B (bound B ctx.target) ∧
        (∀ t ∈ bound B ctx.target,
          t ∈ bound (resolve ctx budget g).out
            ctx.target) ∧
        (∃ e ∈ (resolve ctx budget g).out.log,
          e.kind = ctx.kinds.record ∧
            e.level = ctx.target.name ∧
            e.terms = bound B ctx.target)) := by
  have hbound : (resolve ctx budget g).bound =
      (targetstep ctx (intake ctx budget g).1).2.2 := by
    simp only [resolve, if_neg hb]
  have hg : (intake ctx budget g).1.g = g :=
    (intakeok ctx budget g).1
  have hout := claimone ctx budget g hv
  have htb := targetbound ctx
    (intake ctx budget g).1
  cases htb with
  | inl hnone =>
      exact Or.inl (by rw [hbound, hnone])
  | inr hrest =>
      cases hrest with
      | inl hrep =>
          refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)
          · rw [hbound, hrep, hg]
          · exact boundabove g ctx.target
          · exact boundsat ctx.kinds g hv ctx.target
          · intro s hs hab
            exact boundleast g ctx.target s hs hab
          · intro t ht
            exact boundgrows ctx.kinds hout.2 hout.1
              ctx.target t ht
      | inr happ =>
          obtain ⟨extrat, htops, htsteps, htrun,
            hclass⟩ := targetsteps ctx
            (intake ctx budget g).1
          have hempty : extrat = [] ∨
              ∃ c, extrat = [targetop ctx] ∧
                (targetstep ctx
                  (intake ctx budget g).1).2.1 =
                  .resolved c := by
            cases hclass with
            | inl h => exact Or.inl h.2
            | inr h =>
                cases h with
                | inl h =>
                    obtain ⟨c, h1, h2⟩ := h
                    exact Or.inr ⟨c, h2, h1⟩
                | inr h => exact Or.inl h
          cases hempty with
          | inl he =>
              have hbo := targetboundofempty ctx
                (intake ctx budget g).1 (by
                  rw [htops, he]
                  simp)
              cases hbo with
              | inl hn =>
                  rw [happ] at hn
                  simp at hn
              | inr hr =>
                  refine Or.inr (Or.inl ⟨?_, ?_, ?_,
                    ?_, ?_⟩)
                  · rw [hbound, hr, hg]
                  · exact boundabove g ctx.target
                  · exact boundsat ctx.kinds g hv
                      ctx.target
                  · intro s hs hab
                    exact boundleast g ctx.target s hs
                      hab
                  · intro t ht
                    exact boundgrows ctx.kinds hout.2
                      hout.1 ctx.target t ht
          | inr happ2 =>
              obtain ⟨c, hextra, hres⟩ := happ2
              obtain ⟨hb2, hnh, htg⟩ := targetapplied
                ctx (intake ctx budget g).1 c
                ⟨hres, by rw [htops, hextra]⟩
              obtain ⟨B, hB⟩ : ∃ B : Graph Sym,
                  B = enterall ctx.kinds
                    (intake ctx budget g).1.g
                    ctx.target.terms ctx.kinds.record
                    (witof (targetop ctx)) :=
                ⟨_, rfl⟩
              have hvalidB : Valid ctx.kinds B := by
                rw [hB]
                exact enterallvalid ctx.kinds
                  ctx.target.terms ctx.kinds.record
                  (witof (targetop ctx))
                  (intake ctx budget g).1.g (by
                    rw [hg]; exact hv)
              have hvalidt : Valid ctx.kinds
                  (targetstep ctx
                    (intake ctx budget g).1).1.g := by
                have hready : Ready ctx.kinds
                    (intake ctx budget g).1.g extrat :=
                  stepsready (fun g' op hg' lv w hop => by
                    have hc := rgatecond ctx g' op hg'
                    rw [hop] at hc
                    exact hc) (by rw [hg]; exact hv)
                    (by rwa [hg] at htsteps)
                rw [htrun]
                exact runvalid ctx.kinds hready
              have hgrowt : Growth ctx.kinds
                  (targetstep ctx
                    (intake ctx budget g).1).1.g
                  (resolve ctx budget g).out := by
                have hout2 : (resolve ctx budget g).out =
                    (sweeps ctx
                      ((intake ctx budget g).2.1.length
                        + 1)
                      (targetstep ctx
                        (intake ctx budget g).1).1
                      (intake ctx budget g).2.1).1.g := by
                  simp only [resolve, if_neg hb]
                obtain ⟨extras, hsops, hssteps, hsrun,
                  -, -⟩ := sweepsfold ctx
                  ((intake ctx budget g).2.1.length + 1)
                  (targetstep ctx
                    (intake ctx budget g).1).1
                  (intake ctx budget g).2.1
                have hready : Ready ctx.kinds
                    (targetstep ctx
                      (intake ctx budget g).1).1.g
                    extras :=
                  stepsready (fun g' op hg' lv w hop => by
                    have hc := rgatecond ctx g' op hg'
                    rw [hop] at hc
                    exact hc) hvalidt hssteps
                rw [hout2, hsrun]
                exact rungrows ctx.kinds hready
              have hboundB : bound (targetstep ctx
                    (intake ctx budget g).1).1.g
                  ctx.target = bound B ctx.target := by
                rw [htg, hB, recordelse ctx.kinds
                  (intake ctx budget g).1.g ctx.target
                  (witof (targetop ctx)) hnh]
                rfl
              refine Or.inr (Or.inr ⟨B, ?_, hvalidB,
                ?_, ?_, ?_, ?_⟩)
              · rw [hbound, hb2, ← hB]
              · exact boundabove B ctx.target
              · exact boundsat ctx.kinds B hvalidB
                  ctx.target
              · intro t ht
                rw [← hboundB] at ht
                exact boundgrows ctx.kinds hgrowt
                  hout.1 ctx.target t ht
              · have hgrec : Growth ctx.kinds
                    (record ctx.kinds
                      (intake ctx budget g).1.g
                      ctx.target
                      (witof (targetop ctx)))
                    (resolve ctx budget g).out := by
                  rwa [htg] at hgrowt
                obtain ⟨e, he, hk, hl, ht⟩ :=
                  boundrecorded ctx.kinds
                    (intake ctx budget g).1.g ctx.target
                    (witof (targetop ctx)) hnh hgrec
                rw [← hB] at ht
                exact ⟨e, he, hk, hl, ht⟩

/-- Claim nine, view growth: every edge of the input
    graph has a counterpart edge in the output graph
    holding all its terms and all its colors — the
    theory's view growth theorem at the run's growth,
    with both graphs valid. The filtered view clause
    is the same statement read at a filtered edge
    list, which the growth's colors clause carries. -/
theorem claimnine (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym)
    (hv : Valid ctx.kinds g) (e : Edge Sym)
    (he : e ∈ g.edges) :
    ∃ e' ∈ (resolve ctx budget g).out.edges,
      (∀ t ∈ e.terms, t ∈ e'.terms) ∧
        ∀ c ∈ e.colors, c ∈ e'.colors := by
  have hout := claimone ctx budget g hv
  exact edgegrow ctx.kinds hout.2 hv hout.1 e he

/-- Claim ten, first part: the color algebra of the
    theory — color lists join commutatively,
    associatively, and idempotently (the union laws
    of the coloring file). -/
theorem claimtenalgebra (xs ys zs : List (Color Sym)) :
    (∀ c, c ∈ union xs ys ↔ c ∈ union ys xs) ∧
    (∀ c, c ∈ union (union xs ys) zs ↔
      c ∈ union xs (union ys zs)) ∧
    (∀ c, c ∈ union xs xs ↔ c ∈ xs) :=
  ⟨unioncomm xs ys, unionassoc xs ys zs,
    unionidem xs⟩

/-- The step form of claim ten: along a gated trace,
    at the step where a meant-marked paint is
    applied, the filter test held at that step's
    graph. -/
theorem claimtenstep (ctx : Ctx Sym)
    [DecidableEq Sym] :
    ∀ {g h : Graph Sym} {ops : List (Op Sym)},
    Steps ctx.kinds (RGate ctx) g h ops →
    ∀ (t : Term Sym) (c : Color Sym) (l w : Sym),
    Op.paint t c l w ∈ ops → c.mark = ctx.meant →
    ∃ (pre : List (Op Sym)) (m : Graph Sym)
      (post : List (Op Sym)),
      Steps ctx.kinds (RGate ctx) g m pre ∧
      pre ++ [Op.paint t c l w] ++ post = ops ∧
      filterok ctx m (Op.paint t c l w) = true := by
  intro g h ops hs
  induction hs with
  | nil =>
      intro t c l w hop
      simp at hop
  | step op hs' hg happ ih =>
      intro t c l w hop hc
      rw [List.mem_append, List.mem_singleton]
        at hop
      cases hop with
      | inl hmem =>
          obtain ⟨pre, m, post, hpre, hpost, hfil⟩ :=
            ih t c l w hmem hc
          exact ⟨pre, m, post ++ [op], hpre, by
            rw [← hpost]
            simp [List.append_assoc], hfil⟩
      | inr heq =>
          refine ⟨_, _, [], hs', ?_, ?_⟩
          · rw [heq]; simp
          · cases hg with
            | inl hg =>
                rw [← heq] at hg
                exact hg.2.2.2.1
            | inr hg =>
                rw [← heq] at hg
                have h2 : Op.paint t c l w =
                    Op.record ctx.target
                      (ctx.twit.getD
                        ctx.target.name) := hg.1
                cases h2

/-- The filter test's content: where a meant-marked
    paint passes, the painted term's edge holds a
    seen entry and a wanted entry of the same
    painter. -/
theorem filterokcontent (ctx : Ctx Sym)
    [DecidableEq Sym] (g : Graph Sym) (t : Term Sym)
    (c : Color Sym) (l w : Sym)
    (h : filterok ctx g (Op.paint t c l w) = true)
    (hc : c.mark = ctx.meant) :
    ∃ e, edgeof g t = some e ∧
      (∃ x ∈ e.colors, x.who = c.who ∧
        x.mark = ctx.seen) ∧
      (∃ x ∈ e.colors, x.who = c.who ∧
        x.mark = ctx.wanted) := by
  have hd : decide (c.mark = ctx.meant) = true :=
    decide_eq_true hc
  cases he : edgeof g t with
  | none =>
      simp [filterok, hd, he] at h
  | some e =>
      simp only [filterok, hd, he, if_true,
        Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨⟨x1, hx1, hd1⟩, ⟨x2, hx2, hd2⟩⟩ := h
      exact ⟨e, rfl,
        ⟨x1, hx1, of_decide_eq_true hd1⟩,
        ⟨x2, hx2, of_decide_eq_true hd2⟩⟩

/-- Claim ten, second part: a paint step in a run
    whose color's mark is the meant mark passed the
    gate's filter rule at its step, so at the graph
    of that step the painted term's edge held a seen
    entry and a wanted entry of the same painter. -/
theorem claimten (ctx : Ctx Sym) [DecidableEq Sym]
    {g h : Graph Sym} {ops : List (Op Sym)}
    (hs : Steps ctx.kinds (RGate ctx) g h ops)
    (t : Term Sym) (c : Color Sym) (l w : Sym)
    (hop : Op.paint t c l w ∈ ops)
    (hc : c.mark = ctx.meant) :
    ∃ (pre : List (Op Sym)) (m : Graph Sym)
      (post : List (Op Sym)),
      Steps ctx.kinds (RGate ctx) g m pre ∧
      pre ++ [Op.paint t c l w] ++ post = ops ∧
      ∃ e, edgeof m t = some e ∧
        (∃ x ∈ e.colors, x.who = c.who ∧
          x.mark = ctx.seen) ∧
        (∃ x ∈ e.colors, x.who = c.who ∧
          x.mark = ctx.wanted) := by
  obtain ⟨pre, m, post, hpre, hpost, hfil⟩ :=
    claimtenstep ctx hs t c l w hop hc
  exact ⟨pre, m, post, hpre, hpost,
    filterokcontent ctx m t c l w hfil hc⟩

/-- Claim eleven, composition of the derived set:
    the derived set is the join of the three sources
    — the intent, the fresh terms of the target and
    the candidates, and the overlap — each source
    below it, membership exactly the three-way
    disjunction, and the same state under the other
    associations and orders (the join laws of the
    theory). -/
theorem claimeleven (ctx : Ctx Sym) [DecidableEq Sym]
    (g : Graph Sym) (cands : List (Op Sym)) :
    (∀ t, t ∈ derivedset ctx g cands →
      t ∈ ctx.intent ∨ t ∈ fresh ctx g cands ∨
        t ∈ overlap ctx g) ∧
    State.below ctx.intent (derivedset ctx g cands) ∧
    State.below (fresh ctx g cands)
      (derivedset ctx g cands) ∧
    State.below (overlap ctx g)
      (derivedset ctx g cands) ∧
    State.same (derivedset ctx g cands)
      (State.join (overlap ctx g)
        (State.join (fresh ctx g cands) ctx.intent)) ∧
    State.same (derivedset ctx g cands)
      (State.join ctx.intent
        (State.join (fresh ctx g cands)
          (overlap ctx g))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [derivedset, State.join,
      List.mem_append] at ht
    cases ht with
    | inl h =>
        cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  · intro t ht
    simp only [derivedset, State.join,
      List.mem_append]
    exact Or.inl (Or.inl ht)
  · intro t ht
    simp only [derivedset, State.join,
      List.mem_append]
    exact Or.inl (Or.inr ht)
  · intro t ht
    simp only [derivedset, State.join,
      List.mem_append]
    exact Or.inr ht
  · intro t
    simp only [derivedset, State.join,
      List.mem_append]
    constructor
    · intro h
      cases h with
      | inl h =>
          cases h with
          | inl h => exact Or.inr (Or.inr h)
          | inr h => exact Or.inr (Or.inl h)
      | inr h => exact Or.inl h
    · intro h
      cases h with
      | inl h => exact Or.inr h
      | inr h =>
          cases h with
          | inl h => exact Or.inl (Or.inr h)
          | inr h => exact Or.inl (Or.inl h)
  · intro t
    simp only [derivedset, State.join,
      List.mem_append]
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

/-- The one-step form of claim twelve: over one
    applied operation at a valid graph, a new
    equivalence between distinct terms either held
    already or factors through the operation's own
    join endpoints — and only a join has endpoints
    to factor through: an enter adds only the
    diagonal pair of its term, a record only the
    diagonal pairs of its level, a paint none. -/
theorem claimtwelvestep (ctx : Ctx Sym)
    [DecidableEq Sym] (g : Graph Sym)
    (hv : Valid ctx.kinds g) (op : Op Sym) :
    ∀ a b, same (apply ctx.kinds g op) a b → a ≠ b →
    same g a b ∨
      ∃ one two l w, op = Op.join one two l w ∧
        (same g a one ∨ a = one ∨
          same g a two ∨ a = two) ∧
        (same g b one ∨ b = one ∨
          same g b two ∨ b = two) := by
  intro a b hsame hne
  cases op with
  | enter t l w =>
      have h2 : same (enter ctx.kinds g t l w) a b :=
        hsame
      have h3 := (entersame ctx.kinds g t l w a b).mp
        h2
      cases h3 with
      | inl h => exact Or.inl h
      | inr h =>
          exact (hne (h.1.trans h.2.symm)).elim
  | join one two l w =>
      have h2 : same (join ctx.kinds g one two l w)
          a b := hsame
      have h3 := joinsameback ctx.kinds g hv one two
        l w a b h2
      cases h3 with
      | inl h => exact Or.inl h
      | inr h =>
          exact Or.inr ⟨one, two, l, w, rfl, h⟩
  | paint t c l w =>
      have h2 : same (paint ctx.kinds g t c l w) a b :=
        hsame
      exact Or.inl ((paintsame ctx.kinds g t c l w a
        b).mp h2)
  | record lv w =>
      have h2 : same (record ctx.kinds g lv w) a b :=
        hsame
      have h3 := (recordsame ctx.kinds g hv lv w a
        b).mp h2
      cases h3 with
      | inl h => exact Or.inl h
      | inr h => exact (hne h.1).elim

/-- A gated trace from a valid graph reaches a
    valid graph. -/
theorem stepsvalid (ctx : Ctx Sym) [DecidableEq Sym] :
    ∀ {g h : Graph Sym} {ops : List (Op Sym)},
    Steps ctx.kinds (RGate ctx) g h ops →
    Valid ctx.kinds g → Valid ctx.kinds h := by
  intro g h ops hs
  induction hs with
  | nil =>
      intro hv
      exact hv
  | step op hs' hg happ ih =>
      intro hv
      have hvm := ih hv
      rw [← happ]
      cases op with
      | enter t l w =>
          exact entervalid ctx.kinds _ hvm t l w
      | join a b l w =>
          exact joinvalid ctx.kinds _ hvm a b l w
      | paint t c l w =>
          exact paintvalid ctx.kinds _ hvm t c l w
      | record lv w =>
          have hcond : lv.terms.Nodup ∧
              ∀ t ∈ lv.terms, lv.scope t = true := by
            cases hg with
            | inl hg =>
                exact rgatecond ctx _ _ (Or.inl hg)
            | inr hg =>
                have hlv : lv = ctx.target := by
                  have h1 := hg.1
                  simp only [targetop,
                    Op.record.injEq] at h1
                  exact h1.1
                subst hlv
                exact recordokcond ctx.target w
                  hg.2.2.2.1
          exact recordvalid ctx.kinds _ hvm lv w
            hcond.1 hcond.2

/-- Claim twelve, intent paints no equivalence:
    along a gated trace with no join operation in
    it, every equivalence of the final graph either
    held in the input graph or is a diagonal pair.
    Paints — the operations intent acts through —
    create no equivalence between distinct terms;
    equivalences are created only by joins, whose
    endpoints the step form above reads. -/
theorem claimtwelve (ctx : Ctx Sym)
    [DecidableEq Sym] :
    ∀ {g h : Graph Sym} {ops : List (Op Sym)},
    Steps ctx.kinds (RGate ctx) g h ops →
    Valid ctx.kinds g →
    (∀ op ∈ ops, ∀ one two l w,
      op ≠ Op.join one two l w) →
    ∀ a b, same h a b → same g a b ∨ a = b := by
  intro g h ops hs
  induction hs with
  | nil =>
      intro _ _ a b hsame
      exact Or.inl hsame
  | step op hs' hg happ ih =>
      intro hv hno a b hsame
      by_cases hab : a = b
      · exact Or.inr hab
      · have hvm := stepsvalid ctx hs' hv
        have h3 := claimtwelvestep ctx _ hvm op a b
          (happ.symm ▸ hsame) hab
        cases h3 with
        | inl h =>
            exact ih hv (fun op' hop' =>
              hno op' (List.mem_append_left _ hop')) a
              b h
        | inr h =>
            obtain ⟨one, two, l, w, hop, -, -⟩ := h
            exact (hno op (by simp) one two l w
              hop).elim

/-- The charge a verdict carries in the accounting:
    a resolution its counted cost, a witness refusal
    one, everything else nothing. -/
def outcharge (o : Outcome) : Nat :=
  match o with
  | .resolved c => c
  | .refused .witness _ => 1
  | _ => 0

/-- The sum over an append of lists of counts. -/
theorem sumappend (l1 l2 : List Nat) :
    (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_assoc]

/-- A pass's spend decomposes over its verdicts. -/
theorem passspentfold (ctx : Ctx Sym)
    [DecidableEq Sym] :
    ∀ (l : List (Nat × Op Sym))
      (acc : St Sym × List (Nat × Outcome)),
    (l.foldl (vstep ctx) acc).1.spent +
        (acc.2.map (fun p => outcharge p.2)).sum =
      acc.1.spent +
        ((l.foldl (vstep ctx) acc).2.map
          (fun p => outcharge p.2)).sum := by
  intro l
  induction l with
  | nil =>
      intro acc
      simp
  | cons ic l ih =>
      intro acc
      have hstep : (ic :: l).foldl (vstep ctx) acc =
          l.foldl (vstep ctx) (vstep ctx acc ic) := by
        rw [List.foldl_cons]
      rw [hstep]
      have h := ih (vstep ctx acc ic)
      have hv : vstep ctx acc ic =
          ((visit ctx ctx.cands acc.1 ic).1,
            acc.2 ++ [(ic.1,
              (visit ctx ctx.cands acc.1 ic).2)]) := rfl
      rw [hv] at h
      have hspent : (visit ctx ctx.cands acc.1
          ic).1.spent = acc.1.spent +
        outcharge (visit ctx ctx.cands acc.1 ic).2 :=
        visitspent ctx acc.1 ic
      rw [hv] at ⊢
      simp only [List.map_append, sumappend,
        List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at h
      omega

/-- A pass's spend, from the pass itself. -/
theorem passspent (ctx : Ctx Sym) [DecidableEq Sym]
    (st : St Sym) (pool : List (Nat × Op Sym)) :
    (pass ctx st pool).1.spent = st.spent +
      ((pass ctx st pool).2.map
        (fun p => outcharge p.2)).sum := by
  have h := passspentfold ctx (isortkey st.g pool)
    (st, [])
  simp at h
  rw [pass]
  exact h

/-- The sweeps' spend decomposes over their
    verdicts. -/
theorem sweepsspent (ctx : Ctx Sym)
    [DecidableEq Sym] :
    ∀ (fuel : Nat) (st : St Sym)
      (pool : List (Nat × Op Sym)),
    (sweeps ctx fuel st pool).1.spent = st.spent +
      ((sweeps ctx fuel st pool).2.1.map
        (fun p => outcharge p.2)).sum := by
  intro fuel
  induction fuel with
  | zero =>
      intro st pool
      simp [sweeps]
  | succ fuel ih =>
      intro st pool
      by_cases hstop :
          (pass ctx st pool).1.ops.length =
            st.ops.length
      · obtain ⟨h1, -⟩ := sweepsone ctx fuel st pool
          hstop
        have h2 : (sweeps ctx (fuel + 1) st pool).2.1 =
            (pass ctx st pool).2 := by
          rw [sweepseq]
          dsimp only
          rw [if_pos hstop]
        rw [h1, h2]
        exact passspent ctx st pool
      · obtain ⟨h1, h2⟩ := sweepsmore ctx fuel st pool
          hstop
        have h3 : (sweeps ctx (fuel + 1) st pool).2.1 =
            (pass ctx st pool).2 ++
              (sweeps ctx fuel (pass ctx st pool).1
                (asideof pool
                  (pass ctx st pool).2)).2.1 := by
          rw [sweepseq]
          dsimp only
          rw [if_neg hstop]
        rw [h1, h3, List.map_append, sumappend]
        have h4 := ih (pass ctx st pool).1
          (asideof pool (pass ctx st pool).2)
        have h5 := passspent ctx st pool
        omega

/-- Intake's spend decomposes: one counted test per
    admitted candidate and per scope deferral, and
    nothing else. -/
theorem intakespent (ctx : Ctx Sym) [DecidableEq Sym]
    (budget : Nat) (g : Graph Sym) :
    (intake ctx budget g).1.spent =
      (intake ctx budget g).2.1.length +
        ((intake ctx budget g).2.2.filter
          (fun p => p.2 = .deferred .scope)).length :=
  by
  have key : ∀ (l : List (Nat × Op Sym))
      (acc : St Sym × List (Nat × Op Sym) ×
        List (Nat × Outcome)),
      (List.foldl (istept ctx) acc l).1.spent +
          acc.2.1.length +
          (acc.2.2.filter
            (fun p => p.2 = .deferred .scope)).length =
        acc.1.spent +
          (List.foldl (istept ctx) acc l).2.1.length +
          ((List.foldl (istept ctx) acc l).2.2.filter
            (fun p => p.2 = .deferred .scope)).length :=
    by
    intro l
    induction l with
    | nil =>
        intro acc
        simp
    | cons ic l ih =>
        intro acc
        rw [List.foldl_cons]
        have h := ih (istept ctx acc ic)
        have hstep : (istept ctx acc ic).1.spent +
            acc.2.1.length +
            (acc.2.2.filter
              (fun p => p.2 = .deferred
                .scope)).length =
          acc.1.spent +
            (istept ctx acc ic).2.1.length +
            ((istept ctx acc ic).2.2.filter
              (fun p => p.2 = .deferred
                .scope)).length := by
          unfold istept
          repeat' split
          all_goals simp_all [List.filter_append,
            List.length_append]
          all_goals omega
        omega
  rw [intakeeq]
  have h := key (indexed ctx)
    ((St.mk g budget 0 []), [], [])
  simp at h
  omega

/-- Claim thirteen, Pareto accounting: the run's
    spend and the budget left sum to the budget (no
    unit unaccounted), and the spend decomposes
    exactly: one counted test per candidate admitted
    at intake and per scope deferral there, the
    target step's verdict charge, and the verdict
    charges of the sweeps. Nothing is spent on
    anything else — the decomposition is the waste
    statement. The dominance clause of the claim
    reads with claim six (every unapplied candidate
    is blocked, so no cheaper correct run applies
    more) and with the theory's cross-join excess
    facts; dominance over other procedures is not a
    statement about this implementation alone. -/
theorem claimthirteen (ctx : Ctx Sym)
    [DecidableEq Sym] (budget : Nat) (g : Graph Sym)
    (hb : budget ≠ 0) :
    (resolve ctx budget g).spent +
        (resolve ctx budget g).left = budget ∧
    (resolve ctx budget g).spent =
      (intake ctx budget g).2.1.length +
        ((intake ctx budget g).2.2.filter
          (fun p => p.2 = .deferred .scope)).length +
        outcharge (targetstep ctx
          (intake ctx budget g).1).2.1 +
        ((sweeps ctx
            ((intake ctx budget g).2.1.length + 1)
            (targetstep ctx (intake ctx budget g).1).1
            (intake ctx budget g).2.1).2.1.map
          (fun p => outcharge p.2)).sum := by
  have hspent : (resolve ctx budget g).spent =
      (sweeps ctx ((intake ctx budget g).2.1.length
          + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1).1.spent := by
    simp only [resolve, if_neg hb]
  have hleft : (resolve ctx budget g).left =
      (sweeps ctx ((intake ctx budget g).2.1.length
          + 1)
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1).1.left := by
    simp only [resolve, if_neg hb]
  have h1 := (intakeok ctx budget g).2.2.1
  have h2 := targetacct ctx (intake ctx budget g).1
  obtain ⟨-, -, -, -, hsum3, -⟩ := sweepsfold ctx
    ((intake ctx budget g).2.1.length + 1)
    (targetstep ctx (intake ctx budget g).1).1
    (intake ctx budget g).2.1
  have h3 := sweepsspent ctx
    ((intake ctx budget g).2.1.length + 1)
    (targetstep ctx (intake ctx budget g).1).1
    (intake ctx budget g).2.1
  have h4 := targetspent ctx (intake ctx budget g).1
  have h5 := intakespent ctx budget g
  constructor
  · rw [hspent, hleft]
    omega
  · have h6 : outcharge (targetstep ctx
        (intake ctx budget g).1).2.1 =
      (match (targetstep ctx
          (intake ctx budget g).1).2.1 with
        | .resolved c => c
        | .refused .witness _ => 1
        | _ => 0) := rfl
    rw [hspent, h3, h4, h5, h6]
