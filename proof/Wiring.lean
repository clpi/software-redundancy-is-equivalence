/-
  The wiring of algorithm.md section 22's follow-on:
  the resolution run's candidate pool, routed through
  the scheduler's bounded pass. Schedule.lean landed
  as the selection and accounting layer — its bounded
  pass (Sched.sweep) selects over Sched.Cand values
  under the cone gate, the instantiation-depth cap,
  the per-rule fuel gate, and the rank beam — but no
  resolver value was ever projected to a scheduler
  candidate, and the run's own loop (Resolve.lean:
  intake, pass, sweeps, resolve) read nothing of it.
  This file is the projection and the routing: every
  field of the scheduler candidate is read off the
  resolver's own values at the pass's starting graph,
  the wired pool is the pool's survivors of the
  bounded pass, and the wired pass, sweeps, and run
  are the run's own pass, sweeps, and run over the
  wired pool, with the scheduler plan threaded through
  the sweeps and every resolved visit reported back
  through the scheduler's step function.

  The projection's readings, stated as this file's
  definitions, in the resolver's own terms:

  - rule: the candidate's kind position (tagno of
    tagof). The resolver's rule table is its four
    kinds, in the visiting order of section 6; the
    scheduler's per-rule fuel is indexed by it, and a
    plan for a wired run carries four allowances.
  - cone: relevance at the pass's starting graph
    against the run's candidate list. Relevance and
    the derived set are the cone, per section 21
    (claims three, six, and eleven); relevance is
    also the visit's own first test, so a candidate
    the cone gate refuses is one the visit would have
    deferred with reason target at that graph.
  - depth: the deepest nesting of the candidate's
    terms. The resolver carried no instantiation
    depth (gap eleven's interim rule: operations are
    data, applied once per visit); the wiring counts
    the depth from the terms themselves — an atom
    nests zero deep, a form one deeper than its
    deepest part.
  - gain: the visiting key of section 6 packed as
    one number and negated, so a higher gain is a
    higher visiting priority and the beam's rank over
    gains is the rank by the run's own visiting
    order. The packing's radices are read off the
    pool at the pass's starting graph: the price
    component is the counted cost, with a candidate
    of no cost at that graph placed above every
    counted cost in its pool (the key's no-cost flag,
    folded into the price component), then the kind
    position, then the input position.
  - bridge: the candidate presents a term not yet
    collected at that graph that another pool
    candidate also acts on — it carries material the
    rest of the pool is waiting on, the resolver's
    reading of a step whose value is bridging.

  The report-back's readings, likewise stated: a
  resolved visit fires its kind's rule with growth
  one (a visit applies one operation atomically, and
  the scheduler's fire counts growth at least one);
  the fire counts as a merge exactly when every term
  of the candidate already stood collected at the
  pass's starting graph — the visit then joins
  material already in the graph — and as growth
  without a merge otherwise. Both readings are taken
  at the pass's starting graph, the same point where
  the pass reads its pool.

  Four states are kept distinct: the bounded design
  is settled intent (the rulings of 2026-11-24); this
  file is implemented behavior; what the family gate
  checks at a landed pin is verified behavior; and no
  proved theorem of Resolve.lean or Schedule.lean is
  restated or weakened here — the wired run's claims
  are proved from theirs (passfold, sweepsfold's
  pattern, targetsteps, intakeok, sweepgates,
  beambridge, stepmerge, stepfuel), and the wired
  run inherits the run's soundness decomposition by
  the same proof as runsteps.
-/

import Resolve
import Schedule

namespace Wire

variable {Sym : Type}

/- ## The projection (the resolver's values, read as
   scheduler candidates) -/

/-- The scheduler rule of a resolver candidate: its
    kind's position in the visiting order. -/
def ruleof (op : Op Sym) : Nat :=
  tagno (tagof op)

/- The nesting depth of a term: an atom nests zero
   deep; a form nests one deeper than its deepest
   part, head included. -/
mutual
def termdepth : Term Sym → Nat
  | .atom _ => 0
  | .form h args => 1 + max (termdepth h) (listdepth args)
def listdepth : List (Term Sym) → Nat
  | [] => 0
  | t :: rest => max (termdepth t) (listdepth rest)
end

/-- The depth of a candidate: the deepest nesting
    among its terms. -/
def canddepth (op : Op Sym) : Nat :=
  (termsof op).foldl (fun m t => max m (termdepth t)) 0

/-- The price radix of a pool at a graph: one past
    the widest counted cost in the pool, so a
    candidate of no cost at that graph, read at this
    radix, stands above every counted cost. -/
def pricebound [DecidableEq Sym] (g : Graph Sym)
    (pool : List (Nat × Op Sym)) : Nat :=
  ((pool.map
    (fun ic => (priceof g ic.2).getD 0)).max?).getD 0 + 1

/-- The visiting key of section 6 packed as one
    number: scope rank, then counted cost (no cost
    read at the pool's price radix, the key's no-cost
    flag folded in), then kind position, then input
    position, each component under the next one's
    radix. -/
def keynum [DecidableEq Sym] (g : Graph Sym)
    (pool : List (Nat × Op Sym)) (ic : Nat × Op Sym) :
    Nat :=
  let b := pricebound g pool
  let price := (priceof g ic.2).getD b
  ((candrank ic.2 * (b + 1) + price) * 4 +
    tagno (tagof ic.2)) * (pool.length + 1) + ic.1

/-- A bridge candidate of a pool at a graph: it
    presents a term not yet collected that another
    pool candidate also acts on. -/
def bridgeof [DecidableEq Sym] (g : Graph Sym)
    (pool : List (Nat × Op Sym)) (ic : Nat × Op Sym) :
    Bool :=
  (termsof ic.2).any (fun t =>
    !(collectedb g t) &&
      pool.any (fun jc =>
        decide (jc.1 ≠ ic.1) &&
          decide (t ∈ termsof jc.2)))

/-- The scheduler candidate of a resolver candidate,
    read at a graph against its pool: rule by kind,
    gain by the packed visiting key negated, depth by
    term nesting, bridge by shared uncollected
    material, cone by relevance against the run's
    candidate list. -/
def candof [DecidableEq Sym] (ctx : Ctx Sym)
    (g : Graph Sym) (pool : List (Nat × Op Sym))
    (ic : Nat × Op Sym) : Sched.Cand :=
  { rule := ruleof ic.2,
    gain := -(keynum g pool ic : Int),
    depth := canddepth ic.2,
    bridge := bridgeof g pool ic,
    cone := relevant ctx g ctx.cands ic.2 }

/- ## The wired pool (the bounded pass, interposed at
   the head of a pass) -/

/-- The wired pool: the candidates of the pool whose
    projections survive the scheduler's bounded pass
    — beam, cone gate, depth cap, fuel gate — read at
    the pass's starting graph, in the pool's own
    order. The pass a wired run makes visits exactly
    this pool, in the visiting order. -/
def wiredpool [DecidableEq Sym] (plan : Sched.Plan)
    (cap w : Nat) (ctx : Ctx Sym) (g : Graph Sym)
    (pool : List (Nat × Op Sym)) :
    List (Nat × Op Sym) :=
  pool.filter (fun ic =>
    decide (candof ctx g pool ic ∈
      Sched.sweep plan cap w
        (pool.map (candof ctx g pool))))

/-- A wired pool member is a pool member. -/
theorem wiredmem [DecidableEq Sym]
    {plan : Sched.Plan} {cap w : Nat} {ctx : Ctx Sym}
    {g : Graph Sym} {pool : List (Nat × Op Sym)}
    {ic : Nat × Op Sym} :
    ic ∈ wiredpool plan cap w ctx g pool →
      ic ∈ pool := by
  intro h
  simp only [wiredpool, List.mem_filter] at h
  exact h.1

/-- Everything in the wired pool passed every gate of
    the bounded pass at that graph: it is a pool
    member, in the witnessed cone (relevant, the
    visit's own first test), within the depth cap,
    and its kind's rule had fuel — the scheduler's
    proved bounds (sweepgates), read back through the
    projection. -/
theorem wiredgates [DecidableEq Sym]
    {plan : Sched.Plan} {cap w : Nat} {ctx : Ctx Sym}
    {g : Graph Sym} {pool : List (Nat × Op Sym)}
    {ic : Nat × Op Sym} :
    ic ∈ wiredpool plan cap w ctx g pool →
      ic ∈ pool ∧
        relevant ctx g ctx.cands ic.2 = true ∧
        canddepth ic.2 ≤ cap ∧
        Sched.fuelof plan (ruleof ic.2) ≠ 0 := by
  intro h
  simp only [wiredpool, List.mem_filter] at h
  obtain ⟨hpool, hsweep⟩ := h
  have hg := Sched.sweepgates
    (of_decide_eq_true hsweep)
  exact ⟨hpool, hg.2.1, hg.2.2.1, hg.2.2.2⟩

/-- A bridge candidate that passes the three gates is
    in the wired pool whatever its rank: the beam
    keeps every bridge candidate (beambridge), and
    the gates it passes are the pass's filter. -/
theorem wiredbridge [DecidableEq Sym]
    {plan : Sched.Plan} {cap w : Nat} {ctx : Ctx Sym}
    {g : Graph Sym} {pool : List (Nat × Op Sym)}
    {ic : Nat × Op Sym} :
    ic ∈ pool → bridgeof g pool ic = true →
    relevant ctx g ctx.cands ic.2 = true →
    canddepth ic.2 ≤ cap →
    Sched.fuelof plan (ruleof ic.2) ≠ 0 →
    ic ∈ wiredpool plan cap w ctx g pool := by
  intro hpool hbridge hcone hdepth hfuel
  have hmem : candof ctx g pool ic ∈
      pool.map (candof ctx g pool) :=
    List.mem_map.mpr ⟨ic, hpool, rfl⟩
  have hbeam : candof ctx g pool ic ∈
      Sched.beam w (pool.map (candof ctx g pool)) :=
    Sched.beambridge hmem hbridge
  have hgates : ((candof ctx g pool ic).cone &&
      ((candof ctx g pool ic).depth ≤ cap) &&
        (Sched.fuelof plan
          (candof ctx g pool ic).rule ≠ 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hcone, hdepth⟩, hfuel⟩
  have hsweep : candof ctx g pool ic ∈
      Sched.sweep plan cap w
        (pool.map (candof ctx g pool)) := by
    simp only [Sched.sweep, List.mem_filter]
    exact ⟨hbeam, hgates⟩
  simp only [wiredpool, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨hpool, hsweep⟩

/- ## The wired pass -/

/-- One wired pass: the run's own pass over the wired
    pool — the bounded pass interposed at the head of
    the pass, at the pass's starting graph, where the
    visiting order also reads the pool. -/
noncomputable def wpass [DecidableEq Sym]
    (plan : Sched.Plan) (cap w : Nat) (ctx : Ctx Sym)
    (st : St Sym) (pool : List (Nat × Op Sym)) :
    St Sym × List (Nat × Outcome) :=
  pass ctx st (wiredpool plan cap w ctx st.g pool)

/-- Every verdict of a wired pass is the visit of a
    candidate that passed every gate of the bounded
    pass at the pass's starting graph: the pass's
    verdicts are its visits (passfold), the visited
    list is a permutation of the wired pool
    (isortkeyperm), and the wired pool's members are
    gated (wiredgates). -/
theorem wiredvisits [DecidableEq Sym]
    (plan : Sched.Plan) (cap w : Nat) (ctx : Ctx Sym)
    (st : St Sym) (pool : List (Nat × Op Sym))
    (p : Nat × Outcome)
    (hp : p ∈ (wpass plan cap w ctx st pool).2) :
    ∃ ic ∈ pool, ∃ st',
      relevant ctx st.g ctx.cands ic.2 = true ∧
      canddepth ic.2 ≤ cap ∧
      Sched.fuelof plan (ruleof ic.2) ≠ 0 ∧
      p = (ic.1, (visit ctx ctx.cands st' ic).2) := by
  obtain ⟨extra, vs, hops, hsteps, hrun, hsum,
    hspent, hverdicts, hlen, hfst, hcount, hprop⟩ :=
    passfold ctx (isortkey st.g
      (wiredpool plan cap w ctx st.g pool)) (st, [])
  simp only [List.nil_append] at hverdicts
  have hpeq : (wpass plan cap w ctx st pool).2 = vs := by
    have e : (wpass plan cap w ctx st pool).2 =
        ((isortkey st.g
          (wiredpool plan cap w ctx st.g pool)).foldl
            (vstep ctx) (st, [])).2 :=
      congrArg Prod.snd (passeq ctx st
        (wiredpool plan cap w ctx st.g pool))
    rw [e, hverdicts]
  rw [hpeq] at hp
  obtain ⟨ic, hic, st', hpform, -⟩ := hprop p hp
  have hicw : ic ∈ wiredpool plan cap w ctx st.g
      pool :=
    (isortkeyperm st.g
      (wiredpool plan cap w ctx st.g pool)).mem_iff.mp
      hic
  obtain ⟨hpool, hcone, hdepth, hfuel⟩ :=
    wiredgates hicw
  exact ⟨ic, hpool, st', hcone, hdepth, hfuel,
    hpform⟩

/- ## The report back (fires, through the scheduler's
   step function) -/

/-- Report one fire to the scheduler: the step
    function under the caller's reading of merge and
    growth, keeping the plan where the step refuses —
    a refusal the wired pass's fuel gate has already
    excluded for the plan in force at the pass, and
    which a later report in the same fold can still
    meet once an allowance is spent. -/
def report (p : Sched.Plan) (r growth : Nat)
    (merged : Bool) : Sched.Plan :=
  (Sched.step p r growth merged).getD p

/-- A reported merge restores the rule's allowance to
    the base and clears its stall count — the
    scheduler's proved step behavior (stepmerge),
    carried through the report. -/
theorem reportmerge {p : Sched.Plan} {r growth : Nat}
    (hfuel : Sched.fuelof p r ≠ 0)
    (hr : r < p.fuel.length)
    (hs : r < p.stall.length) :
    Sched.fuelof (report p r growth true) r =
        p.base ∧
      Sched.stallof (report p r growth true) r =
        0 := by
  cases hstep : Sched.step p r growth true with
  | none =>
      exfalso
      have hsome : Sched.step p r growth true ≠
          none := by
        unfold Sched.step
        rw [if_neg hfuel]
        simp
      exact hsome hstep
  | some p' =>
      have hget : report p r growth true = p' := by
        simp [report, hstep]
      rw [hget]
      exact Sched.stepmerge hstep hr hs

/-- A reported fire without a merge refreshes the
    rule's allowance to the base divided by two to
    the new stall count — the scheduler's proved
    backoff (stepfuel), carried through the report. -/
theorem reportbackoff {p : Sched.Plan}
    {r growth : Nat}
    (hfuel : Sched.fuelof p r ≠ 0)
    (hr : r < p.fuel.length) :
    Sched.fuelof (report p r growth false) r =
      p.base / 2 ^ (Sched.stallof p r + 1) := by
  cases hstep : Sched.step p r growth false with
  | none =>
      exfalso
      have hsome : Sched.step p r growth false ≠
          none := by
        unfold Sched.step
        rw [if_neg hfuel]
        simp
      exact hsome hstep
  | some p' =>
      have hget : report p r growth false = p' := by
        simp [report, hstep]
      rw [hget]
      exact Sched.stepfuel hstep hr

/-- Report a whole pass back: for each pool candidate
    whose verdict in the pass was a resolution, one
    fire of its kind's rule, growth one, counting as
    a merge exactly when the candidate's terms all
    stood collected at the pass's starting graph. -/
def reportall [DecidableEq Sym] (_ctx : Ctx Sym)
    (g : Graph Sym) (p : Sched.Plan)
    (pool : List (Nat × Op Sym))
    (verdicts : List (Nat × Outcome)) : Sched.Plan :=
  pool.foldl (fun acc ic =>
    match verdicts.find? (fun v => v.1 = ic.1) with
    | some (_, .resolved _) =>
        report acc (ruleof ic.2) 1
          ((termsof ic.2).all (collectedb g))
    | _ => acc) p

/- ## The wired sweeps -/

/-- The wired sweeps: the run's sweeps over the wired
    pool, the scheduler plan threaded through — each
    pass reads the plan in force at its start, and
    the pass's resolved visits are reported back
    before the next pass reads the pool again. The
    stop condition and the fuel are the run's own. -/
noncomputable def wsweeps [DecidableEq Sym]
    (cap w : Nat) (ctx : Ctx Sym) :
    Nat → Sched.Plan → St Sym →
      List (Nat × Op Sym) →
      St Sym × List (Nat × Outcome) ×
        List (Nat × Op Sym) × Bool × Sched.Plan
  | 0, plan, st, pool => (st, [], pool, false, plan)
  | fuel + 1, plan, st, pool =>
      let (st', verdicts) :=
        wpass plan cap w ctx st pool
      let plan' :=
        reportall ctx st.g plan pool verdicts
      let aside := asideof pool verdicts
      if st'.ops.length = st.ops.length then
        (st', verdicts, aside, true, plan')
      else
        let (st'', rest, left, stopped, plan'') :=
          wsweeps cap w ctx fuel plan' st' aside
        (st'', verdicts ++ rest, left, stopped,
          plan'')

/-- One step of the wired sweeps, unfolded. -/
theorem wsweepseq [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) (fuel : Nat) (plan : Sched.Plan)
    (st : St Sym) (pool : List (Nat × Op Sym)) :
    wsweeps cap w ctx (fuel + 1) plan st pool =
      let (st', verdicts) :=
        wpass plan cap w ctx st pool
      let plan' :=
        reportall ctx st.g plan pool verdicts
      let aside := asideof pool verdicts
      if st'.ops.length = st.ops.length then
        (st', verdicts, aside, true, plan')
      else
        let (st'', rest, left, stopped, plan'') :=
          wsweeps cap w ctx fuel plan' st' aside
        (st'', verdicts ++ rest, left, stopped,
          plan'') := rfl

/-- A stopping wired sweep step: the state is the
    wired pass's state. -/
theorem wsweepsone [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) (fuel : Nat) (plan : Sched.Plan)
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hstop : (wpass plan cap w ctx st pool).1.ops.length = st.ops.length) :
    (wsweeps cap w ctx (fuel + 1) plan st pool).1 =
      (wpass plan cap w ctx st pool).1 := by
  rw [wsweepseq]
  dsimp only
  rw [if_pos hstop]

/-- A growing wired sweep step recurses on the aside
    pool at the wired pass's state, under the reported
    plan. -/
theorem wsweepsmore [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) (fuel : Nat) (plan : Sched.Plan)
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hstop : (wpass plan cap w ctx st pool).1.ops.length ≠ st.ops.length) :
    (wsweeps cap w ctx (fuel + 1) plan st pool).1 =
      (wsweeps cap w ctx fuel
        (reportall ctx st.g plan pool
          (wpass plan cap w ctx st pool).2)
        (wpass plan cap w ctx st pool).1
        (asideof pool
          (wpass plan cap w ctx st pool).2)).1 := by
  rw [wsweepseq]
  dsimp only
  rw [if_neg hstop]

/-- A stopping wired sweep step: the verdicts are the
    wired pass's verdicts. -/
theorem wsweepsstopv [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) (fuel : Nat) (plan : Sched.Plan)
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hstop : (wpass plan cap w ctx st pool).1.ops.length = st.ops.length) :
    (wsweeps cap w ctx (fuel + 1) plan st pool).2.1 =
      (wpass plan cap w ctx st pool).2 := by
  rw [wsweepseq]
  dsimp only
  rw [if_pos hstop]

/-- A growing wired sweep step: the verdicts are the
    wired pass's verdicts followed by the recursion's. -/
theorem wsweepsmorev [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) (fuel : Nat) (plan : Sched.Plan)
    (st : St Sym) (pool : List (Nat × Op Sym))
    (hstop : (wpass plan cap w ctx st pool).1.ops.length ≠ st.ops.length) :
    (wsweeps cap w ctx (fuel + 1) plan st pool).2.1 =
      (wpass plan cap w ctx st pool).2 ++
        (wsweeps cap w ctx fuel
          (reportall ctx st.g plan pool
            (wpass plan cap w ctx st pool).2)
          (wpass plan cap w ctx st pool).1
          (asideof pool
            (wpass plan cap w ctx st pool).2)).2.1 := by
  rw [wsweepseq]
  dsimp only
  rw [if_neg hstop]

/-- The wired sweeps, folded: the final state is
    reached by one gated trace from the start, the
    budget sum is kept, and the spend never falls —
    sweepsfold's statement over the wired sweeps,
    proved by its argument with the wired pass's fold
    (passfold) at each step. -/
theorem wsweepsfold [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) :
    ∀ (fuel : Nat) (plan : Sched.Plan) (st : St Sym)
      (pool : List (Nat × Op Sym)),
    ∃ extra,
      (wsweeps cap w ctx fuel plan st pool).1.ops =
        st.ops ++ extra ∧
      Steps ctx.kinds (RGate ctx) st.g
        (wsweeps cap w ctx fuel plan st pool).1.g
          extra ∧
      (wsweeps cap w ctx fuel plan st pool).1.g =
        run ctx.kinds st.g extra ∧
      (wsweeps cap w ctx fuel plan st pool).1.left +
        (wsweeps cap w ctx fuel plan st pool).1.spent =
          st.left + st.spent ∧
      st.spent ≤
        (wsweeps cap w ctx fuel plan st pool).1.spent := by
  intro fuel
  induction fuel with
  | zero =>
      intro plan st pool
      refine ⟨[], ?_, Steps.nil, ?_, rfl,
        Nat.le_refl _⟩
      · simp [wsweeps]
      · simp [wsweeps, run]
  | succ fuel ih =>
      intro plan st pool
      obtain ⟨extra1, vs, hops1, hsteps1, hrun1,
        hsum1, hspent1, hverdicts1, hlen1, hfst1,
        hcount1, hprop1⟩ :=
        passfold ctx (isortkey st.g
          (wiredpool plan cap w ctx st.g pool))
          (st, [])
      have hpass : wpass plan cap w ctx st pool =
          ((isortkey st.g
            (wiredpool plan cap w ctx st.g pool)).foldl
              (vstep ctx) (st, [])) :=
        passeq ctx st
          (wiredpool plan cap w ctx st.g pool)
      have hops1' : (wpass plan cap w ctx st pool).1.ops = st.ops ++ extra1 := by
        rw [hpass]; exact hops1
      have hsteps1' : Steps ctx.kinds (RGate ctx)
          st.g (wpass plan cap w ctx st pool).1.g
            extra1 := by
        rw [hpass]; exact hsteps1
      have hrun1' : (wpass plan cap w ctx st pool).1.g = run ctx.kinds st.g extra1 := by
        rw [hpass]; exact hrun1
      have hsum1' : (wpass plan cap w ctx st pool).1.left +
          (wpass plan cap w ctx st pool).1.spent =
            st.left + st.spent := by
        rw [hpass]; exact hsum1
      have hspent1' : st.spent ≤
          (wpass plan cap w ctx st pool).1.spent := by
        rw [hpass]; exact hspent1
      by_cases hstop :
          (wpass plan cap w ctx st pool).1.ops.length = st.ops.length
      · have h1 := wsweepsone cap w ctx fuel plan st
          pool hstop
        refine ⟨extra1, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1]; exact hops1'
        · rw [h1]; exact hsteps1'
        · rw [h1]; exact hrun1'
        · rw [h1]; exact hsum1'
        · rw [h1]; exact hspent1'
      · have h1 := wsweepsmore cap w ctx fuel plan st
          pool hstop
        obtain ⟨extra2, h2ops, h2steps, h2run, h2sum,
          h2spent⟩ := ih
          (reportall ctx st.g plan pool
            (wpass plan cap w ctx st pool).2)
          (wpass plan cap w ctx st pool).1
          (asideof pool
            (wpass plan cap w ctx st pool).2)
        refine ⟨extra1 ++ extra2, ?_, ?_, ?_, ?_,
          ?_⟩
        · rw [h1, h2ops, hops1', List.append_assoc]
        · rw [h1]
          exact stepstrans hsteps1' h2steps
        · rw [h1, h2run, hrun1', runappend]
        · rw [h1]; omega
        · rw [h1]; omega

/-- Every verdict of the wired sweeps is the visit of
    a pool candidate that passed every gate of the
    bounded pass at its pass's starting graph, under
    the plan in force at that pass: the first pass's
    verdicts by wiredvisits, the recursion's by
    induction, its pool a sub-pool of the original
    (asideof is a filter). -/
theorem wsweepsgates [DecidableEq Sym] (cap w : Nat)
    (ctx : Ctx Sym) :
    ∀ (fuel : Nat) (plan : Sched.Plan) (st : St Sym)
      (pool : List (Nat × Op Sym))
      (p : Nat × Outcome),
    p ∈ (wsweeps cap w ctx fuel plan st pool).2.1 →
    ∃ ic ∈ pool, ∃ (plan' : Sched.Plan)
      (g : Graph Sym) (st' : St Sym),
      relevant ctx g ctx.cands ic.2 = true ∧
      canddepth ic.2 ≤ cap ∧
      Sched.fuelof plan' (ruleof ic.2) ≠ 0 ∧
      p = (ic.1, (visit ctx ctx.cands st' ic).2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro plan st pool p hp
      simp [wsweeps] at hp
  | succ fuel ih =>
      intro plan st pool p hp
      by_cases hstop :
          (wpass plan cap w ctx st pool).1.ops.length = st.ops.length
      · have h1 := wsweepsstopv cap w ctx fuel plan
          st pool hstop
        rw [h1] at hp
        obtain ⟨ic, hpool, st', hcone, hdepth, hfuel,
          hpform⟩ :=
          wiredvisits plan cap w ctx st pool p hp
        exact ⟨ic, hpool, plan, st.g, st', hcone,
          hdepth, hfuel, hpform⟩
      · have h1 := wsweepsmorev cap w ctx fuel plan
          st pool hstop
        rw [h1] at hp
        cases List.mem_append.mp hp with
        | inl hp1 =>
            obtain ⟨ic, hpool, st', hcone, hdepth,
              hfuel, hpform⟩ :=
              wiredvisits plan cap w ctx st pool p
                hp1
            exact ⟨ic, hpool, plan, st.g, st', hcone,
              hdepth, hfuel, hpform⟩
        | inr hp2 =>
            obtain ⟨ic, haside, plan', g, st', hcone,
              hdepth, hfuel, hpform⟩ := ih
              (reportall ctx st.g plan pool
                (wpass plan cap w ctx st pool).2)
              (wpass plan cap w ctx st pool).1
              (asideof pool
                (wpass plan cap w ctx st pool).2)
              p hp2
            have hpool : ic ∈ pool := by
              simp only [asideof, List.mem_filter] at haside
              exact haside.1
            exact ⟨ic, hpool, plan', g, st', hcone,
              hdepth, hfuel, hpform⟩

/- ## The wired run -/

/-- One wired run of the algorithm: the run of
    section 8 with its sweeps wired — intake and the
    target step are the run's own, the pool the
    intake leaves is routed through the bounded pass
    at every pass, and the result record closes the
    same way. At a budget of zero the presentation is
    the run's own. -/
noncomputable def wresolve [DecidableEq Sym]
    (plan : Sched.Plan) (cap w : Nat) (ctx : Ctx Sym)
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
    let (fst, verdicts, _, _, _) :=
      wsweeps cap w ctx (pool.length + 1) plan tst
        pool
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

/-- The wired run, decomposed: the output graph is
    reached from the input graph by one gated trace,
    it is the fold of that trace, and the record's
    trace is that trace — runsteps' statement and
    argument, with the wired sweeps' fold
    (wsweepsfold) in place of the sweeps'. -/
theorem wrunsteps [DecidableEq Sym]
    (plan : Sched.Plan) (cap w : Nat) (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym) :
    ∃ ops, Steps ctx.kinds (RGate ctx) g
        (wresolve plan cap w ctx budget g).out ops ∧
      (wresolve plan cap w ctx budget g).out =
        run ctx.kinds g ops ∧
      (wresolve plan cap w ctx budget g).ops =
        ops := by
  by_cases hb : budget = 0
  · have hout : (wresolve plan cap w ctx budget g).out = g := by
      simp [wresolve, hb]
    have hops : (wresolve plan cap w ctx budget g).ops = [] := by
      simp [wresolve, hb]
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [hout]; exact Steps.nil
    · rw [hout]; simp [run]
    · exact hops
  · have hout : (wresolve plan cap w ctx budget g).out =
        (wsweeps cap w ctx
          ((intake ctx budget g).2.1.length + 1)
          plan
          (targetstep ctx (intake ctx budget g).1).1
          (intake ctx budget g).2.1).1.g := by
      simp only [wresolve, if_neg hb]
    have hops : (wresolve plan cap w ctx budget g).ops =
        (wsweeps cap w ctx
          ((intake ctx budget g).2.1.length + 1)
          plan
          (targetstep ctx (intake ctx budget g).1).1
          (intake ctx budget g).2.1).1.ops := by
      simp only [wresolve, if_neg hb]
    obtain ⟨hg, hops0, -, -, -, -, -⟩ :=
      intakeok ctx budget g
    obtain ⟨extrat, htops, htsteps, htrun, -⟩ :=
      targetsteps ctx (intake ctx budget g).1
    obtain ⟨extras, hsops, hssteps, hsrun, -, -⟩ :=
      wsweepsfold cap w ctx
        ((intake ctx budget g).2.1.length + 1) plan
        (targetstep ctx (intake ctx budget g).1).1
        (intake ctx budget g).2.1
    have hsteps : Steps ctx.kinds (RGate ctx) g
        (wresolve plan cap w ctx budget g).out
        (extrat ++ extras) := by
      rw [hout]
      rw [hg] at htsteps
      exact stepstrans htsteps hssteps
    refine ⟨extrat ++ extras, hsteps,
      stepsrun hsteps, ?_⟩
    · rw [hops, hsops, htops, hops0]
      simp [List.append_assoc]

/-- Claim one for the wired run, by claim one's own
    argument: a wired run on a valid graph produces a
    valid output graph, and the growth relation holds
    from the input to the output. The wiring narrows
    which candidates a pass visits; it does not touch
    what a visit may apply, so soundness is inherited,
    not reproved. -/
theorem wclaimone [DecidableEq Sym]
    (plan : Sched.Plan) (cap w : Nat) (ctx : Ctx Sym)
    (budget : Nat) (g : Graph Sym)
    (hv : Valid ctx.kinds g) :
    Valid ctx.kinds
        (wresolve plan cap w ctx budget g).out ∧
      Growth ctx.kinds g
        (wresolve plan cap w ctx budget g).out := by
  obtain ⟨ops, hsteps, hrun, -⟩ :=
    wrunsteps plan cap w ctx budget g
  have hready : Ready ctx.kinds g ops :=
    stepsready (fun g' op hg lv w hop => by
      have hc := rgatecond ctx g' op hg
      rw [hop] at hc
      exact hc) hv hsteps
  constructor
  · rw [hrun]; exact runvalid ctx.kinds hready
  · rw [hrun]; exact rungrows ctx.kinds hready

end Wire
