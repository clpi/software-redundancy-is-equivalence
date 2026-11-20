# The resolution algorithm — specification

## Status, printed on the spec

This document is the specification of the resolution
algorithm for the redundant compute program. It is
settled intent about the algorithm's shape, as directed
by Chris on 2026-11-19 at 15:46 PST: a rigorously
defined algorithm, with all edge cases accounted for,
that resolves the various levels of resolution for
arbitrary compute availability as projections onto the
same source of truth hypergraph, over the entire scope
of all changes that provably can be resolved.

It is not implemented behavior: no code and no proof in
this lane implements it, and this lane writes no Lean
and runs no gate. It is not verified behavior: nothing
in it has been checked by a gate. The claims in it are
proposed semantics at the strength each claim's own
state line gives, and no other strength.

Four states are kept distinct throughout: settled
intent, proposed semantics, implemented behavior,
verified behavior. Every claim in this document carries
exactly one of three state lines, printed with the
claim and collected in section 18:

- theorem to be: the exact statement a proof must
  establish is given; the claim is proposed semantics
  until that proof exists and is gated.
- premise: the claim rests on a named premise outside
  the model; its falsification route is given with it.
- open gap: the point is not decided; the gap is named
  in section 19 with its owner, and the interim rule
  the algorithm follows until it is decided is stated
  where the gap is used.

No claim in this document stands as bare prose. A
sentence that is not under a claim is a definition, a
rule of the procedure, or a citation.

## 1. Citation rule, and what this spec does not do

This spec projects onto `spec.md` and cites it; it
redefines nothing of that document. In particular:

- Levels, the finite resolved upper bound, the view,
  and reconciliation are `spec.md` section 7, cited as
  sections 7.1, 7.2, 7.3, and 7.4 below.
- The only lattice is `spec.md` section 4. Every order,
  bound, join of states, and union in this algorithm is
  that lattice or a reading of it. This algorithm
  introduces no second lattice, no meet, and no order
  of its own on graphs.
- Scopes and arbitrary compute availability rest on
  `spec.md` section 3. The three named scopes and the
  widening rule are taken as given.
- The four operations and the growth relation are
  `spec.md` sections 8.2 and 8.3. Every append this
  algorithm makes is one of those four operations,
  applied as there defined, and its output must satisfy
  that growth relation.
- Colors, qualifications, and filtered views rest on
  `spec.md` section 9, and derived views on its
  section 12.
- The algorithm is the item named as not decided in
  `spec.md` section 14, owned there by the follow-on
  lane. This document is that lane's specification.

Where `spec.md` and this document could be read to
differ, `spec.md` governs the model and this document
is in error; the reading is recorded as a case under
the extension rule of section 17, never settled by
silent choice here.

## 2. Inputs

A run of the algorithm takes exactly these inputs.
Each is a value of the model of `spec.md`, or a finite
list of such values, or a value defined in section 4
of this document. A run with any other input is not a
run of this algorithm.

1. Graph. A valid graph, in the sense of `spec.md`
   section 5.2, reached from the empty graph by the
   operations of its section 8.2 alone. Call it the
   input graph. The run never edits it; the run's
   output is a new graph value grown from it, in the
   sense of section 3 below.
2. Target. Either a level value, in the sense of
   `spec.md` section 7.1 (a name, a finite term list,
   a scope), or a scope together with a finite term
   list, from which the target level is formed by
   taking the caller's level name for that list. A run
   has one target. A run with two targets is two runs.
3. Availability. A compute availability value, defined
   in section 4.2: a ceiling scope and a budget, in one
   of the two forms there stated. Availability in any
   other form is gap three of section 19; the algorithm
   does not translate it.
4. Candidates. A finite list of candidate changes,
   defined in section 4.1, in a fixed input order. The
   candidates are the entire scope of the run: the
   algorithm resolves changes drawn from this list and
   from the target, and no others. The phrase all
   changes that provably can be resolved means, in this
   spec, exactly: every candidate in this list that
   passes the scope test of section 5, the relevance
   test of section 8 step 3, and the witness test of
   section 8 step 5, at a cost the budget can pay at
   its turn, together with the target itself under the
   same tests. A change not in the list is not silently
   omitted; it was never presented, and a later run may
   present it.
5. Intent. A finite list of intent items, defined in
   section 4.3, possibly empty. Intent composes by
   section 13. A run with no intent items skips
   section 13 and its derived set is the empty state.
6. Filters. A finite list of filter predicates,
   possibly empty, each a decidable predicate on
   colors, supplied as a value. Filters name readings
   of the graph under `spec.md` section 9; they are
   gap seven of section 19 as to their language, and
   are used here only as readings, under section 11.
7. Witness check. A decidable check that takes a
   candidate and returns pass or fail, supplied as a
   value. What the check does against the ground the
   witness names is gap six of section 19. Its verdict
   is taken as data; its honesty is premise two of
   section 14.3.

Finiteness of every list above is by construction of
the inputs, and finiteness of the run's problem space
is derived from that, in the manner of `spec.md`
section 4.3: a qualification names its software, its
criteria, and the behavior intended under them, and
the candidate list is that naming made finite. No
claim in this document quantifies over an unbounded
space of behavior.

## 3. Outputs, and the growth condition

A run produces exactly these outputs.

1. Output graph. One graph value. It is reached from
   the input graph by applications of the four
   operations of `spec.md` section 8.2, in the order
   the procedure of section 8 applies them, and by no
   other step. Projections are onto the same graph:
   the output is the one hypergraph grown, never a
   second graph, never a graph per level, and never a
   view stored as a graph (`spec.md` section 7.3).
2. Result record. A derived value, defined in
   section 4.4: one line per candidate and one line
   for the target, each line stating resolved,
   deferred, or refused, with the reason named where
   it is not resolved, the counted spend of the run,
   the budget left, and the bound record of the target
   as taken at its recording moment, or the words bound
   not taken where section 10.4 applies. The result
   record is a reading. It is not appended to the
   graph, it is not a level, and it is never fed back
   as a witness.
3. Derived set. The singular derived set of section 13,
   where intent is present: one state of the lattice of
   `spec.md` section 4, constructed in one construction.
   It is a reading that directs the run's later steps;
   it is not a graph and it is not stored.

Claim one, soundness of output. State: theorem to be.
Exact statement: for every run, the input graph is
valid, the output graph is valid in the sense of
`spec.md` section 5.2, and the growth relation of
`spec.md` section 8.3 holds from the input graph to
the output graph: the input log is a prefix of the
output log, every level of the input is recorded in
the output with the same terms and scope, every term
collected in the input is collected in the output,
every pair equivalent in the input is equivalent in
the output, and every color of the input stands on the
output edge holding those terms. The proof must
establish this by induction on the steps of section 8,
using only that each step is an operation of
`spec.md` section 8.2 and that each such operation
preserves validity and satisfies growth there.

Claim two, one graph only. State: theorem to be.
Exact statement: every value a run produces that
carries terms, edges, or colors is either the output
graph, a view in the sense of `spec.md` section 7.3, a
bound state in the sense of its section 7.2, the
derived set of section 13 of this document, or the
result record; and of these only the output graph is a
graph value, the others being states, lists of edges
read whole, or record lines, none of which is ever an
input to a later step except as a reading that selects
candidates or terms. The proof must establish this by
inspection of the steps of section 8: no step
constructs a graph value other than by an operation of
`spec.md` section 8.2 on the running graph.

## 4. Values the algorithm uses

### 4.1 Candidate

A candidate is a record of five fields, each a single
value: a kind, a term list, a level name, a witness,
and a painter.

- The kind is one of the four operation kinds of
  `spec.md` section 8.2, named by that section's kind
  symbols: admit, join, record, paint. A candidate of
  no other kind exists in this algorithm; a proposed
  change of another kind is refused at intake, with
  reason kind not admitted, and is a case for
  section 17 if its kind is genuinely new.
- The term list is the list the operation acts on: one
  term for admit and for paint, two terms for join,
  the level's term list for record.
- The level name is the name of the level at which the
  change is resolved, or the level free name of
  `spec.md` section 8.1 where the change is level free.
- The witness is a symbol naming the ground, as in
  `spec.md` section 8.1: a proof, a derivation in a
  derived view, or a measurement at a named pin. The
  fixed empty name symbol in this field means no
  witness is presented.
- The painter is a symbol naming who paints, for paint
  candidates and for the colors a qualification paints
  as it appends; for other kinds it is the level free
  name where no painter applies.

A candidate is well formed when its term list has the
length its kind requires, its terms are terms of the
grammar of `spec.md` section 2, and, for join, its two
terms are given in a fixed order as presented. A
candidate that is not well formed is refused at
intake, with reason form, and no spend is charged
beyond the intake test of section 7.

### 4.2 Availability

An availability value is a pair: a ceiling and a
budget.

- The ceiling is a scope: one of the three scopes of
  `spec.md` section 3, or an appended predicate of the
  same form that carries a declared rank, under
  section 5.2 of this document. The ceiling bounds
  which scope the run may resolve under, by the
  widening rule of `spec.md` section 3.2.
- The budget is a count of steps, in the cost unit of
  section 7, in one of two forms. Form one: a natural
  number, given by the caller. Form two: the word
  full, meaning the caller places no limit of their
  own, and the budget is then fixed before the run
  starts as the dry count of section 7.4, a natural
  number computed from the inputs alone. There is no
  third form, and no run has an infinite budget as a
  value: form two is a finite count, derived from
  finite inputs, and a run under it still ends by the
  termination argument of section 15.

Availability is arbitrary in exactly this sense: the
ceiling may be any scope in the widening order, the
budget may be any natural number including zero, and
the algorithm's behavior at every value of each is
defined in this spec, in sections 5, 7, 10, and 16,
and registered as cases in `cases.md`. Nothing in the
procedure branches on why the availability is what it
is, on a venue, or on a caller.

### 4.3 Intent item

An intent item is a record of three fields: a term,
being a symbolic expression of the grammar of
`spec.md` section 2, read as an expression of intent;
a painter, naming the intent's source as a color
painter under `spec.md` section 9.1; and a witness,
naming the ground on which this intent is stated, as
in section 4.1. Intent stated in any form other than a
term is gap four of section 19: the algorithm does not
read prose, criteria in words, or a qualification's
name into terms.

### 4.4 Result record

A result line is a record of: the candidate or target
it reports on, an outcome word (resolved, deferred, or
refused), a reason word where the outcome is not
resolved, drawn only from the reason list of
section 16.1, the counted cost charged to that
candidate, and the epoch in the output log at which
its last append stands, or the word none. The result
record is the list of result lines in candidate input
order, followed by the target line, the total spend,
and the budget left. Two runs with the same inputs
produce the same result record; this is claim four.

## 5. Effective scope and widening

### 5.1 Effective scope

The effective scope of a run is the narrower, in the
widening order of `spec.md` section 3, of the target's
scope and the availability ceiling. Narrower is read
by the nesting `spec.md` section 3.1 requires the
rebuild to prove: the trivial scope inside the first
order scope inside the full scope, with appended
scopes placed by their declared rank under
section 5.2. Where the target's scope and the ceiling
are the same, that scope is the effective scope.

A term is in the run when it satisfies the effective
scope, tested by the scope predicate as a Bool value
of `spec.md` section 3. A term outside the effective
scope is unresolved by this run: it is absent from the
output graph unless it was already collected in the
input graph, its state in the result record is
deferred with reason scope, and it is never
represented by a placeholder term, a dummy symbol, or
a coarser stand in (`spec.md` section 3.2 rule 4). A
coarser reading of it may be resolved as its own term
at its own level where that reading is itself a
candidate or a target term in scope; it is then
resolved as itself, not as a substitute.

### 5.2 Rank of appended scopes

An appended scope predicate, of the form `spec.md`
section 3.1 allows, must carry in the input a declared
rank: its place in the widening order, stated as the
named scope it sits directly above, or the words below
trivial. A candidate or target under an appended scope
with no declared rank is deferred with reason rank,
and the point is gap two of section 19.

Claim three, scope soundness. State: theorem to be.
Exact statement: in every run, every term a step of
the run admits, joins, records, or paints on was
either already collected in the input graph or
satisfies the effective scope at the moment of the
step; and no term outside the effective scope is
admitted by the run. The proof must establish this by
inspection of the steps: the scope test of section 8
step 4 is the only gate to an operation, and every
operation application in section 8 is below that gate.

### 5.3 Widening across runs

Widening is a relation between runs, not a step inside
one. A later run with a wider ceiling resolves under
the wider effective scope; every term the earlier run
resolved stays resolved, under the same spelling and
in the same edge grown forward, by claim one and by
`spec.md` section 13 claim seven, which this algorithm
inherits and does not restate. No run widens its own
ceiling midway: the availability is fixed at intake
for the whole run, so the effective scope is one value
throughout, and a change of availability is a new run
on the output graph. This is the resume rule of
section 16.3.

## 6. Deterministic order

The procedure visits work in one fixed order, defined
here in full. An implementer has no ordering choice.

1. Intake order is candidate input order. It is the
   final tie break everywhere below, and the order of
   the result record.
2. Scope rank order: work is grouped by the rank of
   the scope its terms require, narrowest first. The
   rank a term requires is the narrowest named scope
   that admits it: trivial terms first, then first
   order terms that are not trivial, then full scope
   terms that are not first order, with appended scopes
   interleaved by declared rank. This is the trivial
   first order of `spec.md` section 3.2 made into a
   visiting order.
3. Cost order: within one scope rank, work is visited
   in nondecreasing counted cost, the cost of
   section 7 counted at visiting time against the
   running graph, as section 7.3 provides.
4. Kind order: within one scope rank and one cost,
   work is visited in the kind order admit, join,
   paint, record, except that the target's own record
   is taken first of all, under section 9.2, before any
   candidate is visited.
5. Sweeps: the procedure repeats whole passes over the
   work list in the order above until a full pass
   resolves nothing new, under section 8 step 7. A
   candidate deferred for cost in one pass is visited
   again in the next; a candidate refused is not
   visited again in the run.

Determinism is therefore a property of the inputs
alone: same graph, same target, same availability,
same candidate list in the same order, same intent,
same filters, same witness check, same output.

Claim four, determinism. State: theorem to be. Exact
statement: two runs with equal inputs, in the sense
above, produce output graphs whose edge lists agree up
to state equivalence in the sense of `spec.md`
section 4.1, whose logs are equal as lists, and whose
result records are equal. The proof must establish
this from the fixed order of this section and the
determinism of each operation of `spec.md` section 8.2
as a function.

A permutation of the candidate input order is a
different input. For it, `spec.md` section 7.4 clause 4
and its section 13 claim six bound what may differ:
the final partition and the final color sets may not,
the log order and the counted spend may. This is
registered as a case, not claimed here beyond the
citation.

## 7. Cost and budget accounting

### 7.1 The cost unit

One step is one of the following, and nothing else is
charged:

- one application of one operation of `spec.md`
  section 8.2, including an application that changes
  no edge, since each such application appends a log
  entry there;
- one witness check of one candidate of kind join,
  paint, or record, with the caching rule of
  section 7.2. An admit candidate is not witness
  checked: admission asserts no equivalence, and its
  witness is recorded in its entry as presented, under
  premise two of section 14.3;
- one intake test of one candidate, charged once per
  candidate at intake, covering its form test, its
  scope test, and its relevance test.

Scope tests, parts readings, bound readings, view
readings, filter readings, and derived set readings
are not charged: they are readings of values already
present, in the sense of `spec.md` section 7.3, and
charging for a reading would make the recorded bound
depend on how often it was read. Real time, energy,
and venue cost are not the cost unit; the relation of
the counted unit to them is premise one of
section 14.3.

### 7.2 Witness check caching

Within one run, a witness check verdict for a pair of
a candidate, read by its five fields, and its witness
is cached as a run local reading. A second visit to a
candidate with the same five fields in the same run
takes the cached verdict and is charged no check step.
The cache is not appended to the graph, is not carried
between runs, and is never a witness for anything.

### 7.3 Cost of a candidate at a graph

The cost of a candidate at a given graph is the number
of operation applications its resolution would apply
from that graph, plus, for kinds join, paint, and
record only, one witness check where the cache of
section 7.2 does not already hold its verdict, counted
by its kind:

- admit: one operation (the admission), whether or not
  the term is already collected, and no check.
- join: one operation for the join itself, plus one
  admission operation for each of its two terms not
  collected in the given graph, those admissions being
  part of the join operation's own step as `spec.md`
  section 8.2 operation 2 states, and counted here so
  the budget sees the whole step before it starts.
- paint: one operation, where its term is collected in
  the given graph. Where its term is not collected,
  the candidate has no cost at that graph: it is not
  resolvable from that graph by painting, since
  `spec.md` section 8.2 operation 4 requires a
  collected term, and this algorithm does not invent
  an admission to supply one. It is deferred with
  reason collected, and may become resolvable in a
  later sweep if another candidate admits the term.
- record: one operation for the recording, plus one
  admission operation for each term of its level not
  collected in the given graph, counted as for join.

Cost is therefore a function of a candidate and a
graph, computable before the candidate is started,
and nonincreasing as the graph grows: growth only
collects more terms, so the admission part can only
fall, and the operation part is fixed by kind.

### 7.4 The dry count for the full form of budget

Where the budget is given in form two of section 4.2,
it is fixed at intake as follows. Count, for the
target, its cost at the input graph under
section 9.2's atomic record rule. Count, for each
candidate in input order, one intake test, one witness
check, and its cost at the input graph, taking the
paint cost of an uncollected term as one. Sum these.
That sum is the budget. It is an upper bound on the
spend of the run, since actual costs are counted
against a graph that only grows (section 7.3), each
candidate is witness checked at most once (section
7.2), and each candidate is charged its intake test
once. The run under form two can therefore still end
with budget left; budget left is reported, not treated
as an error, under section 16.2.

### 7.5 Atomicity against the budget

An operation application is atomic against the
budget: it is started only when the budget left is at
least its counted cost, where a join or record
candidate's counted cost includes its admission sub
steps as section 7.3 provides, and it then completes
and is charged in full. Where the budget left is below
a candidate's counted cost at its visit, the candidate
is not started, no sub step of it is applied, and it
is deferred with reason budget. The one partial form
allowed is across candidates, never inside one: where
an earlier candidate in the same run has already
applied admissions that a later join would have needed
as sub steps, those admissions stand, being growth
under claim one, and the later join's cost is counted
again at its own visit against the graph as it then
stands. Budget exhaustion therefore never leaves a
half applied operation, a half merged edge, or a half
recorded level in the output graph.

## 8. The procedure

A run is these steps, in this order, and no others.
Each step states its input, its effect, and the
section that governs its edge cases. An implementer
implements exactly these steps.

Step 0, validate. Read the input graph's validity in
the sense of `spec.md` section 5.2. If the value given
as the graph is not valid, the run does not start: no
output graph is produced, and the result record is the
single line graph not valid. No step of this algorithm
repairs a graph, since the model of `spec.md`
section 8.3 has no repair step.

Step 1, intake. For each candidate in input order,
charge one intake test and test, in this order: form
(section 4.1), kind admitted, scope of its terms
against the effective scope (section 5.1), and
relevance (step 3 below, tested here for the record
line and tested again at each visit, since relevance
grows). A candidate failing form or kind is refused,
with its reason. A candidate failing scope is
deferred, with reason scope. Intake appends nothing
to the graph. Where the budget is zero, no intake test
is charged or run: every candidate line states
deferred with reason budget, by presentation alone,
and the run proceeds to step 2 with all work deferred.

Step 2, fix the run values. Fix the effective scope
(section 5.1), the budget (section 4.2, with
section 7.4 where form two is given), the visiting
order (section 6), and the empty running graph, being
the input graph as the run's current value. Fix the
derived set of section 13 where intent is present;
where intent is absent, the derived set is the empty
state and step 6 is skipped.

Step 3, relevance, defined. A candidate is relevant at
a graph when at least one of the following holds at
that graph: one of its terms is a member of the
current bound reading of the target (section 10.2);
one of its terms is a term of the target level; it is
a join with one term a member of the current bound
reading and the other term any term in scope, this
being the route by which new information is captured
into the bound; one of its terms is a member of the
derived set of section 13; one of its terms is a
part, at any depth under the parts function of
`spec.md` section 2.2, of a term of the target level
or of a term in the current bound reading; or its kind
is record and its level name is the target's name. A candidate
relevant under no clause is outside this projection:
it is deferred with reason target, is charged nothing
beyond intake, and the run spends nothing on it. This
test is what makes the run a projection onto the
target's bound rather than a resolution of the whole
candidate list without regard to target.

Step 4, record the target. Apply the target recording
of section 9.2, atomically: test the target's terms
against the effective scope, count its cost, test the
budget, check its witness where the target carries
one as a record candidate, and either apply the record
operation of `spec.md` section 8.2 operation 3 in
full, with its bound taken and recorded as section 10
provides, or defer the target whole, with the reason
named, and apply none of its admissions as part of the
record. Where the target is deferred, the run
continues with candidates: their appends are growth
whether or not the target is recorded in this run,
and the target line of the result record states
deferred with its reason. Separate admission
candidates for the target's terms, if present in the
list, are ordinary candidates and are unaffected.

Step 5, visit a candidate. At each visit, in the order
of section 6, for the candidate at the head of the
remaining work: recompute its relevance at the running
graph; if it is not relevant, mark it deferred with
reason target and set it aside for this pass. Recompute
its scope test; a candidate whose terms have not
changed cannot pass a scope test it failed, so this is
a reading, not a new charge. Count its cost at the
running graph (section 7.3). If it has no cost at that
graph (the paint case of section 7.3), defer it with
reason collected and set it aside for this pass. If it
is a paint of the intended mark, test the two filter
rule of section 12.3 at the running graph; where the
rule is not met, defer it with reason filter and set
it aside for this pass. The tests of this step are
applied in the order given here, and the first reason
that holds is the reason on the result line, so a line
never carries two reasons. If
the budget left is below its counted cost, that cost
being the whole charge of the candidate under
section 7.3, check included where its kind carries
one, defer it with reason budget and set it aside for
this pass; do not stop the pass, since a later
candidate may cost less. Otherwise, where its kind
carries a check and its verdict is not cached, charge
the check and run it: on fail, refuse the candidate
with reason witness, the check already charged, and
apply nothing, the operation part of its cost never
charged. On pass, or where its kind carries no check,
apply its operation or operations as one atomic budget
unit under section 7.5, charge the operation part of
its cost, and mark it resolved. A join whose two terms are the same
term by spelling is applied as `spec.md` section 8.2
operation 2 provides (admission, then no edge change,
then the entry), is marked resolved, and is expressly
not a witness of redundancy, since redundancy requires
two distinct spellings in one edge (`spec.md`
section 10); its result line carries the note self.

Step 6, compose intent. Where intent is present, the
derived set of section 13 was fixed at step 2 as a
reading of the input graph. After each pass, recompute
the derived set as a reading of the running graph: its
overlap part can only grow, by section 13.3. Terms
entering the derived set for the first time make
candidates that name them relevant at their next
visit, under step 3. The derived set itself appends
nothing; every append it occasions is a candidate's
operation at step 5, on that candidate's own witness.

Step 7, sweep to a fixed point of the pass. Repeat
passes over the set aside and unvisited work, in the
order of section 6, until a full pass resolves no
candidate and admits no term. Then stop visiting. The
stop condition is exact: at the stop, every candidate
is in exactly one of resolved, refused, or deferred,
and every deferred candidate carries a reason that
holds at the output graph, in the sense that visiting
it once more at the output graph, with the budget
left, would defer it again for that reason. This last
property is claim six.

Step 8, close. Produce the output graph, being the
running graph. Produce the result record (section
4.4): one line per candidate in input order, the
target line, the total spend counted under section 7,
and the budget left. Where intent is present, the
final derived set reading is named in the target line
by its term count and edge count as readings, not
appended. The run ends. Nothing is carried to a later
run except the output graph itself, as the next run's
input graph, and the result record as a reading.

Claim five, termination. State: theorem to be. Exact
statement: every run ends. The proof must establish
this from: the candidate list is finite; each pass
either resolves at least one candidate or is the last
pass; a resolved candidate is never visited as
unresolved again; refused candidates are never
revisited in the run; the budget and the candidate
count are natural numbers, so the measure of pairs of
unresolved candidate count and, within a pass, unvisited
count falls in the stated order at every step; and the
sweep of step 7 therefore reaches a pass that resolves
nothing after at most one more pass than the number of
candidates.

Claim six, coverage at the stop. State: theorem to be.
Exact statement: at the stop of step 7, for every
candidate not resolved, at least one of the following
holds at the output graph and is the reason on its
result line: its terms fail the effective scope; it is
not relevant at the output graph; it is a paint
candidate whose term is not collected in the output
graph; its witness check was run and failed, in which
case it is refused, not deferred; or its counted cost
at the output graph is greater than the budget left.
The proof must establish this by the stop condition of
step 7 and the cost monotonicity of section 7.3, and
must establish the cost clause in its strong form:
cost counted at the output graph is the least cost at
which that candidate could be resolved from the output
graph by any sequence of operations of `spec.md`
section 8.2, since any such resolution must apply the
candidate's own operation and must first collect each
of its terms not collected there.

## 9. Projection rule per level

### 9.1 One rule for every level

There is one projection rule, parameterized by the
level value alone. No level name, scope, or grain has
a rule of its own. This is the sense in which the
algorithm is not a case analysis over levels: a new
level is a new value of the same type, resolved by the
same rule, and section 17 governs how a level whose
shape the rule cannot take is registered, which is by
append, never by a new branch written into this
section.

The projection of a graph at a level is the view of
`spec.md` section 7.3. Resolving a level, in this
algorithm, is the following composite, each part being
operations of `spec.md` section 8.2 and nothing else:
admit each term of the level that is in the effective
scope and not already collected; apply each candidate
join, paint, and record whose relevance and tests pass
under section 8; record the level itself under
section 9.2; and take its bound under section 10 at
the recording moment. The projection a caller receives
is then the view at that level in the output graph, a
derived value, reproducible from the output graph and
the level alone.

### 9.2 Recording a level, atomically

Recording the target, and recording any level named by
a record candidate, follows one rule. If a level of
the same name is already recorded in the running graph
with the same terms and the same scope, the recording
is a repeat witnessing in the sense of `spec.md`
section 8.2 operation 3: only the log entry is
appended, the bound recorded is the bound taken at
this moment as that operation provides, and no level
value is appended twice. If no level of that name is
recorded, the level value is appended with its terms
admitted first, as that operation provides. If a level
of the same name is recorded with different terms or a
different scope, the recording is refused with reason
name, nothing is appended, and the point is gap one of
section 19: `spec.md` section 8.2 does not decide
whether a second level value under one name may stand,
and this algorithm does not decide it for the model.

A record whose term list contains a term outside the
effective scope is deferred whole, with reason scope,
under the atomicity of section 8 step 4: no part of
its admissions is applied as part of the record. A
record with an empty term list is recorded as a level
with no terms: it admits nothing, its bound is the
empty state, and its view is the empty list. A record
is charged as section 7.3 provides, atomically under
section 7.5.

### 9.3 Coarser and finer levels

A coarser level and a finer level are two level values
under section 9.1, both appended to the one graph
under `spec.md` section 7.4. Their link is the parts
function of `spec.md` section 2.2 plus co-presence in
the one graph, and nothing else: this algorithm builds
no pairing, no translation, and no mapping between
levels. Where a finer term is a part, at any depth of
the parts reading, of a coarser term in the target,
that finer term is relevant under section 8 step 3
when it is itself named by a candidate or by the
derived set; the algorithm does not invent finer terms
by expanding parts on its own, since an expansion it
invented would be a term no witness presented. Parts
descent ends: a part is a head or an argument of a
form, each a strictly smaller tree than the form, and
terms are finite by `spec.md` section 2.2, so no parts
chain is infinite and no cycle of parts exists.

Claim seven, levels reconciled. State: theorem to be.
Exact statement: appending the target level and any
one further level to a graph by this algorithm, in
either order of the two runs, yields output graphs
whose edge partitions and color sets agree up to state
equivalence, whose recorded bounds are the bounds as
taken at their recording moments, and which both
satisfy growth from the starting graph. This is
`spec.md` section 13 claim six, inherited: the proof
must establish it for the operations as this algorithm
applies them, and may cite that claim's proof for the
operations themselves once that proof exists; until
then both stand as theorem to be, and neither is
upgraded by the other.

## 10. The bound: rule, reading, and bound reached

### 10.1 Taking the bound

The bound of the target is taken exactly as `spec.md`
section 7.2 provides, in its three steps and by no
other route: form the level's state; take the join, in
the lattice of `spec.md` section 4, of the singleton
states of its terms; saturate under the graph's
equivalence at the recording moment. The bound is
recorded in the record entry at that moment, as data:
the level's term list and the edge sets it met. It is
never recomputed as a record, never restated, and
never revised. Taking the bound is an effect of the
record operation; it is charged as part of that
operation and has no separate cost.

### 10.2 The bound reading

Distinct from the recorded bound, and named distinctly
as `spec.md` section 14 choice five requires, the
bound reading at a graph is the bound of section 10.1
recomputed as a reading at that graph: the state of
all terms equivalent in that graph to a member of the
target's state. The bound reading is used for the
relevance test of section 8 step 3 and for nothing
else. It only grows as the graph grows, by `spec.md`
section 13 claim five, second half, inherited here as
theorem to be at the same strength. It is never
recorded, never a witness, and never reported as the
bound.

### 10.3 Bound reached

Bound reached is the state of a run in which the bound
reading has stopped growing across a full pass: no
pass step admitted a term into an edge the bound
reading meets, and no join merged such an edge. At
bound reached, candidates whose terms stand outside
the bound reading and outside the derived set are
deferred with reason target, and claims about terms
outside the recorded bound are claims about unresolved
terms, of state unmeasured, as `spec.md` section 7.2
provides at its close. Bound reached is a normal end
state of a projection, not an error: it states that
this projection, at this resolution time, resolves
exactly its bound and no more.

### 10.4 Bound not taken

Where the target record is deferred at section 8
step 4, no bound is taken in the run. The result
record's target line states bound not taken with the
record's deferral reason. A later run that records the
target takes the bound then, at that later graph; no
bound is backdated to this run, since a bound is data
of its recording moment under section 10.1.

Claim eight, bound correctness. State: theorem to be.
Exact statement: the recorded bound of a target, where
one is taken, is a state of the lattice of `spec.md`
section 4; it is the least state that contains the
target's state and is closed under the running graph's
equivalence at the recording moment; it is finite; and
the bound reading of the same target at any graph
grown from the recording graph contains the recorded
bound as a state, read by the lattice order. This is
`spec.md` section 13 claim five, inherited at the same
strength and with the same separation of record and
reading.

## 11. Views and filters

### 11.1 The view is a reading

The view of the output graph at the target is computed
as `spec.md` section 7.3 defines: the edges that meet
the target's bound, each edge whole, all of its terms
and all of its colors. A view is materialized only as
an index or a reading. It is never stored as a second
graph, never edited, and never fed back as evidence
about its own members: a candidate whose only witness
is that its terms stand together in a view is refused
with reason witness, since standing together in a view
is either co-membership in an edge, which needs no
candidate, or a reading across edges, which is not
equivalence under `spec.md` section 6.

### 11.2 Filtered views

A filtered view is the view read through one filter
predicate of section 2 input 6: the list of the view's
edges whose color list holds at least one color the
predicate passes. Filtering selects edges whole; it
never selects part of an edge, never removes a term or
a color from an edge, and never paints. The two
filters of `spec.md` section 9.2 are never conflated
in a filtered view: the observed filter and the
qualified filter are distinct predicates over distinct
color kinds, and a filter predicate that names the
qualified kind while reading only observed colors is
applied as written, as a reading, and yields whatever
it yields as a reading; the discipline about what may
be painted from it is section 12.3, not a property of
the reading.

An empty filtered view, where the predicate passes no
edge of the view, is a reading of no edges. It defers
nothing, refuses nothing, and paints nothing. A filter
that passes every edge yields the view itself. Both
are ordinary readings, registered as cases, and
neither is a special form in the procedure.

Claim nine, view growth. State: theorem to be. Exact
statement: under growth from the input graph to the
output graph of a run, every edge of the view of the
input graph at the target is a subset, in terms and in
colors, of exactly one edge of the view of the output
graph at the target, and the same holds for every
filtered view under a fixed predicate. The proof must
establish this from the growth relation of `spec.md`
section 8.3 and the definitions of its section 7.3,
as that section itself states the property.

## 12. Overlapping qualifications on target edges

### 12.1 Coexistence is the rule

A qualification, under `spec.md` section 9.2, reaches
the run in exactly two ways, and the algorithm takes
both by the same steps: as candidates that append new
terms, equivalences, or a level, painted with the
qualification's colors as they go; and as paint
candidates on edges already collected. Where two
qualifications paint the same edge, in one run or
across runs, their colors coexist on that edge as
distinct color entries, differing in painter, epoch,
or mark. There is no priority among painters, no
single color of an edge, and no overwriting: a paint
step never removes, alters, or shadows a color already
on the edge, including a color of the same painter at
an earlier epoch, which stands as its own fact under
`spec.md` section 9.1.

### 12.2 An edge spanning levels

An edge that meets the bounds of two levels, or that
holds terms named at two levels, is one edge. A paint
candidate on any of its terms paints the edge whole,
as `spec.md` section 8.2 operation 4 provides, and the
painting is therefore visible in the views of both
levels, each view taking the edge whole under
section 11.1. No step of the algorithm splits such an
edge by level, copies it per level, or paints a part
of it. A join candidate joining a term of such an edge
to a further term merges the further term's edge into
this one edge, whole, under the join operation; the
spanning grows, it never divides.

### 12.3 The two filter rule in painting

A paint candidate whose mark is the qualification mark
intended, under `spec.md` section 9.2, is applied only
where both an observation entry and an intent entry
for that qualification are present for that edge, as
colors already on the edge or as entries appended
earlier in the same run on their own witnesses. Where
either is absent at the candidate's visit, the
candidate is deferred with reason filter, and may pass
in a later sweep if the missing entry is painted
meanwhile. Where the run ends with it still deferred,
no intended mark stands on that edge from this run.
An intended mark is never painted from observation
alone or from intent alone, in this algorithm, in any
sweep, under any budget.

Claim ten, coloring. State: theorem to be. Exact
statement: for every edge of every output graph of a
run, the color list of that edge, read up to
membership, is the union of the color list it had in
the input graph and the colors the run's paint steps
added, each added color applied under sections 12.1
and 12.3; color union on an edge is commutative,
associative, and idempotent up to membership; and an
intended mark of a qualification stands on an edge
only where an observation entry and an intent entry
for that qualification both stand for that edge in the
output graph. The first parts are `spec.md` section 13
claim four, inherited; the last part must be proved
for the painting discipline of section 12.3 as its
premise, as that claim itself provides.

## 13. Composition of intent: the singular derived set

### 13.1 The three source states

Where intent is present, the derived set is
constructed from three states of the one lattice of
`spec.md` section 4, each a finite list of terms read
up to membership:

- Source one, stated: the state of the terms of the
  intent items, as spelled. Every intent item
  contributes its term, whether or not that term is
  collected in the graph.
- Source two, new: the state of terms presented in the
  run that are not yet captured in the graph: the terms
  of candidates and of the target that are not
  collected in the graph at the moment of construction,
  and that satisfy the effective scope. New information
  enters the derived set as itself, under its own
  spelling; no term enters source two by being a part
  of another term, a reading of another term, or a
  stand in for another term.
- Source three, overlap: the state of all terms
  standing in edges that meet source one in the graph,
  joined with the state of all terms standing in edges
  of any filtered view of the graph at the target whose
  edges hold a term of source one or a term of the
  target. Overlap is read off the one graph: collected
  edges whole, filtered views as readings under
  section 11.2. A term enters source three by standing
  in such an edge, and by no other route.

### 13.2 The one construction

The derived set is the join, in the lattice of
`spec.md` section 4, of the three source states:
stated joined with new joined with overlap, in that
order as a construction, the result being independent
of that order up to state equivalence by the lattice
laws of `spec.md` section 4.2. It is one state,
constructed in one construction, from all three
sources at once. There are no parallel derivations,
one per source, reconciled after the fact: a term of
the derived set is a member of the join, and its
provenance, where a reading needs it, is the set of
sources whose states contain it, read off the three
states, never a record of a separate derivation.

Composition across new information and across overlap
is therefore the same operation: both are joins into
the one state. A term that is both new and, once
admitted and joined on a witness, overlapping is a
member of the join once, read up to membership, at
every moment of the run at which the reading is taken.

### 13.3 The derived set as a reading that grows

The derived set is recomputed as a reading at step 2
of section 8 from the input graph, and after each pass
under section 8 step 6 from the running graph. Source
one is fixed by the intent items. Source two can only
shrink as a reading, as its terms become collected;
those terms pass into source three or stand as
collected members of the join in their own right, so
the join itself, read as a set of terms, never loses a
member under growth of the graph within the run.
Source three can only grow, since growth never
uncollects a term and never splits an edge (`spec.md`
section 8.3). The derived set directs relevance under
section 8 step 3 and paints nothing, joins nothing,
and admits nothing on its own: every append made
because a term stands in the derived set is a
candidate's append, on that candidate's witness,
charged to that candidate. Intent alone is never a
witness for an equivalence, and membership in the
derived set is never a witness for anything.

Where the derived set directs a paint of an intent
color, the painting follows section 12: the intent
entry is painted under the intent item's painter, on
the edge holding the term once collected, and a
qualification mark of intended is derived from it only
under the two filter rule of section 12.3, with the
observation entry standing as its own entry.

Claim eleven, composition. State: theorem to be.
Exact statement: the derived set of a run, at any
moment it is read, equals, up to state equivalence,
the join in the lattice of `spec.md` section 4 of its
three source states as defined in section 13.1 at that
moment; the join is commutative, associative, and
idempotent up to state equivalence, so the derived set
is independent of the order in which intent items and
candidates were presented, up to state equivalence;
the derived set is monotone in each source, in the
lattice order, so enlarging the intent list, the
candidate list, or the graph grows the derived set or
leaves it equal, never shrinks its term set; and no
term stands in the derived set that is not a member of
at least one source state. The proof must establish
each part from the lattice laws of `spec.md`
section 4.2 and the definitions of section 13.1, with
the growth clause resting on claim one.

Claim twelve, intent paints no equivalence. State:
theorem to be. Exact statement: if two distinct terms
stand in one edge of the output graph and did not
stand in one edge of the input graph, then a join
candidate naming those terms, or a chain of join
candidates whose merges compose to that edge, was
resolved in the run on its own witness; in particular
no intent item, derived set membership, filter, or
view is the witness of any new co-membership in any
output graph. The proof must establish this by
inspection of the steps of section 8: step 5 is the
only step that applies a join, and it applies it only
after the witness check of that candidate passes.

## 14. Pareto optimality, stated exactly

### 14.1 The axes, the alternatives, the comparison

The optimality claim is made over exactly three axes,
for a fixed input tuple in the sense of claim four,
and against exactly one class of alternatives.

- Axis one, resolved: the set of candidates resolved
  by the run, read by inclusion. More is better. The
  target is reported on its own line and is not counted
  in this axis, so two runs are compared on candidates
  alone.
- Axis two, spend: the total counted cost of the run,
  under section 7. Less is better.
- Axis three, waste: the counted steps spent on work
  that neither resolves a candidate nor is a necessary
  part of resolving one, where necessary is counted
  exactly as: an intake test of a candidate that is
  later resolved or whose refusal or deferral reason
  the test established; a witness check whose verdict
  the run used; and an operation application that is
  part of a resolved candidate's counted cost. Every
  other counted step is waste. This algorithm's waste
  is zero by the construction of sections 7 and 8:
  it takes no step outside intake, check, and atomic
  application, it never recomputes a recorded bound,
  it never rechecks a cached witness, and it never
  re-derives a witness carried forward in the graph,
  since a co-membership already in the graph needs no
  candidate at all.

The alternatives are: every procedure that takes the
same inputs, obeys the model of `spec.md` in that its
outputs are reached by the operations of its
section 8.2 alone and satisfy its growth relation,
obeys the widening rule of its section 3.2 in that it
resolves nothing outside the effective scope, and
respects the target's bound in that it resolves no
candidate this algorithm's relevance test would place
outside the projection at every graph it reaches. An
alternative that breaks the model, the scope rule, or
the projection is not a rival; it is a procedure
computing a different thing, and dominance over this
algorithm by such a procedure is not a falsification.

One alternative dominates this algorithm on these axes
when it is at least as good on all three axes and
strictly better on at least one: it resolves a
superset or the same set, spends no more or less, and
wastes no more or less, with at least one strict.
This algorithm is Pareto optimal for the cases it
handles when no alternative in the class dominates it.
The cases it handles are exactly the cases registered
in `cases.md` with state accounted; a case with state
gap is outside the claim until its gap closes, and the
claim's scope grows by the append rule of section 17
as cases are accounted, never by assertion.

### 14.2 The algorithm claim

Claim thirteen, Pareto optimal, algorithm. State:
theorem to be. Exact statement: for every input tuple,
no alternative in the class of section 14.1 dominates
the run of this algorithm on the axes of section 14.1.
The proof must establish the three parts separately.
Part one, no strict superset at no greater spend: by
claim six, every candidate this run leaves unresolved
has, at the output graph, a counted cost greater than
the budget left, or fails scope, relevance, collection,
or witness; an alternative resolving it as well as all
this run resolves must, from a graph grown from the
output graph, apply at least that candidate's counted
cost at the output graph, by the least cost clause of
claim six, and must therefore spend in total more than
this run spent plus the budget left, which is more
than the budget, which no run under the same
availability can spend; the scope, relevance,
collection, and witness clauses are closed to any
alternative by the class definition and the witness
check being a shared input. Part two, no equal resolved
set at lesser spend: any procedure resolving at least
the resolved set from the input graph must apply, for
each new collected term at least one admission, for
each new co-membership at least one effective join in
the sense of `spec.md` section 13 claim two, for each
record and paint at least its operation, and at least
one witness check per resolved join, paint, and record
candidate not already decided by a shared earlier
check; summed, that lower bound is this run's spend,
since this run applies exactly those steps and no
others. Part three, no lesser waste: waste is a
natural number and this run's waste is zero, so no
alternative wastes less. The proof must state the
lower bound of part two as a lemma over the log of
`spec.md` section 8.1, by induction on log length.

### 14.3 The methodology claim, and the premises

Claim fourteen, Pareto optimal, methodology. State:
premise. The methodology of which this algorithm is
the instance (scope rank first under the widening
rule, cost order within rank, atomic budget units,
sweeps to the stop condition of section 8 step 7,
witness before append, bound taken once at recording
and never recomputed) is Pareto optimal over the axes
of section 14.1 against every methodology whose
instances fall in the alternative class of
section 14.1. This is carried as a premise, not a
theorem to be, because a methodology ranges over
procedures not yet written, and no finite proof in
this repo quantifies over them. Falsification route:
exhibit one concrete input tuple, at a named graph pin
or as a concrete graph in the proof tree in the manner
of the controls of `spec.md` section 13, and one
written alternative procedure in the class, whose run
on that tuple dominates the run of this algorithm on
all three axes with at least one strict, the spend of
both runs counted under section 7 by a reader other
than the claimant. One such exhibition refutes the
claim as a campaign claim; it is then registered as a
case under section 17, and claim thirteen's proof
obligation is read again in its light. Owner of the
route: the algorithm lane, then the coordinator.

Premise one, counted cost stands for real cost. State:
premise. Within one operation kind, real compute cost
at a fixed venue is nondecreasing in the counted steps
of section 7, so a run that spends fewer counted steps
of a kind does not spend more real cost of that kind.
Falsification route: at a named pin and a named venue,
measure the real cost of the operation kinds on
concrete graphs of growing size; an exhibition that
one operation application costs more real cost than
two of the same kind, on the same venue and pin,
refutes the premise for that kind, and the axes of
section 14.1 must then be read as counted axes only,
which is stated here in advance as the premise's
failure mode, not discovered after it. Owner: the
measurement lane of the campaign.

Premise two, witness honesty. State: premise. A
witness check that passes means the witness the
candidate names is what it names: a proof the gate
will check, a derivation in a derived view, or a
measurement at its pin. This is the witness honesty
premise of `spec.md` section 13, inherited unchanged.
Falsification route: exhibit a candidate whose check
passes at a named pin while its named ground does not
exist or does not support the candidate; the
exhibition refutes the check, not the theorems, which
are proved from the entries. Owner: the proof lane.

Premise three, reading fidelity. State: premise. A
subject's symbol type and term readings are the
subject's own, as in `spec.md` section 13. The
algorithm proves and resolves facts about terms as
read, not about behavior they were read from.
Falsification route: exhibit a subject reading at a
named pin that maps two behaviors the subject counts
distinct to one term, or one behavior to two terms
with no equivalence witness; the exhibition is a case
under section 17 against the reading, not against the
algorithm. Owner: the subject's lane.

## 15. Termination, restated as a rule

Termination is claim five. As a rule for implementers:
no step of section 8 loops over anything but the
finite candidate list, the finite term lists of the
inputs, the finite edge list of the running graph, and
the parts readings of finite terms, which end by
section 9.3. A step that would loop over the graph's
growth, over all terms of a scope, or over all graphs
is not a step of this algorithm; scopes are predicates
tested on presented terms, never enumerated.

## 16. Refusals, deferrals, budget left, and resume

### 16.1 The reason list

A result line's reason is one word from this list, and
no other reason is ever given: form, kind, scope,
rank, target, collected, witness, budget, filter,
name, graph. Read in plain words: form, the candidate
is not well formed; kind, its kind is not one of the
four; scope, a term fails the effective scope; rank,
its scope carries no declared rank; target, it is not
relevant to this projection; collected, a paint term
is not collected; witness, its witness check failed,
or it presents no witness, or its only ground is a
view, spelling, an identifier, or a hash, the last
three being grounds `spec.md` section 6 forbids for
equivalence; budget, its counted cost exceeds the
budget left at the stop; filter, a mark's filter rule
of section 12.3 is not met; name, a level name is
already recorded with different terms or scope; graph,
the input graph is not valid. A refused line carries
one of form, kind, witness, name, or graph, being
reasons no later sweep of the same run can cure. Every
other reason is a deferral: a later sweep or a later
run may cure it, and the line states which.

### 16.2 Budget left

A run may end with budget left in exactly these
circumstances, each registered as a case: every
remaining candidate costs more than the budget left;
every remaining candidate is deferred for a reason
other than budget; the budget was form two and the dry
count overcounted, as section 7.4 provides; or the
candidate list is exhausted. Budget left is not waste
under axis three of section 14.1, since no step was
spent on it, and it is not carried between runs: a
later run takes its own availability as its own input.

### 16.3 Resume

A run that ends with deferred candidates is resumed
only as a new run whose input graph is the output
graph, whose candidate list is the deferred candidates
in their original input order, with the target and a
fresh availability as new inputs. No run state, cache,
or budget crosses.

Claim fifteen, resume composes. State: theorem to be.
Exact statement: let a first run end with budget left
unused only because each deferred candidate then cost
more than that budget left; let a second run resume it
under section 16.3 with availability whose ceiling
gives the same effective scope and whose budget is at
least the first budget left plus the added budget the
resumption presents; then the second run resolves
every candidate that a single run with the first
run's inputs and the summed budget, in the same
candidate order, would resolve, and the final edge
partition after the second run agrees with that single
run's partition up to state equivalence. The proof
must establish this from cost monotonicity
(section 7.3), the stop condition (section 8 step 7),
and order independence for appends (`spec.md`
section 7.4 clause 4). Where the first run ended with
budget left for a different reason of section 16.2,
the claim does not apply and the resumption is an
ordinary new run.

### 16.4 The unmeasured state

A term, candidate, or claim deferred or never
presented is unmeasured, in the sense of `spec.md`
sections 3.2 and 7.2: not resolved, not refuted, and
not absent in the sense of disproved. The result
record's word is deferred, and no line of it states or
implies that a deferred change cannot be resolved by a
later run with wider scope, a greater budget, a
painted missing entry, or a presented witness.

## 17. The caseless extension rule

### 17.1 What caseless means here

This algorithm is specified by rules over values
(section 4), not by a case analysis over inputs. Its
cases, in `cases.md`, are an accounting: a register
that every input shape the argument of this spec
enumerates is covered by a named rule and a named
claim, or is named as a gap. A new observation does
not break the algorithm; it is either already covered,
and the register gains a line saying which rule covers
it, or it is not covered, and the register and this
spec grow by append under section 17.2. Neither the
procedure of section 8 nor any rule of sections 5 to
16 is rewritten to accommodate a new case. Growth by
append is the only growth either document takes, as
the graph itself takes no other growth (`spec.md`
section 8).

### 17.2 How a new case is appended

A newly observed case is entered in `cases.md` by
append, in exactly this form, and in no other act:

1. Give the case the next number in its family of
   `cases.md`, or, if it fits no family, append a new
   family at the end of `cases.md` with the next family
   letter, its dimension named in its heading. Existing
   numbers, letters, and headings are never changed,
   renumbered, or moved.
2. The entry states: the observation and its source, at
   a named pin or a named record; the input instance,
   in the values of section 4, small enough to be
   checked by reading; what the algorithm as specified
   does on it, step by step by the steps of section 8;
   the rule and the claim that cover it, or the gap it
   opens; and its state, accounted or gap.
3. If the case is covered, nothing else changes: this
   spec is not edited, and the case is evidence that
   the covering rule holds on a new instance.
4. If the case is not covered, a gap is appended to
   section 19 of this spec with the next gap number, a
   name, and an owner, and an interim rule is appended
   as a new numbered paragraph at the end of the
   section the case touches, stating the most
   conservative behavior consistent with `spec.md`:
   defer, append nothing for that case, and state the
   reason. An interim rule never resolves a case the
   model has not decided.
5. If the case contradicts a claim of section 18, the
   claim is not edited. A state line is appended to the
   claim's entry in section 18 naming the case and the
   contradiction, and a superseding claim, if one is
   stated, is appended at the end of section 18 with
   the next claim number. The contradicted claim stands
   in the text as the record of what was claimed.
6. An entry in `cases.md` changes state only by a
   dated state line appended at the end of the entry,
   naming the act that changed it: a gap closed by a
   decision of its owner, a proof landed, or a
   superseding claim appended. Entries are never
   edited in place and never removed, as the log of
   `spec.md` section 8.1 is never edited or removed.

### 17.3 The enumeration that seeds the register

The seed register in `cases.md` is generated by
crossing the dimensions the argument of this spec
itself enumerates, and no other source: the state of
the graph (section 5 of `spec.md`); the kind and
collection state of a candidate (sections 4.1 and 7.3
here); the scope state of its terms (section 5 here
and section 3 of `spec.md`); the witness state
(sections 4.1 and 8 step 5 here, section 6 of
`spec.md`); the budget state at each sub step of a
compound candidate (section 7 here); the level and
bound state (sections 9 and 10 here, section 7 of
`spec.md`); the view and filter state (section 11
here, sections 7.3 and 9.2 of `spec.md`); the
qualification overlap state (section 12 here,
section 9.2 of `spec.md`); the intent and new
information state (section 13 here); the order and
repeat state (sections 6 and 16 here); and the refusal
state (section 16 here). A dimension value observed in
the world that is not a value of a dimension in this
list is itself a new case under section 17.2, opening
a new family; the list is therefore closed as a method
and open as a register, which is the caseless property
this section specifies.

## 18. Claims register

Every claim of this document, with its state. A claim
not in this list is not claimed.

- Claim one, soundness of output. Theorem to be.
  Section 3.
- Claim two, one graph only. Theorem to be. Section 3.
- Claim three, scope soundness. Theorem to be.
  Section 5.
- Claim four, determinism. Theorem to be. Section 6.
- Claim five, termination. Theorem to be. Section 8.
- Claim six, coverage at the stop. Theorem to be.
  Section 8.
- Claim seven, levels reconciled. Theorem to be.
  Section 9. Inherited from `spec.md` section 13
  claim six at the same strength.
- Claim eight, bound correctness. Theorem to be.
  Section 10. Inherited from `spec.md` section 13
  claim five at the same strength.
- Claim nine, view growth. Theorem to be. Section 11.
- Claim ten, coloring. Theorem to be. Section 12.
  Inherited in part from `spec.md` section 13 claim
  four.
- Claim eleven, composition. Theorem to be.
  Section 13.
- Claim twelve, intent paints no equivalence. Theorem
  to be. Section 13.
- Claim thirteen, Pareto optimal, algorithm. Theorem
  to be. Section 14.2.
- Claim fourteen, Pareto optimal, methodology.
  Premise, with falsification route. Section 14.3.
- Claim fifteen, resume composes. Theorem to be.
  Section 16.
- Premise one, counted cost stands for real cost.
  Premise, with falsification route. Section 14.3.
- Premise two, witness honesty. Premise, with
  falsification route. Section 14.3. Inherited from
  `spec.md` section 13.
- Premise three, reading fidelity. Premise, with
  falsification route. Section 14.3. Inherited from
  `spec.md` section 13.

No claim of this document is implemented behavior and
none is verified behavior. Each theorem to be becomes
implemented behavior only when a proof of its exact
statement exists in the proof tree, and verified
behavior only when the family gate checks that proof
at a named pin.

## 19. Open specification gaps, with owners

Each gap below is a point this spec does not decide.
Each names its owner: the owner decides it, by a
decision recorded in the repo this spec lives in, and
the gap closes only by the append acts of section
17.2, never by an implementer's choice.

- Gap one, level name reuse. A level name recorded
  with different terms or a different scope than a
  record candidate presents: whether a second level
  value under one name may stand is not decided by
  `spec.md` section 8.2 operation 3. Interim rule:
  refuse with reason name, append nothing (section
  9.2). Owner: the coordinator, as a change to
  `spec.md` sections 7.1 and 8.2 if the decision alters
  the model.
- Gap two, rank of appended scopes. The widening order
  among appended scope predicates beyond the three
  named scopes, where two appended scopes are declared
  above the same named scope, is not decided. Interim
  rule: an appended scope with no declared rank defers
  its work with reason rank (section 5.2); two scopes
  declared above the same scope are visited in input
  order, and that order is a reading of the input, not
  a rank. Owner: the coordinator.
- Gap three, availability in other forms. Availability
  given as time, money, a venue, or a rate has no
  translation into the ceiling and counted budget of
  section 4.2 in `spec.md` or here. Interim rule: the
  algorithm does not translate it; the caller supplies
  the counted form, and any translation the caller used
  is their premise, named in the run's record by the
  caller, not by this algorithm. Owner: the
  coordinator, with the measurement lane.
- Gap four, intent in other forms. Intent stated as
  criteria in words, as a qualification's prose, or as
  any value other than a term of the grammar has no
  reading into intent items (section 4.3). Interim
  rule: such intent is not an input; nothing is
  derived from it. Owner: the coloring and
  qualification lane.
- Gap five, two runs at once. Two runs on one graph at
  the same time, and the interleaving of their steps,
  are not specified: the model of `spec.md` is a
  sequence of appends, and this algorithm is one run.
  Interim rule: runs are taken in sequence, each on
  the output graph of the one before; no interleaving
  is a run of this algorithm. Owner: the coordinator.
- Gap six, the witness check itself. What checking a
  witness against its ground does, per ground kind, is
  not defined in `spec.md`: a proof is checked by the
  gate, a measurement by recompute at its pin, a
  derivation by reading the derived view, but the
  procedure that unifies these as one decidable check
  input is program practice, not model. Interim rule:
  the check is an input (section 2 input 7), its
  verdict is data, and premise two covers its honesty.
  Owner: the proof lane.
- Gap seven, the filter language. The language in
  which filter predicates over colors are stated and
  named has no scheme in `spec.md` section 9. Interim
  rule: a filter is supplied as a decidable predicate
  value and used as a reading only (section 11.2).
  Owner: the coloring and qualification lane.
- Gap eight, the target record at zero budget. Whether
  a run whose budget cannot pay the target's record
  counts as a projection of that target, though its
  candidates append growth, is not decided by
  `spec.md` section 7. Interim rule: the run proceeds,
  the target line states deferred and bound not taken
  (section 10.4), and no party calls the run a
  projection of the target until the owner decides.
  Owner: the coordinator.

## 20. A worked run

A small run, by reading, on abstract symbols. Let the
symbols be a, b, c, d. Let the input graph hold one
edge with terms atom a and atom b, painted with an
observation color of a qualification whose painter is
q, and no other edges. Let the target be a level named
t, with terms atom a and the form with head atom c and
one argument atom d, under the first order scope. That
form is first order and not trivial, since its
argument is an atom and its head is an atom, so its
required rank is first. Let availability be the first
order ceiling and a budget of seven steps in form one.
The target is presented with a witness naming a
measurement at a pin, so its record carries a check.
Let the candidates be, in input order: a join of atom b
and the form above, on a witness naming a measurement
at a pin; a paint of the intended mark of q on atom a;
and an admit of atom d. Let there be no intent and no
filters.

Intake charges three steps in total across the three
candidates and tests them: all are well formed, in the
effective scope, which is the first order scope, being
the narrower of the target scope and the ceiling.
Step 4 records the target: atom a is collected, the
form is not, so the record costs three steps, one
admission, one recording, and one witness check,
leaving one step of the
seven after intake and record are charged. The bound is
taken at that moment: the edges the target's terms
stand in are the edge of a and b and the new edge of
the form alone, so the recorded bound is the state of
atom a, atom b, and the form. The admit of atom d is
relevant, since atom d is a part of the form, but
parts relevance holds only where a candidate names the
term, which this one does; it costs one step. It is
visited before the join, by cost order within the
first rank. It resolves, spending the last step. The
join now costs one step, the join alone, both its
terms being collected, plus one witness check, and the
budget left is zero: it is deferred with reason
budget. The paint of intended is deferred with reason
filter, the first reason that holds at its visit under
section 8 step 5: the edge of a holds an observation
entry of q but no
intent entry of q, so section 12.3 forbids the paint
in this run at any budget. The run ends with budget
left zero, the output graph grown by the target record
and the admission of atom d, the join and the paint
deferred with their reasons named, and nothing outside
the bound claimed. A later run on the output graph
presenting the join, a paint of the intent entry of q
on atom a on its own witness, and the paint of
intended again, with a budget of nine steps counted
the same way, would spend three on intake, then take
the two paints first, at two steps each, since atom a
is of trivial rank and the form is of first rank: the
intent paint stands, the two filter rule is then met,
and the intended paint stands. It would then take the
join at two steps, check and join, on its own witness,
ending with budget left zero.

This worked run is an illustration of the rules, in
proposed semantics. It is not a claim, it is not a
control, and no proof obligation rests on it; the
controls are the proof lane's, in the proof tree.
