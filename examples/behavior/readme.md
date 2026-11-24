# Behavioral qualification of a canonical equivalence join

The existing graph is authoritative. Its `Valid` invariant relates materialized
classes to a chain of append-only join records. It says nothing about whether
such a chain preserves external software behavior. This module supplies a
checked bridge without introducing another graph or changing that invariant.

## What generalizes

Read each symbolic term as the state reached in a declared transition semantics.
An action can be a program input, scheduler choice, external response, or another
declared continuation. A state can include memory, host facts, resources and
outcome distinctions. The observation must name what the consumer can see:
results, refusals, side effects, and, if required, their order. Timing/resource
axes are observable only under a declared execution and measurement model.

For a relational (possibly nondeterministic) transition system, `substitute`
proves matching finite observations for every ordered continuation when states
match current observations and simulate each other's labeled transitions.
`sound` transports this through the canonical log, not a shadow graph.
`checkedjoin` and `joinsubstitute` show that only the new join's equivalence
needs to be checked when the semantics, reader and observation contract stay
fixed. Non-join records cannot invent behavioral equivalence. This does not
decide unrestricted nondeterministic equivalence or establish fairness,
divergence sensitivity or equality of probabilities. Those are additional
observable semantics, not consequences of the finite-trace result.

For deterministic tables, `checkedtable` checks equal observations and
equal optional successor classes for every state/action in a verified complete
enumeration. `tablejoin` composes that certificate with the existing graph
operation. Conversely `coarsest` proves that equality of all finite ordered
observations is itself a bisimulation on deterministic partial tables. Thus
within a complete finite deterministic instance, the coarsest stable partition
loses no declared observation. Actual programs require an independently
justified term reading and transition coverage; the model cannot certify those
from a handful of runs.

## Exact scoped algorithm

Start by partitioning states by checked observation. Split on previous class
and the ordered vector of successor classes, distinguishing explicit refusal
from transition. An unresolved entry is not a refusal and cannot form a closed
table. Each changing round strictly splits a class. A fixed point is stable,
and any bisimulation is preserved by each refinement round because equivalent
states begin with equal observations and their matching successors survive the
previous round. Thus the fixed point is the coarsest stable partition. The
executable implementation demonstrates this finite algorithm; the Lean proof
checks the certificate and deterministic coarseness theorem, not the Python
loop implementation.

`verify` inspects a complete table and candidate class IDs independently of
the search. The example freezes the full table once, then checks each new
join by class lookup, without rerunning refinement. Its in-process certificate
identity is not portable across sessions; the durable replay below uses explicit
content and contract binding instead. The separate pair traversal checks reachable paired states and
distinguishes an observation or enabled-action mismatch. It is an independent
oracle in the replay. Refinement here is a simple full-scan baseline, not an
implementation of [Hopcroft's 1971 minimizer](https://www.cs.cmu.edu/~cdm/resources/Hopcroft1971.pdf)
and not a fastest-algorithm claim. Once table entries are present, a stable
class certificate can be checked by one signature per state and action plus
grouping. Constructing a complete faithful table is separately charged.

## Append and re-resolution

Append raw witnesses at acquisition time. A bounded or coarse equivalence is
a qualification for a particular projection/epoch. Do not put it in an
unscoped canonical equivalence class and then try to split that class when
evidence arrives. Either attach it as a scoped derived fact or encode the
contract identity in its projected terms before joining. A wider read is a
new checked projection of the same retained evidence; a previous proof still
speaks about the scope in which it was issued. A change of reader, actions,
environment, effects, evidence or order invalidates a certificate unless a
checked refinement connects the contracts. Old historical ratios need not stay
valid in a new query. No fresh runtime execution is claimed for a carried
observation.

## Replay

Run `python3 examples/behavior/check.py`. The checked receipt reports 200 seeded
finite machine controls compared to the independent pair oracle, plus three
real pieces of software. SQLite prefixes are replayed on fresh in-memory
databases and cached only by the exact seed lane and ordered prefix within the
same test. Equal observed rows split after rollback. Two redundant explicit
seed lanes remain equivalent under the declared two-step scope. Fifteen prior
prefix records are reused, and a full cold rebuild agrees. The finite horizon
is visible, not represented as a program termination. Python JSON objects
that are equal under unordered key/value observation split under observed
order. zlib's three different encodings agree under decoded bytes but split
when encoded bytes are observable. These are controls for representation,
order and transactional context, not claims about other versions or hidden
effects. `Behavior.emptyactions` and `continuationdiffers` are standing Lean
controls for the danger of an omitted action.

Full decidability does not follow from finite syntax or a finite collected
prefix: in a model with unbounded execution, compare a program that reports
success iff arbitrary code halts to one that never reports it. A general
decision procedure for that equivalence would decide halting. The constructive
claim is a reusable proof interface for any supplied semantics and exact
checking on a complete finite resolved domain, with honest open cases.


## Durable, scoped replay and concurrency

Run `python3 examples/behavior/durable.py`. It records two actual SQLite WAL
sessions that agree on both visible database values and open transaction state.
After the writer commits 0 → 1 → 0 in one session, the same next write succeeds
in the fresh session and returns `SQLITE_BUSY_SNAPSHOT` in the stale one.
[SQLite's isolation specification](https://sqlite.org/isolation.html) documents
this distinction. The fixture is a declared two-connection schedule, not a
complete SQLite transition extractor.

The replay stores immutable, typed content-addressed objects. The table binds
stable state/action IDs, semantics, projection and closed rows. Partition names
are not stored: reload reconstructs classes by canonical order and verifies
them. The qualification separately binds that table to a lineage, release,
coverage declaration, extractor and checker. The caller must supply the
expected qualification and trusted prior head; the same table can serve both
lineages, but one lineage cannot pick up the other's journal. The join journal
uses the qualification digest and prior head and appends without revisiting
the old entries during a live session. A clean Python subprocess reads,
reconstructs and checks the retained chain. Immutable records do not replace the
canonical graph; these are evidence objects for its scoped joins, not a second
class authority. This reference does not sign qualifications, warrant coverage,
prevent rollback without a separately retained trusted head, or promise
power-loss durability. Startup currently rechecks the full table and retained
journal. This is not a production storage or throughput benchmark.

`Binding.lean` proves exact structural equality and rejection across scopes,
append preservation, and composition with a synchronized environment that sees
only the declared component observation. The latter preserves finite ordered
behavior; it does not assert scheduler fairness, or cover a context with extra
access to hidden state. Lean does not verify the Python codec, SHA-256 or SQLite.

## Witness-prioritized search, separate from certification

Run `python3 examples/behavior/search_boundary.py`. The trace or example
selects work; a separately checked semantic relation justifies the join.
Search may hold temporarily expensive candidates without allowing an expensive
release successor. `SearchBoundary.lean` separates these using a qualified
state, a componentwise constructive release relation, and a fuelled loop; it
checks the step count and composes release progress for a fixed cost vector.
It does not assume a weight ranking is a proof or that two revisions compare
under incompatible observations or cost models.

The pure-integer fixture uses an independent polynomial normal form and a
deliberately restricted rewrite successor set, not a production e-graph.
An expanding 7 → 9 node step makes a 1-node result reachable. Two attempts give
different incumbents with a different initial branch order; a third attempt
finds the same 1-node result. A single observed equality at x=0 cannot admit
the unsupported x → 0 rewrite. The counted attempts are not CPU timings.
A real matcher must meter intermediate join work and allocations, including
failed attempts and maintenance. Backoff controls priority, not memory or
wall time. A witness defines a search starting point; a dependency cut can
exclude work only with a checked completeness argument or an explicit scope.

The control brute-forces ordered, disjoint nonempty child-subset pairs for AC
through 8 distinct atoms. Across all subsets their count is
`3^n - 2·2^n + 1`. This is a count of candidate binary partitions for explicit
enumeration, not a bound on every compressed e-graph. A cycle alone does not
imply infinitely many canonical nodes: a normalized wrap can re-emit the same
node. Reversed search is valid only for enumerable predecessor generation in
the declared search model, and extracted paths still require proof.

## Bidirectional policy control with conserved credit

Run `python3 examples/behavior/guided.py`. The reference uses a finite
indexed directed rewrite graph, typed first-order disagreement residuals with
shared mismatch variables, an AC-invariant typed operator/leaf bag, supplied
witness-count tie breaks, and a deterministic four-plus-one selection policy.
The 80/20 control is for selection slots, not a beam completeness guarantee.
A separate eight-edge control actually exercises an exploration slot.
Opposing frontier hits are stitched using inverses of the index, not claimed
inverses of the executable transformation; every edge replays forward under
an independent polynomial checker. Concrete disagreement may prune but
agreement never authorizes any edge. A witness is an endpoint only when a
candidate expression implementing that observation is separately specified.

UCB1 ranks indexed choices between witness rows using historical visits and
winning provenance, with deterministic ties; its statistical regret
assumptions are not asserted for this workload. Credit is at most once per
scope and endpoint pair with a strict residual decrease at the certified
collision. A successful collision ends the current search, so residual credit
carries to future work rather than retroactively making the completed search
cheaper. This control does not implement partial congruence-closure dividends.

Allocation and match counters use conserved accounts, with a finite reserve.
Credit transfers from reserve; it does not undo allocations or replenish
lifetime work. Lean checks the lifetime bound, debit and no-mint invariant.
Depth caps each anchored path. These are logical counters: upfront index
construction, oracle cost, actual bytes, rebuilding work and wall time are not
measured or certified by the counters. A production implementation must meter
or bound these separately. The example is not an Idol-native e-hypergraph
backend or a claim of order-independent completeness, exact shortest meeting,
or a general square-root speedup.

## Matched cap ablation

Run `timeout 55s python3 examples/behavior/ablate.py` on Linux. Each policy sees
the same 144 cases (12 ordered batches of the same 12 model instances with
witness order and per-input arc order permutations). Each batch gets the same
86 lifetime allocation tickets and 99 matcher tickets; each cone is limited
to depth 6. All oracle-success fixtures have a path of at most 6 edges.
The BFS oracle exhausts the finite directed fixture graph up to depth 6
independently of traversal priority, using exact polynomial equality as
the trusted fixture contract, also used by every policy. A matching trace
does not replace that test. Each policy uses its own process with a 4-second CPU limit, 512 MiB
address-space limit and 6-second watchdog; a 55-second watchdog wraps the suite.
Timing includes index, oracle and scheduler passes; three raw timing
samples, whole-worker peak RSS including Python startup, and traced Python
allocation peaks are recorded separately. None
is a stable receipt field to compare byte-for-byte on another computer.
This does not report end-to-end e-graph timings, per-match allocated
bytes, real-world coverage, or a statistical performance win.

The baseline is a bounded one-way breadth-first variant with the exact
checker; it is separate from the strictly downhill control. Leave-one-out
runs remove matching factors, and the upfront-reserve control spends exactly
the same total potential credit without requiring a dividend. Rejected budget
attempts are unknown, not false-equivalence claims. The no-witness-prune run
still checks every actual merge. No restart occurred in these fixtures.

## Epoch-local provenance arena

Build with `cc -std=c11 -Wall -Wextra -Werror -O2 examples/behavior/arena.c -o /tmp/arena`,
then run `/tmp/arena`. The reference uses one 16-byte node per local
provenance ID, a flat overflow slab, and fixed depth buckets with a touched
generation. Depth decreases strictly along all premise edges, so shared
contributions are aggregated before the one visit to that node. Replacing
a first derivation with a valid shallower one preserves all existing incoming
depth inequalities; it does not guarantee the stored depths of descendants are
globally shortest. The control tests a shared bridge, duplicate roots,
multi-premise overflow, self-cycle and longer-cycle refusal, depth replacement
and tag rollover. The bounded overflow slab counts even tail slots made stale
by a shorter replacement. At the end of the epoch the local arena is reset
by advancing its bounds; the rare generation rollover clears the scratch
tags. No queue insertion allocates heap memory.

At the declared capacity, the 16-byte layout is only the node component.
The receipt includes the overflow slab and credit scratch. A production
implementation must also bound its e-node-to-ID map, merge-event records,
classes and matcher state; the example is not an integrated e-graph.
Congruence records must be reconstructable from checked premises and cannot
be replaced by a `BASE` token in an exported certificate. Persist qualified
join evidence and scope in the canonical ledger; persist only versioned
aggregates for scheduling, not the full speculative arena. No reward or
bonus is itself a proof or an authorization to mint fuel.
