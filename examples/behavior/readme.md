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
identity is not portable across sessions; a durable implementation must bind
the exact table and contract and check that binding before reuse. The separate pair traversal checks reachable paired states and
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
