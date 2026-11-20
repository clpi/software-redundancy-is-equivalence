# The approach space — approaches by semantic axes

## Status, printed on this document

This document is the standing structure of the amendment
of 2026-11-20 (Chris, direct, 02:43 PST): find where any
approach would Pareto dominate on any semantic axis, and
structure and parametrically weight that space so it is
continuously searchable, solvable, and optimizable,
across the board, all of it represented in the
hypergraph, with no benchmark gaming.

It is settled intent about the space's shape, in the
form of `spec.md` and `algorithm.md`: definitions and
rules here bind every later append. It is not
implemented behavior in Lean: no Lean file of this
repository defines the space, and none is claimed to.
It is not verified behavior: the only gate result
claimed for this landing is the space validator's run
and the standing family gate's run, each named in the
landing record, at the landed pin. Readings entered in
the space register under `space/` are measured behavior
at exactly the strength of the record and pin each
reading cites, and proposed semantics wherever a reading
says proposed. Four states are kept distinct
throughout: settled intent, proposed semantics,
implemented behavior, verified behavior.

The estate view of this space is the closed loop
synthesis repository of the estate: it picks this space
up on its next refresh from this home. This home is the
authority; the estate view is a view, in the sense of
`spec.md` section 7.3, and is never a second source.

## 1. What the space is, in the model's own terms

The space is a registry in the sense of `spec.md`
section 11, standing beside the registry of witnessed
configurations in `registry/`, and built by the same
discipline:

- An approach is a term of the one hypergraph: a named
  method, algorithm, route, or weighting configuration,
  admitted by an append, never edited in place.
- An axis is a measure name in a fixed axis list (the
  register of section 3 of this document), as a measure
  name is fixed in `spec.md` section 11.3. An axis
  enters this list only with the agent proof definition
  of section 2. A named axis with no such definition is
  a named gap (section 5), never an axis.
- A reading is one approach's value on one axis, under
  one stated contract, at one named pin, with its
  evidence named. A reading is a color in the sense of
  `spec.md` section 9, painted by this register: the
  painter is the register, the kind is the axis, the
  mark is the reading's state and value, and the epoch
  is the append's position in the register's log.
- A configuration of this space is one approach's full
  reading vector: every axis of the register, each
  carrying a reading or an explicit unmeasured mark.
  Identity of a configuration is content equivalence of
  its vector, as in `spec.md` section 11.2; no digest
  is an identity.
- A weighting is an epoch of this register, in the
  sense of `spec.md` section 11.3: an appended weights
  record over a named subset of axes. A weighting
  excludes nothing, bounds nothing, and selects only
  within a frontier computed weight free (section 6).
- A verdict is an appended entry of the register
  (section 7). Verdicts are never edited; a later
  measurement appends a new verdict that supersedes by
  position, as provenance appends in section 11.2 of
  `spec.md`.

Why a new standing file and a new register directory,
rather than entries in `registry/`: the registry of
`spec.md` section 11 holds witnessed configurations of
the one graph under its five fixed measures, and its
builder and epochs are closed over that witnessed set.
The approach space has its own axis list, its own
subjects (approaches, not graph configurations), and
its own verdict kind. Mixing the two would overload an
existing kind, which `spec.md` section 9.1 forbids for
colors and which this document forbids for registers.
The pattern followed is therefore the home's own: a
standing specification file in the form of
`algorithm.md`, and a register directory in the form of
`registry/`, with a builder and validator beside the
data.

## 2. What an axis definition must carry

An axis is admitted to the register only when its entry
states all four of the following, at a resolution any
agent can apply without further judgment:

1. What is measured: the quantity, its unit, and its
   direction (which way is better), with any orientation
   stated in the entry, never applied silently.
2. On what contract: the battery, task set, or count
   procedure under which rival approaches are read, the
   same contract for every rival in a comparison.
3. At what grain: the unit of one reading (per instance,
   per epoch, per append prefix, per task, per claim, as
   the entry states).
4. What evidence a reading requires: the executed run,
   count, proof, or checker output a reading must cite,
   with its record and its pin. A reading with no
   evidence of the stated kind is not a reading; it is
   an unmeasured mark.

No axis is defined so that a favored approach wins by
construction: the contract is fixed before readings are
taken, the same contract binds every rival, held out
validation follows any down selection that steers work,
and losses and unmeasured marks are printed in the
register wherever they stand.

## 3. The axis register

Sources, all on disk in the estate records: the
candidate space measures and its six improvement axes
(candidate space record of 2026-11-19, and section 11.2
of the search specification in the frontier home at its
landed pin); the seven certification dimensions
(certification record of 2026-11-19, and the
certification specification in its home); the guidance
vector of the reversible search space (reversible
record of 2026-11-20, and the search specification in
the reversible home at `d05ff699`); the four declared
axes over weighting configurations (meta search lane
one record of 2026-11-20, landed at `c710c2a` in the
reversible home); and the amendment's own named axes
(visibility, workspacing, compositionality, compactness,
incrementality, reversibility, checkability,
derivability), each dispositioned below.

Axes are grouped by the family that named them. The
grouping is provenance, not priority: dominance is
computed over the whole register, axis by axis.

### 3.1 Candidate measures (candidate space, section 11.2 of its specification)

- novelty. What: the count a candidate adds that the
  carried set does not carry — one for its own term when
  new, plus one for each part not carried. Unit: count.
  Direction: higher is more new. Contract: the candidate
  record (its term and its parts) read against the
  carried list of the space it enters. Grain: per
  candidate. Evidence: the count itself, computed from
  the record and the carried list. Aliases: the source
  measure name `fresh`, and the phrase net newness. The
  guidance coordinate named not pre-existing is this
  axis read as a boolean; it is not a second axis.
- impact. What: the count of entries of the space that
  are composed from the candidate's term. Unit: count.
  Direction: higher reaches more of the space. Contract:
  composition read over the entered space at a named
  state. Grain: per candidate, per space state.
  Evidence: the count itself, computed from the space.
  Aliases: the source measure name `reach`. Note: the
  round two ranking figure suspended in the candidate
  record was a static reading of this axis under an
  extraction whose links were not compiler resolved;
  readings of this axis that steer work require resolved
  bindings, and the suspended ranking enters no verdict
  in this space.
- recombination. What: zero when the candidate's term
  is already carried; otherwise the count of its parts
  that are carried. Unit: count. Direction: higher is a
  more novel recombination of what exists. Contract: as
  novelty. Grain: per candidate. Evidence: the count
  itself. Aliases: novelty of composition, and the
  source measure name `blend`.
- solving. What: the count of gaps of the space that
  the candidate closes, under the closing relation of
  the candidate space. Unit: count. Direction: higher
  closes more gaps. Contract: the gap list of the space
  at a named state, with the closing relation applied
  uniformly. Grain: per candidate, per space state.
  Evidence: the count itself, computed from the gap list
  and the closing relation. Aliases: gap solving.

### 3.2 Improvement axes (candidate space, the six of its score)

Each of the six is a natural reading, higher is better,
evidenced as its entry states; a reading with no
evidence of the stated kind is absent, never scored as
zero or as intended.

- quality. What: the stated quality reading of the
  candidate's behavior. Unit: the contract's own (an
  exactness count, a checked score), named with the
  reading. Direction: higher is better. Contract: a
  checked comparison against the incumbent the candidate
  would replace, on the same instances. Grain: per
  candidate, per contract. Evidence: the executed
  comparison at a named pin. Aliases: better, and the
  source measure name `gain`. The guidance coordinate
  named much improved is this axis with a magnitude
  threshold stated by the reader; it is not a second
  axis, and a threshold used in a verdict is printed
  with the verdict.
- speed. What: the stated time reading. Unit: time, in
  the contract's stated form (a latency, a total, a
  percentile pair). Direction: less time is better; a
  reading enters any score in its stated orientation.
  Contract: a timed run at a named pin on a named venue,
  the same venue and workload for every rival. Grain:
  per run. Evidence: the timed run itself. Aliases:
  faster. This axis and the certification dimension
  named speed are one axis: the certification entry is
  this axis read under a harness contract (matched
  conditions, percentile readings, the count of measured
  axes at or better than the earlier state). Counted
  work (relaxations, rule checks, probes) is not time
  and never enters this axis; counted work enters
  incrementality or probes, as those entries state.
  Wall clock forms stand unmeasured wherever the records
  say so, and print so here.
- leanness. What: the count of duplicated behavior the
  candidate removes. Unit: count. Direction: higher
  removes more. Contract: the graph count of duplicated
  behavior before and after the candidate, on the same
  graph state. Grain: per candidate, per graph state.
  Evidence: the two counts. Aliases: less redundant, and
  the source measure name `lean`. This axis is a count
  over behavior, not the excess of `spec.md` section
  10: excess is a property of one graph's edges, and a
  leanness reading is a difference of counts across two
  states. The two are related and are never conflated.
- power. What: the count of behaviors the candidate
  makes derivable that were not derivable before. Unit:
  count. Direction: higher is more powerful. Contract:
  the derivability closure over the same recorded steps,
  before and after. Grain: per candidate, per step set.
  Evidence: the closure count itself. Aliases: more
  powerful. The amendment's named axis derivability is
  this axis: its source definition already measures it
  by the derivability closure count, so derivability
  enters as an alias, not a second axis.
- width. What: the count of distinct forms the
  candidate can state. Unit: count. Direction: higher
  is more expressive. Contract: enumeration of the forms
  under the candidate's own grammar, at a named state.
  Grain: per candidate. Evidence: the enumeration.
  Aliases: more expressive, expressive, and the source
  measure name `width`.
- ease. What: the character count of the shortest form
  that invokes the candidate. Unit: characters of the
  counted canonical form; layout is presentation and is
  not counted. Direction: fewer characters is better; a
  reading enters any score in its stated orientation.
  Contract: the canonical form of the shortest invoking
  expression, counted by the same counting rule for
  every rival. Grain: per candidate. Evidence: the
  counted form itself, printed with the reading.
  Aliases: more ergonomic, ergonomic, and the source
  measure name `ease`. This axis is about invoking a
  candidate; compactness (section 3.5) is about the size
  of an approach's own artifact. The measure type is the
  same and the subjects differ, so the axes stand apart,
  and a verdict may not trade one for the other.

### 3.3 Certification dimensions (certification specification, its sections 2 and 3)

Each dimension's value at a state is a stated function
of that state's appended measurement records, the same
function at every state; a measurement never rewrites a
prior record. A dimension with no executed measurement
at a state prints unmeasured there.

- coverage. What: the share of the comparator's verified
  capability surface the subject has built. Unit: the
  contract's row or case counts, built and partly stated
  separately, read in contract order. Direction: higher
  covers more. Contract: the subject's capability matrix
  against its comparator, each row audited at the state.
  Grain: per subject state. Evidence: the audit at the
  pin, row by row.
- fidelity. What: the faithfulness of the subject's
  behavior to its own stated contracts. Unit: count of
  executed contract battery tests passing. Direction:
  higher is more faithful. Contract: the subject's own
  full check target, executed whole in a named venue;
  the projection measured is named on the reading.
  Grain: per subject state. Evidence: the executed
  battery at the pin, with its run recorded.
- solvability. What: the subject's success on live
  tasks. Unit: count of tasks solved, over the task set
  size, both printed. Direction: higher solves more.
  Contract: the acceptance discipline of the task set —
  matched hardware, builds, state, permissions, and
  workload semantics, an effect counting only when
  independently confirmed; a simulated task set is a
  different contract from a live one and a reading names
  which it is. Grain: per task set run. Evidence: the
  executed run at a named pin. No executed campaign, no
  value: the axis prints unmeasured.
- reconversibility. What: the subject's ability to
  return a fixture or environment to a recorded prior
  state. Unit: count of state restore producers with an
  executed battery, the covered fixture shapes named.
  Direction: higher restores more. Contract: a producer
  records a pre state, drives to a named baseline,
  verifies by re observation, and restores the pre state
  when restorable. Grain: per subject state. Evidence:
  the producer's executed battery at the pin. This axis
  is not reversibility (section 3.5): this one counts
  restore producers in a subject; that one tests one
  action's inverse by fresh observation. Related, and
  kept apart.
- reweightability. What: whether the subject's weighting
  can be replaced on the fly without changing the
  qualified result set and without recomputing what the
  set is. Unit: a value exists exactly when the subject
  carries a weighting surface and an executed check that
  replacing the weighting leaves the qualified set
  unchanged; the value is that check's outcome over its
  named instance set. Direction: a passing check over a
  larger set is better. Contract: the reweighting check
  in the shape proved for the search layer in the
  frontier home. Grain: per subject state. Evidence: the
  executed check at a named pin. No weighting surface,
  no value: unmeasured.
- setup. What: the weight of standing the subject up.
  Unit: count of pinned external inputs in the subject's
  own manifest, read whole; supporting prerequisite
  counts are evidence, not the value. Direction: fewer
  inputs is better; a reading enters any score in its
  stated orientation, and an improving claim must show a
  strictly smaller count. Contract: the manifest read
  whole at the state. Grain: per subject state.
  Evidence: the manifest itself at the pin.

### 3.4 Guidance coordinates (reversible search space)

The guidance vector of the reversible record is explicit
— novelty, not pre-existing, much improved, unique,
compositional synthesis potential — each coordinate a
reading with named evidence. Three of its five
coordinates are aliases of axes above, dispositioned in
their entries: novelty is the axis novelty; not
pre-existing is novelty read as a boolean; much improved
is quality with a stated threshold. The remaining two
stand as axes here.

- uniqueness. What: the count of qualified frontier
  results, on a named instance set, that this approach
  reaches and no other entered approach reaches. Unit:
  count, over the instance set size, both printed.
  Direction: higher reaches more that nothing else
  reaches. Contract: every entered rival run on the same
  instance set, selections compared member by member.
  Grain: per instance set run. Evidence: the executed
  runs at a named pin, with the comparison printed.
  Aliases: unique.
- compositionality. What: the count of compositions, on
  a named composition battery, under which the approach
  behaves as the composition of its behaviors on the
  parts — applying the approach to a composed input
  yields the composed result, with no approach change
  and no added premise. Unit: count, over the battery
  size, both printed. Direction: higher composes more.
  Contract: a battery of paired part and whole tasks,
  the same battery for every rival, each pair executed.
  Grain: per battery run. Evidence: the executed battery
  at a named pin, pair by pair. Aliases: compositional
  synthesis potential, and the amendment's
  compositionality. This axis is not recombination:
  recombination counts carried parts in a new term;
  compositionality tests behavior under composition.

### 3.5 Amendment axes

Named by the amendment of 2026-11-20 02:43 PST, and by
the standing layer of the program record that carries
it (compactness, incrementality, reversibility,
checkability, derivability). Derivability is
dispositioned as an alias of power (section 3.2). The
prefixed forms in the amendment (high visibility, and
its kin) are directions on these axes, not separate
axes.

- visibility. What: the share of an approach's decisions
  and intermediate states, in one run, that are
  inspectable as appended records of the one graph —
  each decision carrying its premises and its outcome —
  over the run's total decisions. Unit: a pair of counts,
  printed as a share. Direction: higher is more visible.
  Contract: one executed run, its decisions enumerated
  by the run's own record, each decision checked for an
  appended graph record that a reader can re-derive the
  decision from. Grain: per run. Evidence: the run record
  and the graph appends at a named pin. A decision
  reported only in prose outside the graph counts as not
  visible.
- compactness. What: the size of the approach's own
  artifact in its canonical encoding — a tensor, a term,
  a scheme, a plan — counted in the encoding's own unit
  (bytes of the canonical form, or symbols at symbolic
  grain), the unit printed with the reading. Unit: count
  in the stated unit. Direction: smaller is better; a
  reading enters any score in its stated orientation.
  Contract: the same encoding and counting rule for
  every rival artifact of the same family. Grain: per
  artifact, at a named pin. Evidence: the counted
  artifact itself, reproducible from the pin.
- incrementality. What: the counted work of an update
  under the approach, against the counted work of the
  from scratch form of the same computation, with
  exactness as a precondition: an incremental reading
  exists only where the incremental result is proved or
  measured equal to the full result over the same
  checkpoints. Unit: a pair of counted work figures
  (relaxations, rule checks, or the contract's stated
  work unit), both printed. Direction: less incremental
  work at equal result is better. Contract: the same
  instance set and the same work counter for the
  incremental and the from scratch forms; equality
  checked at every stated checkpoint. Grain: per update
  battery run. Evidence: the executed battery at a named
  pin, with its equality checks printed. Counted work is
  not time; time enters speed, and only from timed runs.
- reversibility. What: whether an action's constructed
  inverse, executed after the action, returns the
  observed state to the pre action state. Unit: per
  action kind, a verdict under the protocol, over the
  run's trials, both printed. Direction: more action
  kinds passing, and a refusal by name where no inverse
  is derivable counting as a correct verdict, never as a
  pass. Contract: the validation protocol of the
  reversible home — fresh observation, execute, fresh
  observation, execute the constructed inverse, fresh
  observation; equality of the first and third
  observations is the verdict, and any difference names
  the differing component. A state model run and a live
  surface run are different contracts, and a reading
  names which it is. Grain: per action kind, per run.
  Evidence: the executed protocol run at a named pin,
  with its negative controls printed.
- checkability. What: the share of an approach's output
  claims, in one run, that an independent checker
  re-derives from the graph records alone — no trust in
  the approach's own reporting — over the run's total
  claims. Unit: a pair of counts, printed as a share.
  Direction: higher is more checkable. Contract: a named
  checker, run over the run's appended records at a
  named pin, its verdicts compared claim by claim; the
  checker shares no component with the approach it
  checks. Grain: per run. Evidence: the checker's
  executed run and its output at the pin.
- probes. What: the count of environment probes an
  approach spends to make one selection or complete one
  task. Unit: count, per selection or per task as the
  reading states, means over a named instance set
  printed with their set size. Direction: fewer probes
  is better; a reading enters any score in its stated
  orientation. Contract: the same instance set and the
  same definition of one probe for every rival. Grain:
  per instance set run. Evidence: the executed harness
  counts at a named pin. Probes are counted work against
  an environment; they are not time and not relaxations.

### 3.6 Weight space axes (meta search, over weighting configurations)

These axes read weighting configurations as candidates.
They bind only comparisons among configurations, and a
verdict among configurations may not be restated as a
verdict among approaches of another family.

- misses. What: the count of frontier members, over a
  named instance set, that the configuration does not
  select on any instance — middle members first among
  them, as the meta record counts them. Unit: count.
  Direction: fewer misses is better. Contract: the
  enumerated configuration space and instance set of the
  meta harness, the frontier of each instance computed
  weight free. Grain: per configuration, per instance
  set. Evidence: the executed harness at a named pin.
- ties. What: the count of instances on which the
  configuration's selection is a tie rather than a unique
  selection, summed over the instance set (the tie excess
  of the meta record). Unit: count. Direction: fewer ties
  is better. Contract: as misses; a selection counts only
  on a unique minimiser, ties recorded as ties. Grain:
  per configuration, per instance set. Evidence: the
  executed harness at a named pin.
- parsimony. What: the sum of the configuration's
  parameter magnitudes. Unit: count. Direction: smaller
  is better. Contract: the configuration's stated
  parameter list, summed as stated. Grain: per
  configuration. Evidence: the parameter list itself, as
  entered in the harness at a named pin. Aliases: the
  meta record's parameter sum.
- rank. What: the configuration family's declared rank
  in the meta record's family order. Unit: a position in
  a declared order. Direction: as declared. Contract:
  none — this is a declared preference, not a
  measurement. Grain: per family. Evidence: the
  declaration in the record, and nothing else. A rank
  reading is proposed by construction, may never be the
  sole strict axis of a measured verdict, and any
  weighting that uses it prints that fact. It stands in
  the register because the meta level's measure vector
  carries it; its weakness is printed here, not hidden.

## 4. Dedupe summary

Same measure, two names, one axis — each pair stated in
its axis entry and collected here so no later append
re-splits them:

- faster (candidate score) and speed (certification
  dimension) are the axis speed.
- better and its source name, and much improved
  (guidance, with a threshold), are the axis quality.
- net newness, its source measure name, and not
  pre-existing (guidance, as a boolean) are the axis
  novelty.
- derivability (amendment) is the axis power, whose
  source definition is already the derivability closure
  count.
- parameter sum (meta record) is the axis parsimony.
- novelty of composition is the axis recombination, and
  compositional synthesis potential is the axis
  compositionality; the two guidance names that sound
  alike name different measures and stand apart.

Kept apart, with the reason printed in each entry:
reversibility and reconversibility; ease and
compactness; leanness and the excess of `spec.md`
section 10; speed and counted work (incrementality,
probes).

## 5. Named gaps — named, not axes

A named gap enters no frontier, no weighting, and no
verdict. Each stands here with its owner and its closing
route, in the discipline of the program record.

- workspacing. Named by the amendment (high workspacing)
  with no definition in any record on disk: no record
  states what is measured (a workspace's size, its cost,
  or its availability to later steps), on what contract,
  or in which direction more is better — and the
  plausible readings point in opposite directions, so a
  definition chosen here would decide winners by
  construction, which the no gaming rule forbids.
  State: named gap. Owner: the amendment layer's next
  lane, with the idol-eyes line, whose faces are the
  likely contract home. Closing route: a record that
  states the quantity, its unit, its direction, and one
  executed reading on two rival approaches under one
  contract; on that record this gap is retired by append
  and the axis enters section 3 by append.
- payoff. The reversible record's driving tests are
  payoff weighted, and its order phrase for that guidance
  is recorded there with its reading stated once; no
  record states a payoff unit, a payoff contract, or a
  payoff evidence kind that two rival approaches could be
  read under. State: named gap. Owner: the reversible
  home's successor lane. Closing route: as workspacing.
- The pipeline specification's own speed axes and power
  axes stand as named gaps of that specification (its
  item in the program record), under its owner's interim
  rules. The axes speed and power of this register are
  defined on the candidate and certification contracts;
  they do not close the pipeline specification's gaps,
  whose contracts are that specification's to state.

## 6. The standing structure

### 6.1 Entries

The register under `space/` holds three append only
lists, in the form of `registry/`:

- `entries.json`: one entry per approach. An entry
  carries its name (a single word, minted under the
  naming discipline of this home), its family (the
  contract family its readings belong to), its contract
  stated in one line, and its readings: exactly one
  reading per axis of section 3, each a value with a
  state, or an explicit unmeasured mark. A reading's
  state is one of measured (an executed same contract
  measurement at a named pin, its record named),
  proposed (a modeled or argued reading, at exactly that
  strength), or unmeasured (no reading; the mark prints
  the gap or the closing route where the record names
  one). Entries are appended, never edited; a new
  reading for an entered approach appends a new entry
  version by position in the file's list, with its
  provenance, and the latest version is a reading of the
  list, not a stored field.
- `epochs.json`: one entry per weighting epoch, in the
  form of `registry/epochs.json`: the scheme over a
  named axis subset, and, for any epoch adopted over its
  predecessor, the metric, the instance set, the searched
  space, and both schemes, as `spec.md` section 11.3
  requires. Epoch zero is the founding epoch: no
  weighting at all — the frontier, computed weight free,
  is the whole selection. A weighting is never an upper
  bound and excludes nothing from the space.
- Verdicts ride in `entries.json` as their own list:
  one entry per dominance verdict (section 7), appended,
  never edited.

### 6.2 Search, solve, optimize — continuously

The space is searched, solved, and optimized by the
same operations, applied at every append:

1. Search: the entered approaches of one family, read
   over the axes their contract supports, with unmeasured
   marks printed — never filled, never scored as zero.
2. Solve: the frontier of a family is computed weight
   free over the axes that carry a measured reading for
   every member being compared on that axis set. An axis
   with an unmeasured mark on any compared member is
   excluded from that comparison and the exclusion is
   printed with the result. This is frontier before
   weights, applied recursively: weighting configurations
   are themselves entries (the weight family), their
   frontier is computed weight free over the weight space
   axes, and a weighting over configurations selects only
   from that frontier, as the meta level of the
   reversible home specifies and executes.
3. Optimize: a weighting epoch may select within a
   frontier, on a stated metric over a named instance
   set, adopted only as an epoch entry records it. A
   selection is a reading, not a verdict: it claims that
   this weighting, on this metric, on this set, picks
   this member, and nothing more.
4. Append: every new approach, axis, reading, weighting,
   and verdict appends. Nothing is recomputed blindly:
   a frontier or a score is recomputed only over the
   entries its append touches, and carried readings stand
   until a new reading at a newer pin supersedes them by
   append.

### 6.3 The validator

`space/build.py` is foreign scaffolding beside the data,
as `registry/build.py` is: it validates the register
against this document — every entry carries exactly one
reading per registered axis; every measured reading
names its record and its pin; no verdict stands as
measured without a contract, a record, and a pin; every
epoch names its axis subset from the register; named
gaps appear in no reading, epoch, or verdict. It prints
the counts of section 8 and fails on any violation. It
computes no reading and invents no value.

## 7. Dominance verdicts — the selection law

- One approach dominates another, in this space, exactly
  when, under one stated contract in one family, it is
  no worse on every axis of a stated axis set and
  strictly better on at least one, where every reading
  used is measured, executed under that same contract,
  at a named pin. The axis set, the contract, the
  record, and the pin are printed in the verdict entry.
- A dominance statement whose readings are modeled,
  argued, or taken from different contracts is a
  proposed verdict, entered as proposed, and steers
  nothing until its measurement lands.
- A tie on the frontier is a frontier membership for
  both members, printed as a tie verdict where the
  records support one; neither member is silently
  dropped, and a later axis or reading may separate
  them by append.
- A measured loss is a verdict too: the losing approach
  stays entered, its loss printed, as the records print
  theirs. A candidate that fails an empirical pass
  returns as a named loss and the selection re-runs over
  the appended space.
- Implementation gate, from the amendment: a clear
  candidate — dominant on the measured frontier,
  empirically sound — is implemented and proved after
  the empirical testing proves the result sound, never
  before. This document implements nothing and proves
  nothing; it founds the space those gates read.

## 8. The seeded census

Seeded at founding from the records named in section 3,
at the pins those records name. No reading is invented:
every measured reading below is in its source record,
and every other axis of every entry carries an explicit
unmeasured mark in the register. The register's counts
at founding, as the validator prints them:

- Entries: 18 approaches — 13 in five contract families
  (selection, stop, repair, closure, action) and 5
  weighting configurations in the weight family.
- Verdicts: 9 verdict entries — 7 measured dominance
  verdicts, 1 measured tie verdict, and 1 proposed
  dominance verdict (the meta level's own dominance
  reading over its declared axes, entered at proposed
  strength because its per axis readings are not yet
  entered in this register) — each with its contract,
  record, and pin printed in its entry.
- Epochs: 2 — epoch zero, the founding frontier only
  epoch; epoch one, the demonstration meta weighting of
  the meta record, over the weight space axes, adopted
  in that record at its pin and entered here as this
  register's first weighting epoch, binding only the
  weight family.

The families and their seeded members, with the reading
each record actually supports (the register carries the
full vectors):

- selection (contract: the frontier selection battery
  of the validation lanes in the reversible home —
  candidate sets read frontier first against an
  exhaustive oracle, held out permutations throughout):
  the frontier first approach (entered as `frontier`),
  measured exact; its rival
  the weight first ranking (entered as `scalar`), entered as a measured loss
  (it recovers only part of the frontier, and a named
  class of frontier members is unreachable by any
  positive weighting — the proved segment counterexample
  stands behind the measured figure).
- stop (contract: the stop rule battery over streams,
  optimality claims checked against remaining
  alternatives): the two face stop (entered as `dual`), measured with no
  false optimality claim; its rival the fixed budget
  stop, entered as a measured loss (nearly half of its
  optimality claims false).
- repair (contract: append and weight decrease epochs,
  exactness against the oracle, counted relaxations):
  the cone scoped repair, measured exact at the least
  counted work; its rivals the from scratch form and the
  scan per round form, both exact and both dominated on
  counted work, printed as such.
- closure (contract: append prefix comparisons against
  the least full closure, counted rule checks): the
  distinct count worklist, measured with no mismatch;
  its rival the duplicate blind worklist, entered as a
  measured loss (its mismatches named, their differing
  component named in the record).
- action (contract: the action model battery of the
  reversible home — seven scenario families, paired
  seeded instances, the same instance seed for every
  rival; simulated scenarios only, no live surface, and
  every reading of this family carries that scope): the
  combination route and the obscurity route, tied on
  task success at the frontier; the combination route
  down selected on the probes axis; the explicit route,
  dominated on task success, retained as the combination
  route's planning leg in its home record; the naive
  greedy control, refuted as a selection approach and
  retained as the standing control.
- weight (contract: the meta harness of the reversible
  home — enumerated configurations over three instances,
  each instance's frontier computed weight free): five
  family representatives at their stated parameters,
  with the reaching and missing readings the harness
  executed, and the meta level's own dominance reading
  over the declared axes entered as a verdict at its
  strength.

What the seeded census does not carry, printed plainly:
every speed reading in the space is unmeasured (no timed
run under any of these contracts stands in the records);
every live surface reading is unmeasured (the action
family is simulated, the reversibility protocol's live
pass is owed, and the certification dimensions'
solvability and speed stand unmeasured in their own first
certificate); the 28 frontier members no enumerated
configuration selects stand unmeasured in the weight
family's home, owned by its successor lane; and no
approach outside the meta search program's records is
entered yet — the space is founded on the records that
support readings, and grows by append as further records
land.

## 9. Rules for later appends

1. A new approach appends an entry with a full reading
   vector; axes its contract does not support carry
   unmeasured marks naming why.
2. A new axis appends to section 3 of this document
   only with the four parts of section 2, and appends a
   reading (or an unmeasured mark) to every entered
   approach in the same landing, so the vector stays
   complete.
3. A new weighting appends an epoch; a new verdict
   appends a verdict entry. Nothing already entered is
   edited, renumbered, or removed.
4. Every append re-runs the validator, and any landing
   that touches Lean re-runs the family gate; a landing
   that touches neither prints the validator's verdict
   and the standing gate state at the base pin, claiming
   no new gate result.
5. The naming discipline of this home binds every name
   minted here: single words, no underscore, no camel
   form, no mashed compound. Foreign names quoted from
   other records keep their own spelling and are
   evidence, not models.
