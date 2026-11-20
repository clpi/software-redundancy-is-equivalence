# The registry

This directory is the registry of section 11 of the
specification, built on the canonical model over one
witnessed set. Four states are kept distinct: the
specification is settled intent, the Lean development
in the proof folder is implemented behavior, what the
family gate checks at the landed pin is verified
behavior, and this registry is measured behavior at
the pins named below, at exactly that strength.

## The witnessed set

The extract layer of the library hypergraph branch at
its head step: 321 symbol records at the extract pin
69ee40eb000f557e07dae548efa9a503703ecb35, in fourteen
home files and one combined file whose records are
exactly the records of the fourteen files. The
trajectory record of the program holds the head step
at pin 4b2d5f81 of that branch. Each record carries
its identity, its home, its name, and, for 244 of the
321, a signature term; 77 records carry no signature
term.

## Construction, at symbolic grain

- A record becomes one term. Where the record carries
  a signature term, the term is a form whose head is
  the atom of the record identity and whose arguments
  are the atoms of the signature argument words, in
  order. Where it carries none, the term is the atom
  of the record identity. The head atom keeps distinct
  records distinct: nothing is silently identified.
- Every term is in the trivial scope of section 3: an
  atom, or a form with an atom head and atom arguments.
- Equivalence is asserted only where a record
  witnesses it, under the witness honesty premise of
  the theory. No record in this set witnesses an
  equivalence between distinct terms: the class field
  of the records takes 321 distinct values on 321
  records, so it joins nothing, and a shared signature
  spelling across homes is spelling, which section 6
  bars as a ground for equivalence. Every term
  therefore stands in a singleton edge, every edge
  holds no colors, and the excess of every
  configuration below is zero. This is a finding about
  the witnessed set, stated as a finding in the
  validation record, not a claim about the subject.
- A level is recorded per home, and one combined level
  for the whole set. A configuration is the view of
  the graph at a level: the singleton edges of that
  level's terms. All fifteen configurations are at
  symbolic grain; no configuration is entered at a
  coarser grain.

## Format

- The entries file holds one entry per unique
  witnessed configuration: the configuration (its
  edges, each with its terms and its colors), its five
  measures, its provenance (pin, level, and epoch of
  each witnessing, in append order), and its colors as
  epoch and score pairs, in append order.
- The epochs file holds the appended schemes in order.
  Epoch zero is the founding scheme. The specification
  fixes the five measures and no numeric founding
  weights; the choice taken here is unit weights, one
  for each measure, named in the epoch entry itself.
- Identity of a configuration is content equivalence
  as in section 11: same edges up to membership, edge
  by edge the same terms and the same colors up to
  membership. No digest is an identity anywhere here.
- The builder is foreign scaffolding in Python, beside
  the data, so the build can be repeated. It reads the
  combined extract file, the merged pin of this
  repository at build time, and an output folder.

## The solved epoch

The coloring exists to make redundancy inspectable:
configurations distinguished by their content, and,
where the coloring is one to one on the registered
set, the full measure reading of a configuration
recoverable from its color by the registry table.

The objective, stated exactly: over the fifteen
registered configurations, first the count of distinct
colors, then the least gap between distinct colors,
then the least weight sum, then the lexicographically
least scheme in the fixed measure order (term count,
edge count, excess, colored edge count, distinct
symbol count).

- Epoch zero, unit weights: 15 distinct colors, least
  gap 1. The sum of the fifteen colors is 1998.
- Epoch one, solved: weights 9, 9, 0, 0, 6 in the
  measure order above. 15 distinct colors, least gap
  12. The sum of the fifteen colors is 15840.
- The search was exhaustive over every scheme with
  each weight from zero to nine inclusive: 100000
  schemes, enumerated in lexicographic order by the
  builder. The optimality claim is at exactly this
  level: the best scheme over that searched set, found
  by exhaustive enumeration of the set. No bound over
  schemes outside the set is claimed or proved.
- The excess and colored measures are constant zero on
  this witnessed set, so no weight on them changes any
  color on this set; the least sum rule of the
  objective sets both weights to zero. Their weights
  are unidentifiable from this instance set, and a
  later epoch over a set with witnessed equivalence or
  painted colors is the route that identifies them.
  That gap is owned in the validation record.
- The epoch one entry in the epochs file names the
  metric, the set, the searched space, and both
  schemes, as section 11 requires for an adoption. A
  weighting excludes nothing: no configuration,
  term, or bound is pruned by either epoch.

## Counts

- Entries: 15. Unique configurations: 15, all at
  symbolic grain, none at a coarser grain.
- Epochs: 2 (epoch zero founding, epoch one solved).
- Distinct terms in the one graph: 321. Term
  occurrences across all entries: 642 (each home
  configuration once, and the combined configuration
  once). Distinct symbols in the combined
  configuration: 329 (the 321 record identities and
  the 8 signature argument words).
- Excess: zero in every configuration. Colored edges:
  zero in every configuration.

## What is not entered, by rule

- The earlier trajectory's file level and edge level
  duplication figures are duplication measurements
  about the old construction. They are not canonical
  configurations, and no figure of theirs is entered
  in this registry or cited as a canonical
  measurement.
- Premise cones, traces, effect readings, and filter
  marks of the records are derived view data in the
  sense of section 12, not configurations, and are not
  entered. The filter marks are not painted as colors:
  painting a qualification mark under the discipline
  of section 9 is a decision no record in this set
  makes, so the colored measure stands at zero by
  construction, and the painting question is owned by
  the coloring and qualification lane in the
  validation record.

## The positive witness, appended

A later append, recorded here without editing any
figure above: one witnessed join has been entered,
on the measurement recorded in the witness record
beside this readme (the file named witness in this
folder). The joined pair is the cbor record and the
msgpack record of one definition whose two texts are
byte for byte equal at the extract pin.

- Entries: 18. Unique configurations: 18, all at
  symbolic grain. The fifteen standing entries stand
  as recorded above; each gained only an epoch two
  provenance entry and color pair, by append.
- New entries, the views of the grown graph: level
  cbor grown (33 terms, 32 edges, excess 1, 37
  distinct symbols), level msgpack grown (45 terms,
  44 edges, excess 1, 50 distinct symbols), and level
  all grown (321 terms, 320 edges, excess 1, 329
  distinct symbols). Excess is one in each grown
  configuration and zero in every standing one.
- Epochs: 3. Epoch two, solved over the eighteen
  configurations on the standing objective and
  searched set: weights 5, 9, 0, 0, 5 in the fixed
  measure order; 18 distinct colors, least gap 9.
- The positive cases of monotonicity and of
  appearance now have canonical instances in this
  registry, as the witness record states. The
  colored weight stays unidentifiable (the colored
  measure is zero on all eighteen configurations);
  the excess weight is forced to zero inside the
  searched set and is not separately identifiable in
  the unbounded scheme space, for the definitional
  reason the witness record and the epoch two entry
  state.
