# The positive witness

This record is the provenance of the first witnessed
join in this registry: one equivalence between two
distinct terms, grounded in a measurement at a named
pin, and the three grown configurations and the third
epoch that the join produces. Four states are kept
distinct: the specification is settled intent, this
record and the registry files are measured behavior
at the pins named, at exactly that strength.

## The pair

Two records of the witnessed set, in two homes:

- The record with identity "def:cbor:uval", home
  cbor, file "cbor.id", at the extract pin
  69ee40eb000f557e07dae548efa9a503703ecb35.
- The record with identity "def:msgpack:uval", home
  msgpack, file "msgpack.id", at the same pin.

Their registry terms are distinct: each term is the
form whose head is its own record identity and whose
arguments are the two signature words of its record.
They stand in singleton edges in the fifteen standing
configurations.

## The witness

The ground is a measurement at the pin above: a
direct comparison of the two definition texts in the
library sources the extractor read at that pin. The
two texts are byte for byte equal, head line and
body together. The cbor text stands at lines 38 to
41 of its file; the msgpack text at lines 96 to 99
of its file. Both texts, quoted as evidence:

```
uval = (mag)
    t = node("uint")
    t.mag = mag
    t
```

The comparison is of the full definition texts, and
nothing else is the ground: not the shared signature
spelling of the two records, which section 6 of the
specification bars as a ground; not the shared name;
not any digest, which section 6 also bars — no digest
was computed as a ground anywhere in this witnessing,
and the validator re-runs the direct text comparison
itself. Two further copies of the same library
sources on the same machine, in two other scratch
trees of the program, carry both texts byte for byte
equal as well; the validator reads the extractor
copy, and the agreement of the copies is recorded
here as a check, not as the ground.

One supporting reading, recorded at the same
strength: the sole premise of each definition is the
same called definition in its own home, and those
two texts are likewise byte for byte equal at the
pin (lines 33 to 36 in the cbor file, lines 83 to
86 in the msgpack file), so the equality of the pair
is not undercut by a differing premise. The extract
records agree with this reading: each record's
premise cone is the singleton of its own home's
called definition, and the two records carry the
same effect reading. This paragraph is support; the
ground is the text comparison alone.

Under section 6, an equivalence entry is admitted
only on a witness: a proof, a derivation in a
derived view, or a measurement at a named pin,
recorded in the entry. This join is admitted on the
third kind: the measurement above, at the pin above,
recorded here and in the provenance of the grown
entries. The witness honesty premise of the theory
binds exactly here, as it binds every entry: the
measurement is what this record names, and it was
executed and re-executed by the independent
validator named below.

## The construction

One join is applied to the one graph: the two
singleton edges of the pair are replaced by one edge
holding both terms, under operation two of section
8.2 of the specification. No other edge changes, no
term is admitted or removed, and no color is
painted. Three configurations of the grown graph are
appended as new entries, each the view of the grown
graph at its level, each edge whole as section 7.3
requires — so the view at each home of the pair
holds the joined edge whole, including the term of
the other home:

- Level cbor, grown: 33 terms, 32 edges, excess 1,
  37 distinct symbols.
- Level msgpack, grown: 45 terms, 44 edges,
  excess 1, 50 distinct symbols.
- Level all, grown: 321 terms, 320 edges, excess 1,
  329 distinct symbols.

The fifteen standing entries are not edited: each
gains only an epoch two provenance entry and an
epoch two color pair, by append, as the epoch one
append did before. The registry now holds 18
entries, 18 unique configurations by content, and
3 epochs.

## The solved third epoch

Epoch two is appended and solved over the eighteen
configurations by the standing objective and the
standing searched set (every scheme with each weight
from zero to nine inclusive, 100000 schemes,
exhaustive). Solved scheme, in the fixed measure
order (term count, edge count, excess, colored edge
count, distinct symbol count): weights 5, 9, 0, 0, 5.
Objective: 18 distinct colors, least gap 9. The
coloring stays one to one on the registered set.

What this settles, cell by cell, against the three
unmeasured cells the registry carried:

- Positive monotonicity: now witnessed. Along the
  real chain from the standing combined
  configuration to the grown combined configuration
  — one effective join and no other change — excess
  moves from zero to one: it does not decrease, and
  the positive direction has a canonical instance in
  the registry at symbolic grain.
- Positive appearance: now witnessed as an
  instance. Each home append alone leaves excess at
  zero (the standing cbor and msgpack
  configurations), and the grown combined
  configuration, whose only cross change is the join
  of one term of the first home to a distinct term
  of the second, stands at excess one.
- Identifiability of the excess weight: settled at
  a finer reading than the registry carried. The
  excess measure now varies over the set (zero on
  the fifteen standing configurations, one on the
  three grown ones), and no scheme in the searched
  set with a positive excess weight reaches the
  solved gap, so the solved excess weight of zero is
  forced inside the searched set. In the unbounded
  scheme space the excess weight is not separately
  identifiable on any set at all: excess is by
  definition the term count minus the edge count, so
  the scheme with weights 4, 10, 1, 0, 5 in the
  measure order gives the same colors as the solved
  scheme on every configuration, which the validator
  checks on all eighteen. The weight is therefore
  identifiable only relative to the searched set,
  and the epoch two entry in the epochs file states
  this in its note.
- Identifiability of the colored weight: unchanged.
  The colored measure is constant zero on all
  eighteen configurations — this witnessing paints
  no color — so its weight is still unidentifiable
  from the data, the least sum rule still sets it to
  zero, and the cell stays unmeasured with its
  standing owner, the coloring and qualification
  lane.

## Sources checked and not used

- The candidate space estate extract of rounds one
  and two: its raw record files are not on this
  machine, as two earlier verification lanes also
  found; nothing from it could be grounded here.
  The 321 record extract that is on disk was read in
  full: its class field joins nothing, and its
  constructed traces are branching paths through
  premise cones, not derivations of one term by two
  routes, so they witness no equivalence.
- The factored joint plan data of the derivation to
  action line: a synthetic fixture in another repo,
  whose shared witness is one action covering all
  eight goals of the fixture. It joins no two
  distinct terms of this registry's subject and was
  not used as a ground.
- The jq extraction data: read; no jq pair was
  needed, the pair above being the smallest grounded
  one in the set (four lines of definition text, a
  singleton premise, likewise equal).

## Validation

This change touches registry data and prose only;
no Lean file changes. The independent validator of
the validation record's pattern was re-run in
extended form over the grown registry (it rebuilds
the standing fifteen from the fourteen per home
extract files, rebuilds the grown three by the one
join, re-runs the definition text comparison,
recomputes every measure and every recorded color
under all three epochs, checks uniqueness by
content at eighteen of eighteen, the witness form
on all eighteen configurations, both positive
instances above, and the epoch two solve by the
same exhaustive search): 15 of 15 checks pass. The
cold Lean gate of the repo was also run at the
landed pin, since the tree carries it, and passes;
no theorem state changes by this landing.
