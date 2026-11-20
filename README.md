# Software redundancy is equivalence

## Foundation

This repository is the home of the redundant compute
program, re-founded on the canonical model. There is one
hypergraph: the total equivalence graph of equivalent
terms, whose edges are sets of equivalent symbolic
expressions at the minimum resolution, the symbol being
the finest grain. It is bound, at any resolution time,
only by the finite resolved upper bound taken through
the one lattice of states. Resolution levels are
appended to this same graph and reconciled on it, never
kept as separate graphs. Resolved information is
appended only, so drift is excluded by construction.
Redundancy, on this model, is a property of equivalence
classes: a term is redundant when its edge holds at
least one other term distinct from it by spelling, and
the excess of a graph is its count of collected terms
minus its count of edges. Colorings, qualifications,
and every proof of the program are constructed from
this one graph and from nothing else. The full model
is the specification in `spec.md`, carried verbatim as
this repository's foundation document; its status line
stands as written there.

## State of this repository

Four states are kept distinct throughout: settled
intent, proposed semantics, implemented behavior,
verified behavior. The specification is settled intent
as dictated, and the claims it lists are proposed
semantics at exactly that strength. The proof tree
currently holds a bare skeleton only: no definition of
the model is implemented yet, and no theorem of the
program exists yet. Nothing in this repository may be
read as claiming otherwise.

## The predecessor, dispositioned

This program had a predecessor repository,
`clpi/software-redundant-compute-expands`, landed at
pin `1ea286488cd4fecb7edb7f5debe407db04456b88`. By the
ruling of 2026-11-19, that repository is founded on a
hallucinated construction: a graph as a node list plus
a premise and conclusion hyperedge list, with
redundancy as a count of non-first occurrences over a
flattened incidence list. Its theorems are about that
list counting artifact, not about the canonical
hypergraph, and none of them is a foundation here.
Its 63 program claims stand dispositioned: 48 as
statements about the list construction only, 12 as
duplication measurements only, and 3 withdrawn. The
full disposition is held in the program record at
`~/workspace/redundant-compute-scratch/disposition.md`.
The predecessor stands untouched, cited here as a
predecessor only, never as a foundation, and nothing
of its construction is imported into this tree.

## Contents

- `spec.md` — the canonical specification: the
  foundation document of the program, carried verbatim.
- `defs.md` — where the model's definitions stand.
- `proof/` — the Lean development, at present a bare
  skeleton, with the family gate.
- `space.md` — the approach space: approaches by
  semantic axes, its axis register, its dominance law,
  and its seeded census, founded by the amendment of
  2026-11-20.
- `space/` — the register of that space: entries,
  weighting epochs, verdicts, and its validator, in the
  form of `registry/`.

## The gate

The gate is the script `check.sh` in `proof/`. Run it
with the pinned toolchain on the path:

```
cd proof
PATH=<toolchain bin>:$PATH ./check.sh
```

It compiles every Lean file under `proof/` with
warnings as errors, rejects every proof escape token,
and enforces that every printed axiom lies in the
allowed set {propext, Classical.choice, Quot.sound}.
The gate log is `CHECK.log` in `proof/`. Toolchain:
Lean 4.19.0, pinned in `proof/lean-toolchain`.
