# The approach space register

This directory is the register of the approach space
specified in `space.md`, built by the discipline of the
registry in `registry/` and of section 11 of `spec.md`.
Four states are kept distinct: `space.md` is settled
intent, a proposed reading or verdict here is proposed
semantics at exactly that strength, the files here are
the register's implemented form, and what the validator
checks at the landed pin is verified behavior of the
register's form only — no reading's truth is verified by
the validator; each reading stands at the strength of
the record and pin it cites.

## Form

- `entries.json` holds the axis list, one entry per
  approach (its family, its contract, and exactly one
  reading per axis — a measured value with its record
  and pin, a proposed reading, or an explicit unmeasured
  mark), and the verdict list. Entries and verdicts are
  appended, never edited, never removed.
- `epochs.json` holds the weighting epochs in append
  order. Epoch zero is the founding epoch: no weighting,
  the frontier alone. An adopted epoch names its metric,
  its instance set, its searched space, and both
  schemes, as section 11.3 of `spec.md` requires. A
  weighting excludes nothing from the space.
- `build.py` is the validator: foreign scaffolding in
  Python, beside the data, so the check can be repeated.
  It validates form and discipline only — completeness
  of every reading vector, provenance on every measured
  reading, contract and pin on every measured verdict,
  epoch form — and prints the counts. Run it with
  `python3 build.py` in this directory.

## Counts at founding

As the validator prints them at the founding landing:
28 axes, 18 entries, 504 readings, 30 measured readings,
474 explicit unmeasured marks, 9 verdicts (8 measured,
1 proposed), 2 epochs. The full census, the families,
and what stands unmeasured across the whole space are
stated in `space.md` section 8.

## What is not entered, by rule

- The named gaps of `space.md` section 5 (workspacing,
  payoff) appear in no reading, epoch, or verdict; the
  validator fails if one does.
- No reading is entered from a suspended ranking: the
  candidate space round two ranking, suspended as
  steering input in its home record, contributes no
  reading and no verdict here.
- No speed reading is entered anywhere at founding: no
  timed run under any of these contracts stands in the
  cited records, so the speed axis carries unmeasured
  marks throughout, printed, not filled.
