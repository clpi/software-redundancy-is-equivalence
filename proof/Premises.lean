import Core

/-! # Premise labels

    The two premise labels the rebuild inherits from
    section 13, stated as explicit premises. They bind
    where the model is applied, not what its theorems
    say: no theorem of the development depends on
    either, and neither is smuggled in — each is a
    proposition a subject supplies when applying the
    model, with its falsification route stated. -/

variable {Sym : Type}

/-- Witness honesty: an equivalence entry's witness
    is what it names — a proof checked by the gate, a
    measurement at its pin. Stated as a premise: for
    a subject-supplied verification predicate, every
    join entry of the graph's log carries a witness
    the predicate verifies. The development proves
    everything from the entries and cannot prove an
    entry honest. Falsification route: exhibit a graph
    whose log holds a join entry whose witness the
    subject's own verification predicate rejects —
    the premise then fails for that graph and
    predicate, and every application resting on it is
    void. -/
def honest [DecidableEq Sym] (kinds : Kinds Sym)
    (verified : Sym → Prop) (graph : Graph Sym) :
    Prop :=
  ∀ e ∈ graph.log, e.kind = kinds.join →
    verified e.witness

/-- Reading fidelity: a subject's symbol type and
    term readings are the subject's own — the model
    proves facts about the terms as read, not about
    the behavior they were read from. Stated as a
    premise: for a subject-supplied reading of
    external items as terms, every external fact the
    subject names has its reading among the term
    facts the subject names. Falsification route:
    exhibit an external item whose named fact does
    not hold of its reading under the subject's own
    term facts — the premise then fails for that
    reading, and conclusions about the behavior, as
    opposed to about the terms as read, do not
    follow. -/
def faithful {X : Type} (read : X → Term Sym)
    (fact : X → Prop) (reading : Term Sym → Prop) :
    Prop :=
  ∀ x, fact x → reading (read x)
