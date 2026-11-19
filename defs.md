# Definitions

Every term of the model is defined at implementer
resolution in the specification, `spec.md`, sections 2
to 12: symbols and terms, the three scopes, the one
lattice of states, the one hypergraph and its validity
invariants, equivalence, levels, the finite resolved
upper bound, the view, append only growth, colors and
qualifications, redundancy and excess, the registry and
its epochs, and the derived views.

Those definitions are settled intent. None of them is
implemented in the Lean development yet: the proof tree
holds a bare skeleton with no model definition and no
theorem of the program. As the rebuild implements each
definition, this file will name its Lean counterpart,
one entry per definition, and the Lean development will
be the authority wherever prose and code could drift.
Until then, this file records only where the
definitions stand: in the specification, nowhere else.
