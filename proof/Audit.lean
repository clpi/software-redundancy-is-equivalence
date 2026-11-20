import Core
import Ops
import Claims
import Registry
import Views
import Controls
import Premises

/-! # Axiom audit

    The audit of the development: every main theorem's
    dependencies on the standard axioms, printed
    for the family gate.
    The allowed set is the three standard axioms —
    propext, Classical.choice, Quot.sound — and the
    gate checks that nothing beyond them appears. -/

#print axioms witness
#print axioms boundleast
#print axioms boundsat
#print axioms boundfin
#print axioms sametrans
#print axioms runexcess
#print axioms enterexcess
#print axioms joinexcess
#print axioms recordentry
#print axioms mono
#print axioms monoexcess
#print axioms excessrun
#print axioms compound
#print axioms compoundge2
#print axioms appear
#print axioms appearcontrol
#print axioms effone
#print axioms derivedintended
#print axioms intendedneeds
#print axioms boundgrows
#print axioms boundrecorded
#print axioms reconpart
#print axioms reconcolors
#print axioms widen
#print axioms scoreeq
#print axioms measureeq
#print axioms registryexact
#print axioms notecolor
#print axioms colorsstand
#print axioms schemeatnewepoch
#print axioms derivstore
#print axioms derivsteps
#print axioms derivelim
#print axioms Control.zero
#print axioms Control.split
#print axioms Control.free
#print axioms Control.order
#print axioms Control.filter
