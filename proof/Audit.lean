import Core
import Ops
import Claims
import Registry
import Views
import Controls
import Premises
import Resolve
import Schedule
import Wiring

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
#print axioms runsteps
#print axioms claimone
#print axioms claimtwo
#print axioms claimthree
#print axioms claimfour
#print axioms claimfive
#print axioms claimsix
#print axioms claimsixintake
#print axioms claimseven
#print axioms claimeight
#print axioms claimnine
#print axioms claimtenalgebra
#print axioms claimten
#print axioms claimeleven
#print axioms claimtwelvestep
#print axioms claimtwelve
#print axioms claimthirteen
#print axioms claimfifteen
#print axioms Sched.qminle
#print axioms Sched.resetnodes
#print axioms Sched.resetlen
#print axioms Sched.putlen
#print axioms Sched.getput
#print axioms Sched.recordfresh
#print axioms Sched.recordkeeps
#print axioms Sched.flushlen
#print axioms Sched.depositcap
#print axioms Sched.scentable
#print axioms Sched.scenarena
#print axioms Sched.scoreparts
#print axioms Sched.bettergain
#print axioms Sched.foldpick
#print axioms Sched.pickmem
#print axioms Sched.pickmax
#print axioms Sched.beambridge
#print axioms Sched.beamrank
#print axioms Sched.stepnone
#print axioms Sched.stepfuel
#print axioms Sched.stepbound
#print axioms Sched.stepmerge
#print axioms Sched.sweepgates
#print axioms Wire.wiredmem
#print axioms Wire.wiredgates
#print axioms Wire.wiredbridge
#print axioms Wire.wiredvisits
#print axioms Wire.reportmerge
#print axioms Wire.reportbackoff
#print axioms Wire.wsweepseq
#print axioms Wire.wsweepsone
#print axioms Wire.wsweepsmore
#print axioms Wire.wsweepsstopv
#print axioms Wire.wsweepsmorev
#print axioms Wire.wsweepsfold
#print axioms Wire.wsweepsgates
#print axioms Wire.wrunsteps
#print axioms Wire.wclaimone
