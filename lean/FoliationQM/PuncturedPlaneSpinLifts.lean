module
public import FoliationQM.PuncturedPlaneSpinSign
public import FoliationQM.SpinLiftHOneTorsor

/-!
# Inequivalent genuine lifts on the punctured plane

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
Twisting the identity Spin transitions by the sign around the three-chart
cycle gives a second lift of the same physical Lorentz transitions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneSpinLifts
open PuncturedPlaneSignCover SpinLiftSignDifference SpinLiftChartGauge

/-- The identity Spin cocycle projects to Lorentz data on the three half-planes. -/
def lorentzData (n : WithTop ℕ∞) : CliffordSpinLorentzTransitions.Data model Plane (Fin 3) n :=
  CliffordSpinLorentzTransitions.ofSpinData (CliffordSpinPolarCocycle.identityData domains covers)

/-- The unit Spin transitions are a reference lift of these data. -/
def reference (n : WithTop ℕ∞) : Lift (lorentzData n) :=
  ofSpinData (CliffordSpinPolarCocycle.identityData domains covers) rfl (fun _ _ _ _ _ => rfl)

/-- Twisting by the nonneutral cycle on the three actual half-planes yields a different gauge class of genuine Spin lifts. -/
theorem inequivalent (n : WithTop ℕ∞) :
    liftClass (twist (reference n) (PuncturedPlaneSpinSign.cocycle n)) ≠ liftClass (reference n) :=
  fun h => PuncturedPlaneSpinSign.class_ne_one n
    ((SpinLiftHOneTorsor.act_eq_self_iff _ (liftClass (reference n))).mp h)

end FoliationQM.PuncturedPlaneSpinLifts
