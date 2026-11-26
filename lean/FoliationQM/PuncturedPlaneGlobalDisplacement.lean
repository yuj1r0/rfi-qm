module
public import FoliationQM.GlobalSpinOriginalCover
public import FoliationQM.PuncturedPlaneGlobalSign
public import FoliationQM.PuncturedPlaneRelativeSpin

/-!
# The global sign separating the two punctured-plane lifts

For the Spin-frame component of v13 `prop:takabayasi`, the displacement of
the two explicit geometric Spin structures is the class of the cocycle
whose negative edge joins the first and third half-plane charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneGlobalDisplacement
open PuncturedPlaneSignCover PuncturedPlaneGeometricSpin SpinSignHOne
open SpinLiftSignDifference SpinLiftIsomorphism SpinLiftChartGauge SpinLiftOverlapTorsor
open GlobalSpinDisplacement SmoothSpinRelativeClass

/-- The actual geometric transitions of the reference and twisted lift differ by the specified three-chart sign class. -/
theorem geometric_difference (n : WithTop ℕ∞) :
    classOf (difference (transitions (smoothAtlas n) (reference n))
      (transitions (smoothAtlas n) (twisted n))) = classOf (PuncturedPlaneSpinSign.cocycle n) := by
  let S := PuncturedPlaneSpinLifts.reference n
  let z := PuncturedPlaneSpinSign.cocycle n
  have h := SpinLiftHOneTorsor.differenceClass_congr
    (gaugeEq_of_agree (transitions_realize (smoothAtlas n) (toExtracted S)))
    (gaugeEq_of_agree (transitions_realize (smoothAtlas n) (toExtracted (twist S z))))
  exact h.trans (classOf_eq_of_overlap (difference_twist (toExtracted S) z))

/-- The two independently charted physical lifts have the explicit global negative-edge sign as their displacement. -/
theorem displacement_eq_sign (n : WithTop ℕ∞) :
    displacement (smoothAtlas n) (physicalClass (PuncturedPlaneRelativeSpin.reference n))
      (physicalClass (PuncturedPlaneRelativeSpin.twisted n)) = PuncturedPlaneGlobalSign.sign n := by
  exact (GlobalSpinOriginalCover.displacement_forget (smoothAtlas n) (reference n) (twisted n)).trans
    (congrArg (SpinAllCoverHOne.ofCover domains covers) (geometric_difference n))

end FoliationQM.PuncturedPlaneGlobalDisplacement
