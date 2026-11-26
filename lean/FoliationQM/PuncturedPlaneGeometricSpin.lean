module
public import FoliationQM.PuncturedPlaneSpinLifts
public import FoliationQM.SpinGeometricLiftClasses

/-!
# Two geometric Spin lifts over one punctured-plane Lorentz bundle

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
Both smooth Spin structures map to the principal Lorentz bundle built from
the identity transitions on the three actual half-planes. Extracting that
bundle's chart transitions recovers the supplied Lorentz values on pair
overlaps. The nonneutral sign class distinguishes the geometric lifts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.PuncturedPlaneGeometricSpin
open PuncturedPlaneSignCover CliffordSpinLorentzSmooth LorentzMatrixGroup
open SpinLiftSignDifference SpinLiftChartGauge SpinLiftIsomorphism

/-- The principal Lorentz data are obtained from the identity Lorentz cocycle of the three-chart cover. -/
abbrev principalData (n : WithTop ℕ∞) :=
  CliffordSpinPrincipalBundle.lorentzData (PuncturedPlaneSpinLifts.lorentzData n)

/-- The two Spin structures have this common geometric Lorentz target. -/
abbrev atlas (n : WithTop ℕ∞) := PrincipalCocycleBundle.geometricData (principalData n)

/-- The core charts on the common target have their original smooth forward and inverse maps. -/
abbrev smoothAtlas (n : WithTop ℕ∞) := CliffordSpinPrincipalBundle.lorentzSmoothAtlas (principalData n)

/-- Any original three-chart lift supplies a lift of the transitions extracted from the geometric target. -/
def toExtracted {n : WithTop ℕ∞} (S : Lift (PuncturedPlaneSpinLifts.lorentzData n)) :
    Lift (AdaptedGeometricSpinLift.lorentzData (smoothAtlas n)) where
  transition := S.transition
  smooth_transition := S.smooth_transition
  identity := S.identity
  comp := S.comp
  projection i j x hi hj := (S.projection i j x hi hj).trans
    (PrincipalCocycleBundle.geometricData_transition (principalData n) i j x hi hj).symm

/-- Passing to the extracted Lorentz target keeps the original Spin transition representatives. -/
theorem toExtracted_transition {n : WithTop ℕ∞} (S : Lift (PuncturedPlaneSpinLifts.lorentzData n))
    (i j : Fin 3) (x : Plane) : (toExtracted S).transition i j x = S.transition i j x := rfl

/-- Smooth chart-sign equivalence for these lifts is identical before and after target transition extraction. -/
theorem gaugeEq_toExtracted {n : WithTop ℕ∞} (S T : Lift (PuncturedPlaneSpinLifts.lorentzData n)) :
    GaugeEq (toExtracted S) (toExtracted T) ↔ GaugeEq S T := Iff.rfl

/-- The geometric realization of the identity Spin lift on the punctured plane. -/
def reference (n : WithTop ℕ∞) : GeometricSpinStructure.Lift model (atlas n) n :=
  realize (smoothAtlas n) (toExtracted (PuncturedPlaneSpinLifts.reference n))

/-- The geometric realization of the lift twisted by the explicit sign cycle on the same three charts. -/
def twisted (n : WithTop ℕ∞) : GeometricSpinStructure.Lift model (atlas n) n :=
  realize (smoothAtlas n) (toExtracted
    (twist (PuncturedPlaneSpinLifts.reference n) (PuncturedPlaneSpinSign.cocycle n)))

/-- The canonical sections of the two geometric lifts yield distinct transition gauge classes on the cover. -/
theorem not_gauge_related (n : WithTop ℕ∞) :
    ¬ GaugeEq (transitions (smoothAtlas n) (twisted n)) (transitions (smoothAtlas n) (reference n)) := by
  intro h
  let S := PuncturedPlaneSpinLifts.reference n
  let T := twist S (PuncturedPlaneSpinSign.cocycle n)
  have hT := gaugeEq_of_agree (transitions_realize (smoothAtlas n) (toExtracted T))
  have hS := gaugeEq_of_agree (transitions_realize (smoothAtlas n) (toExtracted S))
  have hTS : GaugeEq (toExtracted T) (toExtracted S) :=
    gaugeEq_equivalence.trans (gaugeEq_equivalence.symm hT) (gaugeEq_equivalence.trans h hS)
  exact PuncturedPlaneSpinLifts.inequivalent n
    ((liftClass_eq_iff T S).mpr ((gaugeEq_toExtracted T S).mp hTS))

/-- No smooth equivariant diffeomorphism between the twisted and reference Spin spaces commutes with their maps to the common Lorentz target. -/
theorem not_isomorphic (n : WithTop ℕ∞) : ¬ Nonempty (Between (twisted n) (reference n)) :=
  fun h => not_gauge_related n
    ((SpinGeometricLiftClasses.nonempty_between_iff_gauge (smoothAtlas n) _ _).mp h)

/-- The two realized lifts represent distinct physical isomorphism classes of smooth geometric Spin structures. -/
theorem geometricClass_ne (n : WithTop ℕ∞) :
    SpinGeometricLiftClasses.geometricClass (smoothAtlas n) (twisted n) ≠
      SpinGeometricLiftClasses.geometricClass (smoothAtlas n) (reference n) :=
  fun h => not_isomorphic n
    ((SpinGeometricLiftClasses.geometricClass_eq_iff (smoothAtlas n) _ _).mp h)

end FoliationQM.PuncturedPlaneGeometricSpin
