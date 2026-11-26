module
public import FoliationQM.AdaptedSpinGaugeExtraction
public import FoliationQM.AdaptedSpinGaugeMap

/-!
# Classification of adapted geometric Spin lifts by degree-one signs

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
A chartwise sign equivalence constructs a physical bundle isomorphism.
Conversely such a diffeomorphism determines its chart signs. Extracting
and realizing genuine cocycles therefore classify the geometric objects
using the degree-one signs of the specified cover.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinGeometricLiftClasses
open CliffordSpinLorentzSmooth LorentzMatrixGroup SpinLiftIsomorphism SpinLiftChartGauge
open SpinLiftSignDifference SpinSignHOne

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- A smooth physical isomorphism exists exactly when chartwise signs identify the two extracted transition lifts. -/
theorem nonempty_between_iff_gauge (A T : GeometricSpinStructure.Lift I L n) :
    Nonempty (Between A T) ↔ GaugeEq (transitions LM A) (transitions LM T) :=
  ⟨fun ⟨e⟩ => AdaptedSpinGaugeExtraction.gauge_of_between LM A T e,
    AdaptedSpinGaugeMap.nonempty_between_of_gauge LM A T⟩

/-- The physical isomorphism condition is equivalent to neutrality of the degree-one relative sign class. -/
theorem nonempty_between_iff_neutral (A T : GeometricSpinStructure.Lift I L n) :
    Nonempty (Between A T) ↔ classOf (difference (transitions LM A) (transitions LM T)) = 1 :=
  (nonempty_between_iff_gauge LM A T).trans (gaugeEq_iff_difference _ _)

/-- Physical isomorphism of the original total spaces is an equivalence relation on adapted lifts. -/
def physicalSetoid : Setoid (GeometricSpinStructure.Lift I L n) where
  r A T := Nonempty (Between A T)
  iseqv := {
    refl := fun A => (nonempty_between_iff_gauge LM A A).mpr (gaugeEq_equivalence.refl _)
    symm := fun {A T} h => (nonempty_between_iff_gauge LM T A).mpr
      (gaugeEq_equivalence.symm ((nonempty_between_iff_gauge LM A T).mp h))
    trans := fun {A T S} h k => (nonempty_between_iff_gauge LM A S).mpr
      (gaugeEq_equivalence.trans ((nonempty_between_iff_gauge LM A T).mp h)
        ((nonempty_between_iff_gauge LM T S).mp k)) }

/-- The classes of adapted geometric structures under smooth principal isomorphisms over the physical target. -/
def GeometricClass := Quotient (physicalSetoid LM)

/-- A geometric structure defines a class by its actual smooth physical isomorphism type. -/
def geometricClass (A : GeometricSpinStructure.Lift I L n) : GeometricClass LM :=
  Quotient.mk _ A

/-- Geometric class equality is existence of a diffeomorphism preserving the right action and physical map. -/
theorem geometricClass_eq_iff (A T : GeometricSpinStructure.Lift I L n) :
    geometricClass LM A = geometricClass LM T ↔ Nonempty (Between A T) := Quotient.eq

variable [IsManifold I n B]

/-- Extraction and geometric realization give inverse bijections between physical isomorphism classes and chart-gauge classes on the fixed cover. -/
def transitionEquiv : GeometricClass LM ≃ LiftClass (AdaptedGeometricSpinLift.lorentzData LM) where
  toFun := Quotient.map (transitions LM) (fun A T h => (nonempty_between_iff_gauge LM A T).mp h)
  invFun := Quotient.map (realize LM) (fun S T h => (nonempty_between_iff_gauge LM _ _).mpr
    (gaugeEq_equivalence.trans (gaugeEq_of_agree (transitions_realize LM S))
      (gaugeEq_equivalence.trans h (gaugeEq_equivalence.symm
        (gaugeEq_of_agree (transitions_realize LM T)))) ))
  left_inv c := Quotient.inductionOn c fun A => (geometricClass_eq_iff LM _ A).mpr
    ((nonempty_between_iff_gauge LM _ A).mpr (gaugeEq_of_agree (transitions_realize LM _)))
  right_inv c := Quotient.inductionOn c fun S => (liftClass_eq_iff _ S).mpr
    (gaugeEq_of_agree (transitions_realize LM S))

/-- Choosing a reference geometric lift identifies the fixed-cover degree-one sign group with all physical isomorphism classes adapted to that cover. -/
def basedEquiv (A : GeometricSpinStructure.Lift I L n) :
    H1 I (AdaptedGeometricSpinLift.lorentzData LM).domain n ≃ GeometricClass LM :=
  (SpinLiftHOneTorsor.basedEquiv (liftClass (transitions LM A))).trans (transitionEquiv LM).symm

/-- Under the based geometric classification the unit sign class gives the chosen reference structure. -/
theorem basedEquiv_one (A : GeometricSpinStructure.Lift I L n) :
    basedEquiv LM A 1 = geometricClass LM A := by
  apply (transitionEquiv LM).injective
  change transitionEquiv LM ((transitionEquiv LM).symm
    (SpinLiftHOneTorsor.act 1 (liftClass (transitions LM A)))) = liftClass (transitions LM A)
  rw [Equiv.apply_symm_apply, SpinLiftHOneTorsor.act_one]

end FoliationQM.SpinGeometricLiftClasses
