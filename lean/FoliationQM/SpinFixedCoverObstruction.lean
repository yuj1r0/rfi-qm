module
public import FoliationQM.SpinSignDefectRepresentative
public import FoliationQM.SpinPairLiftDifference
public import FoliationQM.SpinSignDefectExample

/-!
# The Spin obstruction class of a fixed Lorentz cover

Source scope: the global Spin-frame component of v13 `prop:takabayasi`.
The physical triple signs define a class independent of normalized pair-lift
choices. Its neutral value characterizes an actual Spin cocycle over the
specified cover.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinFixedCoverObstruction
open CliffordSpinSignKernel CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinPairLiftDifference SpinSignCohomology SpinSignDefectRepresentative

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The class of the actual triple-overlap defect is independent of the normalized Spin pair lifts. -/
theorem classOf_independent (P Q : PairLifts D) :
    classOf (representative P) = classOf (representative Q) := by
  apply (classOf_eq_iff _ _).mpr
  refine ⟨ofCorrection (difference P Q), ?_⟩
  intro i j k x hi hj hk
  have h := representative_corrected P (difference P Q) i j k x hi hj hk
  rwa [corrected_difference] at h

/-- The physical defect class is neutral exactly when smooth central signs cancel its triple defects on this cover. -/
theorem classOf_neutral_iff_correction (P : PairLifts D) :
    classOf (representative P) = neutralClass I D.domain n ↔
      ∃ s : Correction D, RemovesDefect P s := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (classOf_eq_iff _ _).mp h
    refine ⟨toCorrection (D := D) b, (removesDefect_iff P b).mpr ?_⟩
    intro i j k x hi hj hk
    exact (hb i j k x hi hj hk).symm
  · rintro ⟨s, hs⟩
    apply (classOf_eq_iff _ _).mpr
    refine ⟨ofCorrection s, ?_⟩
    intro i j k x hi hj hk
    change (1 : Kernel) = _
    rw [← representative_corrected P s i j k x hi hj hk]
    apply Subtype.ext
    rw [representative_val _ i j k x hi hj hk]
    exact ((defectValue_eq_one_iff _ i j k x).mpr
      ((corrected_comp_iff P s i j k x hi hj).mpr (hs i j k x hi hj hk))).symm

/-- The neutral class is equivalent to existence of a genuine Spin cocycle projecting to the original Lorentz transitions. -/
theorem classOf_neutral_iff_lift (P : PairLifts D) :
    classOf (representative P) = neutralClass I D.domain n ↔ HasSpinCocycleLift D :=
  (classOf_neutral_iff_correction P).trans (exists_correction_iff P)

/-- The obstruction attached to Lorentz data with normalized pair lifts available on this cover. -/
def obstruction (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : Nonempty (PairLifts D)) :
    ObstructionClass I D.domain n := classOf (representative (Classical.choice h))

/-- Any particular normalized lift family computes the class attached to the Lorentz data. -/
theorem obstruction_eq_classOf (h : Nonempty (PairLifts D)) (P : PairLifts D) :
    obstruction D h = classOf (representative P) :=
  classOf_independent (Classical.choice h) P

/-- The fixed-cover obstruction is neutral exactly when the original smooth Lorentz cocycle lifts on that cover. -/
theorem obstruction_neutral_iff_lift (h : Nonempty (PairLifts D)) :
    obstruction D h = neutralClass I D.domain n ↔ HasSpinCocycleLift D :=
  classOf_neutral_iff_lift (Classical.choice h)

/-- Simple connectivity and local path connectivity on nonempty pair overlaps supply the lift family used to compute the obstruction. -/
theorem constructed_class_neutral_iff_lift (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j) →
      SimplyConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j))
    (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j) →
      LocallyPathConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap D i j)) :
    classOf (representative (CliffordSpinPairLiftConstruction.pairLifts D hsc hlpc)) =
        neutralClass I D.domain n ↔ HasSpinCocycleLift D :=
  classOf_neutral_iff_lift _

/-- The two-chart real example has neutral class even though its actual triple defect at the origin is the negative Clifford sign. -/
theorem example_neutral_with_negative_defect (n : WithTop ℕ∞) :
    classOf (representative (SpinSignDefectExample.pairLifts n)) =
        neutralClass _ (SpinSignDefectExample.lorentzData n).domain n ∧
      defectValue (SpinSignDefectExample.pairLifts n) 0 1 0 0 =
        CliffordSpinEquivalence.negativeOne :=
  ⟨(classOf_neutral_iff_correction _).mpr
    ⟨SpinSignDefectExample.signCorrection n, SpinSignDefectExample.removesDefect n⟩,
    SpinSignDefectExample.defectValue_negativeOne n 0⟩

end FoliationQM.SpinFixedCoverObstruction
