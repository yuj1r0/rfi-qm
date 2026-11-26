module
public import FoliationQM.CliffordSpinCocycleCorrection

/-!
# Comparing two choices of Spin lifts of the same Lorentz transitions

Source scope: the Spin transition component of v13 `prop:takabayasi`.
The ordered ratio of two normalized pair lifts is a correcting sign on
each pair overlap. This comparison applies to lifts with arbitrary
triple defects.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPairLiftDifference
open CliffordSpinTransitionLifts CliffordSpinCocycleCorrection

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The ordered ratio of arbitrary normalized pair lifts of the same physical transitions is a smooth sign correction. -/
def difference (P Q : PairLifts D) : Correction D where
  value i j x := Q.transition i j x * (P.transition i j x)⁻¹
  smooth_value i j :=
    (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
      ((Q.smooth_transition i j).prodMk ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn
        (P.smooth_transition i j)))
  projection i j x hi hj := by
    rw [map_mul, map_inv, Q.projection i j x hi hj, P.projection i j x hi hj, mul_inv_cancel]
  identity i x hi := by rw [Q.identity i x hi, P.identity i x hi, inv_one, mul_one]

/-- The sign taking the first lift to the second is their literal transition ratio on each pair. -/
theorem difference_value (P Q : PairLifts D) (i j : ι) (x : B) :
    (difference P Q).value i j x = Q.transition i j x * (P.transition i j x)⁻¹ := rfl

private theorem pairLifts_ext {P Q : PairLifts D} (h : P.transition = Q.transition) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Applying the ratio correction recovers the second family of pair lifts exactly. -/
theorem corrected_difference (P Q : PairLifts D) : corrected P (difference P Q) = Q := by
  apply pairLifts_ext
  funext i j x
  exact inv_mul_cancel_right _ _

/-- Every correcting sign which changes the first transition to the second equals their ratio at that point. -/
theorem difference_unique (P Q : PairLifts D) (b : Correction D) (i j : ι) (x : B)
    (h : (corrected P b).transition i j x = Q.transition i j x) :
    b.value i j x = (difference P Q).value i j x := by
  rw [difference_value, ← h, corrected_transition, mul_inv_cancel_right]

/-- On every triple overlap the defects of arbitrary lift choices differ by the explicit pair ratio. -/
theorem defectValue_difference (P Q : PairLifts D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (_hk : x ∈ D.domain k) :
    defectValue Q i j k x =
      (difference P Q).value j k x * (difference P Q).value i j x *
        defectValue P i j k x * ((difference P Q).value i k x)⁻¹ := by
  have h := corrected_defectValue P (difference P Q) i j k x hi hj
  rwa [corrected_difference] at h

end FoliationQM.SpinPairLiftDifference
