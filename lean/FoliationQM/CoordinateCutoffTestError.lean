module

public import FoliationQM.CoordinateCutoffPairing
public import FoliationQM.CoordinateCutoffTests

/-!
# Actual compact-test commutators and local error decay

Source: v13 `eq:log_cutoff_l2_bound` and its following first-derivative
commutator argument, component kinds C and D. The error is defined from the
actual differentiated cutoff test. A bound derived from the original compact
test is fixed before the field, direction and radius; the field needs L2 only
on a set containing that test's support. General curved geometry and the
metric-weighted weak PDE contraction remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffTestError

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff CoordinateCutoffPairing
open scoped ContDiff Topology

/-- The actual differentiated complex cutoff test minus its ordinary test-derivative term, paired with the same field. -/
def commutator (ε : ℝ) (φ ψ : Covector → ℂ) (v x : Covector) : ℂ :=
  (star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) -
    profile ε x • star (fderiv ℝ φ x v)) * ψ x

private theorem commutator_eq {ε : ℝ} {φ ψ : Covector → ℂ} {x : Covector}
    (h0 : 0 < ε) (h1 : ε < 1) (hφ : DifferentiableAt ℝ φ x) (v : Covector) :
    commutator ε φ ψ v x =
      (fderiv ℝ (profile ε) x v) • (star (φ x) * ψ x) := by
  rw [commutator, CoordinateCutoffTests.directional_test h0 h1 hφ v]
  simp only [star_add, star_smul, star_trivial, add_sub_cancel_right, smul_mul_assoc]

/-- A bound derived from the compact test controls its actual commutator for every local L2 field, direction and radius, with genuine product L2 data, the exact derivative identity and integrability before the separate test/field energy bound. -/
theorem test_error_data {φ : Covector → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x, ‖φ x‖ ≤ B) ∧
      ∀ (U : Set Covector) (ψ : Covector → ℂ), tsupport φ ⊆ U →
        MemLp ψ 2 (volume.restrict U) →
        MemLp (fun x => star (φ x) * ψ x) 2 (volume.restrict (tsupport φ)) ∧
        ∀ (v : Covector) {ε : ℝ}, 0 < ε → ε < 1 →
          (∀ x, commutator ε φ ψ v x =
            (fderiv ℝ (profile ε) x v) • (star (φ x) * ψ x)) ∧
          IntegrableOn (commutator ε φ ψ v) (tsupport φ) volume ∧
          IntegrableOn (fun x => ‖commutator ε φ ψ v x‖) (tsupport φ) volume ∧
          ‖∫ x in tsupport φ, commutator ε φ ψ v x‖ ≤
            ∫ x in tsupport φ, ‖commutator ε φ ψ v x‖ ∧
          (∫ x in tsupport φ, ‖commutator ε φ ψ v x‖) ≤
            B * ‖v‖ * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
              Real.sqrt (∫ x in tsupport φ, ‖ψ x‖ ^ 2) := by
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hB0 : 0 ≤ B := (norm_nonneg (φ 0)).trans (hB 0)
  refine ⟨B, hB0, hB, ?_⟩
  intro U ψ hs hψ
  have hψC : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hφtop : MemLp φ ⊤ (volume.restrict (tsupport φ)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hc _
  have hF : MemLp (fun x => star (φ x) * ψ x) 2
      (volume.restrict (tsupport φ)) := hφtop.star.mul hψC
  refine ⟨hF, ?_⟩
  intro v ε h0 h1
  have heq : commutator ε φ ψ v =
      fun x => (fderiv ℝ (profile ε) x v) • (star (φ x) * ψ x) := by
    funext x
    exact commutator_eq h0 h1 (hφ.differentiable (by simp) x) v
  have hF2 := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have hψ2 := (memLp_two_iff_integrable_sq_norm hψC.aestronglyMeasurable).1 hψC
  have he : (∫ x in tsupport φ, ‖star (φ x) * ψ x‖ ^ 2) ≤
      B ^ 2 * (∫ x in tsupport φ, ‖ψ x‖ ^ 2) := by
    calc
      _ ≤ ∫ x in tsupport φ, B ^ 2 * ‖ψ x‖ ^ 2 := by
        apply integral_mono hF2 (hψ2.const_mul (B ^ 2))
        intro x
        calc
          ‖star (φ x) * ψ x‖ ^ 2 = (‖φ x‖ * ‖ψ x‖) ^ 2 := by
            rw [norm_mul, norm_star]
          _ ≤ (B * ‖ψ x‖) ^ 2 := by gcongr; exact hB x
          _ = B ^ 2 * ‖ψ x‖ ^ 2 := by ring
      _ = _ := integral_const_mul _ _
  have hroot : Real.sqrt (∫ x in tsupport φ, ‖star (φ x) * ψ x‖ ^ 2) ≤
      B * Real.sqrt (∫ x in tsupport φ, ‖ψ x‖ ^ 2) := by
    calc
      _ ≤ Real.sqrt (B ^ 2 * (∫ x in tsupport φ, ‖ψ x‖ ^ 2)) :=
        Real.sqrt_le_sqrt he
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB0]
  have H := pairing_data (tsupport φ) hc hF h0 h1 v
  refine ⟨congrFun heq, ?_, ?_, ?_, ?_⟩
  · simpa only [heq] using H.1
  · simpa only [heq] using H.2.1
  · simpa only [heq] using H.2.2.1
  · rw [heq]
    calc
      _ ≤ ‖v‖ * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
          Real.sqrt (∫ x in tsupport φ, ‖star (φ x) * ψ x‖ ^ 2) := H.2.2.2
      _ ≤ ‖v‖ * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
          (B * Real.sqrt (∫ x in tsupport φ, ‖ψ x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hroot (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      _ = _ := by ring

/-- For the same smooth compact test and any field square integrable on a containing set, both the integral of the actual commutator norm and its actual complex integral vanish through positive cutoff radii. -/
theorem test_error_decay {φ ψ : Covector → ℂ} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U)) (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ, ‖commutator ε φ ψ v x‖)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ, commutator ε φ ψ v x)
      (𝓝[>] 0) (𝓝 0) := by
  have hψC : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hφtop : MemLp φ ⊤ (volume.restrict (tsupport φ)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hc _
  have hF : MemLp (fun x => star (φ x) * ψ x) 2
      (volume.restrict (tsupport φ)) := hφtop.star.mul hψC
  have H := pairing_decay (tsupport φ) hc hF v
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, commutator ε φ ψ v =
      fun x => (fderiv ℝ (profile ε) x v) • (star (φ x) * ψ x) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    funext x
    exact commutator_eq hε.1 hε.2 (hφ.differentiable (by simp) x) v
  exact ⟨H.1.congr' (heq.mono fun ε h => by dsimp only; rw [h]),
    H.2.congr' (heq.mono fun ε h => by dsimp only; rw [h])⟩

end FoliationQM.CoordinateCutoffTestError
