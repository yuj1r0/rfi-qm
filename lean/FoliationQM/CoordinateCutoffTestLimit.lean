module

public import FoliationQM.CoordinateCutoffL1Limit
public import FoliationQM.CoordinateCutoffTestError

/-!
# Actual compact-test pairings through the coordinate cutoff limit

Source: v13 `eq:log_cutoff_l2_bound` and its following cutoff-limit
argument, component kinds C and D. Smooth compact tests and their actual
directional derivatives have genuine L1 pairings with a field square
integrable on any containing set. The full differentiated cutoff test
converges by ordinary dominated convergence together with the verified
commutator decay. No derivative or field equation is required of the field.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffTestLimit

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff CoordinateCutoffL1Limit
open CoordinateCutoffTestError
open scoped ContDiff Topology

/-- Smooth compact tests and their actual directional derivatives, both before and after cutoff, have genuine L1 pairings on the original support with every field square integrable on a containing set. -/
theorem test_pairing_data {φ ψ : Covector → ℂ} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U)) (v : Covector) :
    IntegrableOn (fun x => star (φ x) * ψ x) (tsupport φ) volume ∧
    IntegrableOn (fun x => star (fderiv ℝ φ x v) * ψ x) (tsupport φ) volume ∧
    ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      IntegrableOn (fun x => star (CoordinateCutoffTests.test ε φ x) * ψ x)
        (tsupport φ) volume ∧
      IntegrableOn (fun x => star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) * ψ x)
        (tsupport φ) volume := by
  have hψC : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hp {a : Covector → ℂ} (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) :
      IntegrableOn (fun x => star (a x) * ψ x) (tsupport φ) volume ∧
      IntegrableOn (fun x => star (fderiv ℝ a x v) * ψ x) (tsupport φ) volume := by
    have ha2 : MemLp a 2 volume := ha.continuous.memLp_of_hasCompactSupport hca
    have hd2 : MemLp (fun x => fderiv ℝ a x v) 2 volume :=
      ((ha.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))).memLp_of_hasCompactSupport
        (hca.fderiv_apply ℝ v)
    have haC : MemLp a 2 (volume.restrict (tsupport φ)) :=
      MemLp.mono_measure Measure.restrict_le_self ha2
    have hdC : MemLp (fun x => fderiv ℝ a x v) 2 (volume.restrict (tsupport φ)) :=
      MemLp.mono_measure Measure.restrict_le_self hd2
    exact ⟨haC.star.integrable_mul hψC, hdC.star.integrable_mul hψC⟩
  have H := hp hφ hc
  refine ⟨H.1, H.2, ?_⟩
  intro ε h0 h1
  have Hε := CoordinateCutoffTests.test_data h0 h1 hφ hc hs
  exact hp Hε.1 Hε.2.1

/-- Both the actual cutoff-test pairing and its full directional-derivative pairing converge to the original pairings on the same compact support as the positive radius tends to zero. -/
theorem test_pairing_limits {φ ψ : Covector → ℂ} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U)) (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ, star (CoordinateCutoffTests.test ε φ x) * ψ x)
      (𝓝[>] 0) (𝓝 (∫ x in tsupport φ, star (φ x) * ψ x)) ∧
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ,
        star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) * ψ x)
      (𝓝[>] 0) (𝓝 (∫ x in tsupport φ, star (fderiv ℝ φ x v) * ψ x)) := by
  have H := test_pairing_data hφ hc hs hψ v
  have hordinary := cutoff_limits (tsupport φ) H.1
  have hderivative := cutoff_limits (tsupport φ) H.2.1
  constructor
  · simpa only [CoordinateCutoffTests.test, star_smul, star_trivial, smul_mul_assoc]
      using hordinary.2
  · have herror := (test_error_decay hφ hc hs hψ v).2
    have hsum := herror.add hderivative.2
    have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (∫ x in tsupport φ, commutator ε φ ψ v x) +
          (∫ x in tsupport φ, profile ε x • (star (fderiv ℝ φ x v) * ψ x)) =
        ∫ x in tsupport φ, star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) * ψ x := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      obtain ⟨_, _, _, hdata⟩ := test_error_data hφ hc
      have hic := ((hdata U ψ hs hψ).2 v hε.1 hε.2).2.1
      have hiw := (cutoff_data (tsupport φ) H.2.1 hε.1 hε.2).1
      rw [← integral_add hic hiw]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [CoordinateCutoffTestError.commutator, sub_mul, smul_mul_assoc, sub_add_cancel]
    simpa only [zero_add] using hsum.congr' heq

end FoliationQM.CoordinateCutoffTestLimit
