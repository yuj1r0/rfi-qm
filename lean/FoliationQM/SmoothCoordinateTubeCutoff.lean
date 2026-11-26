module

public import FoliationQM.ProductTubeCoordinates
public import FoliationQM.SmoothProductTubeCutoffEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Smooth cutoff estimates in the original four real coordinates

Source: v13 `eq:log_cutoff_wallstrom` and `eq:log_cutoff_l2_bound`, component
kinds C and D. An explicit measure-preserving continuous linear equivalence
transports the flat product cutoff to the manuscript's original Covector space.
That space has the Pi sup norm: the derivative energy comparison therefore
retains the actual fixed operator norm of the coordinate map. This is a flat
coordinate result, not an assertion about arbitrary curved auxiliary metrics.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothCoordinateTubeCutoff

open Filter MeasureTheory Set ProductTubeCoordinates
open scoped Topology ContDiff

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- The actual smooth product cutoff pulled back to the original four real coordinates. -/
def profile (ε : ℝ) (x : Covector) : ℝ :=
  SmoothProductTubeCutoff.profile ε (coordinates x)

/-- A finite tangential region pulled back by the actual coordinate equivalence. -/
def tube (K : Set ℂ) : Set Covector :=
  coordinates ⁻¹' SmoothProductTubeCutoffEnergy.tube K

/-- The coordinate axis with both normal coordinates zero has zero actual four-dimensional coordinate volume. -/
theorem axis_null : volume {x : Covector | x 2 = 0 ∧ x 3 = 0} = 0 := by
  rw [← axis_preimage,
    volume_preserving.measure_preimage_emb coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  exact SmoothProductTubeCutoffEnergy.axis_null

/-- The same coordinate cutoff has the zero and one plateaux at normal radii ε² and ε, with values in the unit interval. -/
theorem profile_spec {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ x : Covector, ‖(coordinates x).snd‖ ≤ ε ^ 2 → profile ε x = 0) ∧
    (∀ x : Covector, ε ≤ ‖(coordinates x).snd‖ → profile ε x = 1) ∧
    ∀ x : Covector, 0 ≤ profile ε x ∧ profile ε x ≤ 1 := by
  obtain ⟨hz, ho, hr⟩ := SmoothProductTubeCutoff.profile_spec h0 h1
  exact ⟨fun x h => hz (coordinates x) h, fun x h => ho (coordinates x) h,
    fun x => hr (coordinates x)⟩

/-- The pulled-back cutoff is infinitely differentiable at every coordinate point, including the axis. -/
theorem contDiff_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (profile ε) :=
  (SmoothProductTubeCutoff.contDiff_profile h0 h1).comp coordinates.contDiff

/-- Its actual Fréchet derivative is the product cutoff derivative composed with the continuous linear coordinate map. -/
theorem fderiv_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (x : Covector) :
    fderiv ℝ (profile ε) x =
      (fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)).comp
        coordinates.toContinuousLinearMap := by
  exact (((SmoothProductTubeCutoff.contDiff_profile h0 h1).differentiable
    (by simp) (coordinates x)).hasFDerivAt.comp x
      coordinates.toContinuousLinearMap.hasFDerivAt).fderiv

/-- Each actual coordinate direction has unit Hilbert length after transport, so the directional cutoff derivative is bounded by the product operator norm without an extra coordinate factor. -/
theorem norm_directional_derivative_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (x : Covector) (i : Fin 4) :
    ‖fderiv ℝ (profile ε) x (RNCCoordinateConnection.axis i)‖ ≤
      ‖fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)‖ := by
  rw [fderiv_profile h0 h1]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    coordinate_axes.2.2.2.2 i, mul_one] using
    (fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)).le_opNorm
      (coordinates (RNCCoordinateConnection.axis i))

/-- At every point off the coordinate axis the same cutoff is eventually exactly one through positive radii. -/
theorem eventually_profile_eq_one {x : Covector} (hx : ¬ (x 2 = 0 ∧ x 3 = 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), profile ε x = 1 := by
  apply SmoothProductTubeCutoff.eventually_profile_eq_one
  intro hz
  exact hx (show x ∈ {y : Covector | y 2 = 0 ∧ y 3 = 0} from
    axis_preimage ▸ (show x ∈ coordinates ⁻¹' {y : Space | y.snd = 0} from hz))

/-- On each finite-tangential-volume coordinate tube the actual derivative genuinely belongs to L²; its finite standard seminorm is the square root of its genuine energy. -/
theorem derivative_l2_data (K : Set ℂ) (hK : volume K ≠ ⊤)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) ∧
    IntegrableOn (fun x : Covector => ‖fderiv ℝ (profile ε) x‖ ^ 2) (tube K) volume ∧
    (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K))).toReal =
      Real.sqrt (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) := by
  have hm := volume_preserving.restrict_preimage_emb
    coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (SmoothProductTubeCutoffEnergy.tube K)
  have hp := (SmoothProductTubeCutoffEnergy.derivative_l2_data K hK h0 h1).1.comp_measurePreserving hm
  have hlp : MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) := by
    apply (hp.norm.mul_const ‖coordinates.toContinuousLinearMap‖).mono'
      ((contDiff_profile h0 h1).continuous_fderiv (by simp)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [fderiv_profile h0 h1]
      exact (fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)).opNorm_comp_le _
  have hi := (memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).1 hlp
  refine ⟨hlp, hi, ?_⟩
  have hn : eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) =
      ENNReal.ofReal (Real.sqrt (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hlp
  rw [hn, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- Genuine coordinate energy is bounded by genuine Hilbert product energy times the square of the actual coordinate-map operator norm; no sup-norm isometry is assumed. -/
theorem energy_comparison (K : Set ℂ) (hK : volume K ≠ ⊤)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 ≤ (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ∧
    (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ≤
      ‖coordinates.toContinuousLinearMap‖ ^ 2 *
        (∫ y in SmoothProductTubeCutoffEnergy.tube K,
          ‖fderiv ℝ (SmoothProductTubeCutoff.profile ε) y‖ ^ 2) := by
  let G : Space → ℝ := fun y => ‖fderiv ℝ (SmoothProductTubeCutoff.profile ε) y‖ ^ 2
  have hm := volume_preserving.restrict_preimage_emb
    coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (SmoothProductTubeCutoffEnergy.tube K)
  have hi : Integrable (G ∘ coordinates) (volume.restrict (tube K)) :=
    (hm.integrable_comp_emb coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding).2
      (SmoothProductTubeCutoffEnergy.energy_integral K hK h0 h1).1
  have he := hm.integral_comp coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding G
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  calc
    _ ≤ ∫ x in tube K, ‖coordinates.toContinuousLinearMap‖ ^ 2 * G (coordinates x) := by
      apply integral_mono (derivative_l2_data K hK h0 h1).2.1
        (hi.const_mul (‖coordinates.toContinuousLinearMap‖ ^ 2))
      intro x
      change ‖fderiv ℝ (profile ε) x‖ ^ 2 ≤
        ‖coordinates.toContinuousLinearMap‖ ^ 2 * G (coordinates x)
      rw [fderiv_profile h0 h1]
      have hb := (fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)).opNorm_comp_le
        coordinates.toContinuousLinearMap
      calc
        _ ≤ (‖fderiv ℝ (SmoothProductTubeCutoff.profile ε) (coordinates x)‖ *
            ‖coordinates.toContinuousLinearMap‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hb
        _ = _ := by dsimp [G]; ring
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (‖coordinates.toContinuousLinearMap‖ ^ 2 * ·) he

/-- One nonnegative constant works before all tangential regions and admissible radii, with the explicit coordinate norm factor and actual tangential volume. -/
theorem exists_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : Set ℂ, volume K ≠ ⊤ → ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 ≤ (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ∧
      (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ≤
        ‖coordinates.toContinuousLinearMap‖ ^ 2 *
          (volume.real K * (2 * Real.pi * C ^ 2 / |Real.log ε|)) := by
  obtain ⟨C, hC, hb⟩ := SmoothProductTubeCutoffEnergy.exists_energy_bound
  refine ⟨C, hC, fun K hK ε h0 h1 => ⟨(energy_comparison K hK h0 h1).1, ?_⟩⟩
  exact (energy_comparison K hK h0 h1).2.trans
    (mul_le_mul_of_nonneg_left (hb K hK ε h0 h1).2 (sq_nonneg _))

/-- On each fixed finite-volume tangential region both actual coordinate energy and finite derivative L² norm vanish as the positive cutoff radius tends to zero. -/
theorem tendsto_energy_and_l2_norm (K : Set ℂ) (hK : volume K ≠ ⊤) :
    Tendsto (fun ε : ℝ => ∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ =>
      (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have hp := (SmoothProductTubeCutoffEnergy.tendsto_energy_and_l2_norm K hK).1.const_mul
    (‖coordinates.toContinuousLinearMap‖ ^ 2)
  have he : Tendsto (fun ε : ℝ => ∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => sq_nonneg _))
      ?_ (by simpa only [mul_zero] using hp)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (energy_comparison K hK hε.1 hε.2).2
  refine ⟨he, ?_⟩
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hs0 : Tendsto (fun ε : ℝ => Real.sqrt
      (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using hs
  apply hs0.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (derivative_l2_data K hK hε.1 hε.2).2.2.symm

end FoliationQM.SmoothCoordinateTubeCutoff
