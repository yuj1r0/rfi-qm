module

public import FoliationQM.SmoothNormalPlaneCutoff
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The smooth logarithmic cutoff on an actual flat four-dimensional tube

Source: v13 `eq:log_cutoff_wallstrom` and `eq:log_cutoff_l2_bound`, component
kinds C and D. The second complex coordinate is the normal plane in the genuine
Euclidean product norm. Its radius equals the actual distance to the flat axis.
The derivative and its operator norm come from this same smooth cutoff. General
curved tubular geometry and arbitrary positive auxiliary metrics remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothProductTubeCutoff

open Filter Set
open scoped Topology ContDiff

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- The same smooth plane cutoff composed with the actual normal projection of the Euclidean four-dimensional product. -/
def profile (ε : ℝ) (x : Space) : ℝ :=
  SmoothNormalPlaneCutoff.profile ε x.snd

/-- The normal radius is the genuine distance to the flat axis, and the same cutoff is the scalar profile of that actual distance. -/
theorem distance_to_axis (ε : ℝ) (x : Space) :
    Metric.infDist x {y : Space | y.snd = 0} = ‖x.snd‖ ∧
    profile ε x = SmoothLogarithmicCutoffProfile.profile ε
      (Metric.infDist x {y : Space | y.snd = 0}) := by
  have hd : Metric.infDist x {y : Space | y.snd = 0} = ‖x.snd‖ := by
    apply le_antisymm
    · have he : x - WithLp.toLp 2 (x.fst, (0 : ℂ)) =
          WithLp.toLp 2 ((0 : ℂ), x.snd) := by
        apply WithLp.ofLp_injective 2
        change x.ofLp - (x.ofLp.1, (0 : ℂ)) = ((0 : ℂ), x.ofLp.2)
        ext <;> simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero]
      calc
        _ ≤ dist x (WithLp.toLp 2 (x.fst, (0 : ℂ))) :=
          Metric.infDist_le_dist_of_mem (show (WithLp.toLp 2 (x.fst, (0 : ℂ))).snd = 0 from rfl)
        _ = ‖x.snd‖ := by rw [dist_eq_norm, he, WithLp.norm_toLp_snd]
    · apply (Metric.le_infDist (show ({y : Space | y.snd = 0} : Set Space).Nonempty
        from ⟨0, rfl⟩)).2
      intro y hy
      change y.snd = 0 at hy
      rw [dist_eq_norm]
      have hxy : (x - y).snd = x.snd - y.snd := rfl
      simpa only [hxy, hy, sub_zero] using WithLp.norm_snd_le ℂ (x - y)
  exact ⟨hd, by rw [hd]; rfl⟩

/-- The tube cutoff is zero at normal radius at most ε², one at radius at least ε, and takes values between zero and one everywhere. -/
theorem profile_spec {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ x : Space, ‖x.snd‖ ≤ ε ^ 2 → profile ε x = 0) ∧
    (∀ x : Space, ε ≤ ‖x.snd‖ → profile ε x = 1) ∧
    ∀ x : Space, 0 ≤ profile ε x ∧ profile ε x ≤ 1 := by
  obtain ⟨hz, ho, hr⟩ := SmoothNormalPlaneCutoff.profile_spec h0 h1
  exact ⟨fun x h => hz x.snd h, fun x h => ho x.snd h, fun x => hr x.snd⟩

/-- The actual flat-tube cutoff is infinitely real differentiable, including every point on its axis. -/
theorem contDiff_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (profile ε) :=
  (SmoothNormalPlaneCutoff.contDiff_profile h0 h1).comp (WithLp.sndL 2 ℝ ℂ ℂ).contDiff

/-- The genuine tube Fréchet derivative is the actual plane derivative composed with the continuous linear normal projection. -/
theorem fderiv_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (x : Space) :
    fderiv ℝ (profile ε) x =
      (fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) x.snd).comp (WithLp.sndL 2 ℝ ℂ ℂ) := by
  exact (((SmoothNormalPlaneCutoff.contDiff_profile h0 h1).differentiable
    (by simp) x.snd).hasFDerivAt.comp x (WithLp.sndL 2 ℝ ℂ ℂ).hasFDerivAt).fderiv

/-- The actual tube derivative has exactly the plane derivative's operator norm, using the isometric zero-tangential-coordinate injection. -/
theorem norm_fderiv_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (x : Space) :
    ‖fderiv ℝ (profile ε) x‖ = ‖fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) x.snd‖ := by
  rw [fderiv_profile h0 h1]
  let A := fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) x.snd
  apply le_antisymm
  · apply (A.comp (WithLp.sndL 2 ℝ ℂ ℂ)).opNorm_le_bound (norm_nonneg A)
    intro y
    exact (A.le_opNorm y.snd).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le ℂ y) (norm_nonneg A))
  · apply A.opNorm_le_bound (norm_nonneg _)
    intro z
    simpa using (A.comp (WithLp.sndL 2 ℝ ℂ ℂ)).le_opNorm
      (WithLp.toLp 2 ((0 : ℂ), z))

/-- The actual tube derivative is supported in the closed normal annulus ε² ≤ radius ≤ ε; no tangential compactness is asserted. -/
theorem support_fderiv_subset {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Function.support (fderiv ℝ (profile ε)) ⊆
      {x : Space | ε ^ 2 ≤ ‖x.snd‖ ∧ ‖x.snd‖ ≤ ε} := by
  intro x hx
  apply SmoothNormalPlaneCutoff.support_fderiv_subset h0 h1
  intro hz
  apply hx
  rw [fderiv_profile h0 h1, hz, ContinuousLinearMap.zero_comp]

/-- Away from the actual flat axis, the cutoff is eventually exactly one as the parameter tends to zero through positive values. -/
theorem eventually_profile_eq_one {x : Space} (hx : x.snd ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), profile ε x = 1 :=
  SmoothNormalPlaneCutoff.eventually_profile_eq_one hx

/-- One fixed nonnegative constant bounds the actual tube derivative by C divided by normal radius times |log ε| for every admissible ε. -/
theorem exists_uniform_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ x : Space, x.snd ≠ 0 →
      ‖fderiv ℝ (profile ε) x‖ ≤ C / (‖x.snd‖ * |Real.log ε|) := by
  obtain ⟨C, hC, hb⟩ := SmoothNormalPlaneCutoff.exists_uniform_fderiv_bound
  refine ⟨C, hC, ?_⟩
  intro ε h0 h1 x hx
  rw [norm_fderiv_profile h0 h1]
  exact hb ε h0 h1 x.snd hx

end FoliationQM.SmoothProductTubeCutoff
