module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

/-!
# A cubic normal-coordinate remainder has zero two-jet

The estimate in the normal-coordinate expansion in v13 Lemma 9.1 determines
the derivatives at the base point. Along each real line Taylor's theorem singles
out the quadratic coefficient. Symmetry and polarization then determine the
mixed entries of the Fréchet Hessian. Conversely, for a locally C³ field,
vanishing of the two-jet gives a uniform cubic bound.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCQuadraticRemainder

open Asymptotics Filter Set Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

/-- A cubic norm estimate at the origin forces the value and first derivative to vanish. -/
theorem value_fderiv_of_isBigO_cubic (h : f =O[𝓝 0] fun y : E => ‖y‖ ^ 3) :
    f 0 = 0 ∧ HasFDerivAt f (0 : E →L[ℝ] ℝ) 0 := by
  have hz : f 0 = 0 := mem_of_mem_nhds h.eq_zero_imp (by simp)
  refine ⟨hz, ?_⟩
  simpa [hasFDerivAt_iff_isLittleO, hz] using
    h.trans_isLittleO (isLittleO_norm_pow_id (by decide : 1 < 3))

/-- A quadratic monomial which is little-o of the square has zero coefficient. -/
private theorem coefficient_eq_zero {c : ℝ}
    (hc : (fun t : ℝ => c * t ^ 2) =o[𝓝 0] fun t => t ^ 2) : c = 0 := by
  by_contra h
  have hs := (isLittleO_const_mul_left_iff h).mp hc
  have hn : ∃ᶠ t : ℝ in 𝓝 0, t ^ 2 ≠ 0 :=
    (frequently_lt_nhds (0 : ℝ)).mono fun _ ht => pow_ne_zero 2 ht.ne
  exact isLittleO_irrefl hn hs

/-- Taylor's formula on radial lines identifies the repeated-direction Hessian. -/
theorem hessian_diagonal_of_isBigO_cubic (hf : ContDiffAt ℝ 2 f 0)
    (h : f =O[𝓝 0] fun y : E => ‖y‖ ^ 3) (v : E) :
    fderiv ℝ (fderiv ℝ f) 0 v v = 0 := by
  obtain ⟨hz, hd⟩ := value_fderiv_of_isBigO_cubic h
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hL (t : ℝ) : L t = t • v := rfl
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  let b := ball (0 : E) r
  have hfb : ContDiffOn ℝ 2 f b := hfu.mono hru
  let s := L ⁻¹' b
  have hs : IsOpen s := isOpen_ball.preimage L.continuous
  have hzero : (0 : ℝ) ∈ s := by simpa [s, b] using hr
  have hconv : Convex ℝ s := (convex_ball (0 : E) r).linear_preimage L.toLinearMap
  have ht := taylor_isLittleO hconv hzero (hfb.comp_continuousLinearMap L)
  rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hzero)] at ht
  have hj (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k (f ∘ L) s 0 = iteratedFDeriv ℝ k f 0 (fun _ => v) := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      L.iteratedFDerivWithin_comp_right hfb isOpen_ball.uniqueDiffOn hs.uniqueDiffOn
        (show L 0 ∈ b from hzero) (mod_cast hk),
      iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ball.uniqueDiffOn
        (by simpa using hf.of_le (show (k : ℕ∞ω) ≤ 2 by exact_mod_cast hk))
        (show L 0 ∈ b from hzero)]
    simp [hL, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hp (t : ℝ) : taylorWithinEval (f ∘ L) 2 s 0 t =
      (fderiv ℝ (fderiv ℝ f) 0 v v / 2) * t ^ 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ, taylorWithinEval_succ,
      taylor_within_zero_eval, hj 1 (by decide), hj 2 le_rfl]
    simp [hz, hd.fderiv, iteratedFDeriv_two_apply]
    ring
  have hl : (f ∘ L) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 3 := by
    have hb := h.comp_tendsto (show Tendsto L (𝓝 0) (𝓝 0) by simpa using L.continuous.tendsto 0)
    refine hb.trans ?_
    change (fun t : ℝ => ‖L t‖ ^ 3) =O[𝓝 0] fun t => ‖t‖ ^ 3
    simp only [hL, norm_smul, mul_pow]
    exact (isBigO_const_mul_self (‖v‖ ^ 3) (fun t : ℝ => ‖t‖ ^ 3) (𝓝 0)).congr_left
      fun _ => mul_comm _ _
  have hl' : (f ∘ L) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    apply hl.trans_isLittleO
    simpa [← Real.norm_eq_abs, ← norm_pow, isLittleO_norm_left] using
      (isLittleO_pow_pow (𝕜 := ℝ) (by decide : 2 < 3))
  have hp' : (fun t : ℝ => (fderiv ℝ (fderiv ℝ f) 0 v v / 2) * t ^ 2) =o[𝓝 0]
      fun t => t ^ 2 := by
    simp only [hp, sub_zero] at ht
    simpa only [Pi.sub_apply, sub_sub_cancel] using hl'.sub ht
  linarith [coefficient_eq_zero hp']

/-- A locally twice continuously differentiable cubic remainder has zero value,
first derivative, and full bilinear Hessian at the base point. -/
theorem zeroJet_of_isBigO_cubic (hf : ContDiffAt ℝ 2 f 0)
    (h : f =O[𝓝 0] fun y : E => ‖y‖ ^ 3) :
    f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧ fderiv ℝ (fderiv ℝ f) 0 = 0 := by
  obtain ⟨hz, hd⟩ := value_fderiv_of_isBigO_cubic h
  refine ⟨hz, hd.fderiv, ?_⟩
  ext u v
  have hp := hessian_diagonal_of_isBigO_cubic hf h (u + v)
  simp only [map_add, add_apply] at hp
  have hsym := hf.isSymmSndFDerivAt (by simp) u v
  simp only [zero_apply]
  linarith [hessian_diagonal_of_isBigO_cubic hf h u,
    hessian_diagonal_of_isBigO_cubic hf h v]

/-- A derivative bounded to order `k` gives a remainder bounded to order `k+1`
by the mean-value inequality on shrinking closed balls. -/
private theorem isBigO_succ_of_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {k : ℕ} (hz : g 0 = 0)
    (hd : ∀ᶠ y in 𝓝 0, DifferentiableAt ℝ g y)
    (hb : (fderiv ℝ g) =O[𝓝 0] fun y : E => ‖y‖ ^ k) :
    g =O[𝓝 0] fun y : E => ‖y‖ ^ (k + 1) := by
  obtain ⟨C, hC, hc⟩ := hb.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hd.and hc.bound)
  apply IsBigO.of_bound C
  filter_upwards [ball_mem_nhds (0 : E) hr] with x hx
  have hlocal {y : E} (hy : y ∈ closedBall (0 : E) ‖x‖) :=
    hball (show y ∈ ball 0 r by
      rw [mem_ball, dist_zero_right] at hx ⊢
      rw [mem_closedBall, dist_zero_right] at hy
      exact hy.trans_lt hx)
  have hbound (y : E) (hy : y ∈ closedBall (0 : E) ‖x‖) :
      ‖fderiv ℝ g y‖ ≤ C * ‖x‖ ^ k := by
    have hyx : ‖y‖ ≤ ‖x‖ := by simpa [mem_closedBall] using hy
    exact (by simpa using (hlocal hy).2 : ‖fderiv ℝ g y‖ ≤ C * ‖y‖ ^ k).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyx _) hC)
  have hmv := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hlocal hy).1) hbound (mem_closedBall_self (norm_nonneg x))
    (show x ∈ closedBall 0 ‖x‖ by simp [mem_closedBall])
  simpa [hz, pow_succ, mul_assoc] using hmv

/-- A locally three times continuously differentiable field with vanishing
two-jet satisfies a uniform cubic norm bound in a neighborhood of the origin. -/
theorem isBigO_cubic_of_zeroJet (hf : ContDiffAt ℝ 3 f 0) (hz : f 0 = 0)
    (hd : fderiv ℝ f 0 = 0) (hh : fderiv ℝ (fderiv ℝ f) 0 = 0) :
    f =O[𝓝 0] fun y : E => ‖y‖ ^ 3 := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ f) 0 := hf.fderiv_right (by decide)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) 0 := h1.fderiv_right (by decide)
  have hb : (fderiv ℝ (fderiv ℝ f)) =O[𝓝 0] fun y : E => ‖y‖ ^ 1 := by
    simpa only [sub_zero, hh, pow_one] using (h2.differentiableAt (by decide)).isBigO_sub.norm_right
  refine isBigO_succ_of_fderiv (k := 2) hz
    ((hf.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by decide)) ?_
  exact isBigO_succ_of_fderiv (k := 1) hd
    ((h1.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by decide)) hb

end FoliationQM.RNCQuadraticRemainder
