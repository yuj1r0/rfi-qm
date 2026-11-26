module

public import FoliationQM.JointL2Curry
public import FoliationQM.DominatedFiberDerivative
public import FoliationQM.ScalarFiberPairing
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiating L² fibers by dominated convergence

An L² bound on first partial derivatives near a retained position suffices.
Dominated convergence is applied to squared normalized scalar remainders,
so the rate of convergence may depend on the remote spatial coordinate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DominatedFiberLimit

open Filter MeasureTheory LorentzCoordinates JointL2Sections
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Almost-everywhere scalar differentiability and an L² envelope on the normalized
remainders imply differentiability of the genuine L² fiber at the retained point. -/
theorem hasFDerivAt_of_dominated {F : X → Remote} {f : X → Spatial → ℂ}
    {D : X →L[ℝ] Remote} {d : Spatial → X →L[ℝ] ℂ} {x : X} {b : Spatial → ℝ}
    (hF : ∀ z, (F z : Spatial → ℂ) =ᵐ[volume] f z)
    (hD : ∀ v, (D v : Spatial → ℂ) =ᵐ[volume] fun y => d y v)
    (hd : ∀ᵐ y, HasFDerivAt (fun u => f u y) (d y) x)
    (hb : MemLp b 2 volume)
    (hbound : ∀ᶠ z in 𝓝 x, ∀ᵐ y, ‖z - x‖⁻¹ * ‖f z y - f x y - d y (z - x)‖ ≤ ‖b y‖) :
    HasFDerivAt F D x := by
  let E (z : X) : Remote := F z - F x - D (z - x)
  let q (z : X) (y : Spatial) := ‖z - x‖⁻¹ * ‖f z y - f x y - d y (z - x)‖
  have hrep (z : X) : (E z : Spatial → ℂ) =ᵐ[volume] fun y => f z y - f x y - d y (z - x) := by
    filter_upwards [Lp.coeFn_sub (F z - F x) (D (z-x)), Lp.coeFn_sub (F z) (F x),
      hF z, hF x, hD (z-x)] with y h₁ h₂ h₃ h₄ h₅
    change (F z - F x - D (z-x)) y = _
    simp only [h₁, Pi.sub_apply, h₂, h₃, h₄, h₅]
  have step (z : X) : (fun y => (‖z - x‖⁻¹ * ‖E z y‖)^2) =ᵐ[volume] fun y => (q z y)^2 :=
    (hrep z).mono fun y he => by simp only [q, he]
  have hmeas (z : X) : AEStronglyMeasurable (fun y => (q z y)^2) volume :=
    ((aestronglyMeasurable_const.mul (Lp.aestronglyMeasurable (E z)).norm).pow 2).congr (step z)
  have hconv : Tendsto (fun z => ∫ y, (q z y)^2) (𝓝 x) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure Spatial))
      (F := fun z y => (q z y)^2) (f := fun _ => (0 : ℝ)) (fun y => ‖b y‖^2)
      (.of_forall hmeas) (hbound.mono fun z hz => hz.mono fun y hy => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hy 2)
      hb.norm.integrable_sq (hd.mono fun y hy => by
        simpa [q] using (hasFDerivAt_iff_tendsto.mp hy).pow 2)
    simpa using h
  apply hasFDerivAt_iff_tendsto.mpr
  have hn (z : X) : (‖z-x‖⁻¹ * ‖E z‖)^2 = ∫ y, (q z y)^2 := by
    rw [mul_pow, JointL2Curry.norm_sq_integral (E z), ← integral_const_mul]
    exact integral_congr_ae ((step z).mono fun y h => (mul_pow _ _ 2).symm.trans h)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ← hn, Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (norm_nonneg _)), Real.sqrt_zero, E] using hs

/-- A locally uniform bound on the scalar first derivative provides the L²
remainder envelope on a convex ball by the mean value inequality. -/
theorem hasFDerivAt_of_derivative_bound {F : X → Remote} {f : X → Spatial → ℂ}
    {D : X →L[ℝ] Remote} {d : Spatial → X →L[ℝ] ℂ} {x : X} {b : Spatial → ℝ}
    {r : ℝ} (hr : 0 < r) (hF : ∀ z, (F z : Spatial → ℂ) =ᵐ[volume] f z)
    (hD : ∀ v, (D v : Spatial → ℂ) =ᵐ[volume] fun y => d y v)
    (hd : ∀ᵐ y, HasFDerivAt (fun u => f u y) (d y) x) (hb : MemLp b 2 volume)
    (hs : ∀ᵐ y, ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ (fun u => f u y) z ∧
      ‖fderiv ℝ (fun u => f u y) z‖ ≤ ‖b y‖) : HasFDerivAt F D x := by
  apply hasFDerivAt_of_dominated hF hD hd (hb.add hb)
  filter_upwards [Metric.ball_mem_nhds x hr] with z hz
  filter_upwards [hd, hs] with y hdy hy
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hv := (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hy u hu).1) (fun u hu => (hy u hu).2) hx hz
  have hdv : ‖d y (z-x)‖ ≤ ‖b y‖ * ‖z-x‖ :=
    ((d y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hdy.fderiv ▸ (hy x hx).2) (norm_nonneg _))
  have he := (norm_sub_le (f z y - f x y) (d y (z-x))).trans (add_le_add hv hdv)
  change _ ≤ ‖b y + b y‖
  rw [← two_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  by_cases hzero : z = x
  · simp [hzero]
  · have hpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    linarith

/-- A square-integrable field of scalar first derivatives and a local first-derivative
bound identify the actual Hilbert current with its scalar integral. -/
theorem current_of_derivative_bound (hbar m : ℝ) (f : X → Spatial → ℂ)
    (hf : ∀ z, MemLp (f z) 2 volume) {x : X} (v : X) (d : Spatial → X →L[ℝ] ℂ)
    (hd : MemLp d 2 volume) (hscalar : ∀ᵐ y, HasFDerivAt (fun u => f u y) (d y) x)
    {r : ℝ} (hr : 0 < r) {b : Spatial → ℝ} (hb : MemLp b 2 volume)
    (hs : ∀ᵐ y, ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ (fun u => f u y) z ∧
      ‖fderiv ℝ (fun u => f u y) z‖ ≤ ‖b y‖) :
    HilbertFiberObservables.current hbar m (DominatedFiberDerivative.fiber f hf) x v =
      (hbar / m) * ∫ y, (star (f x y) * fderiv ℝ (fun u => f u y) x v).im := by
  let D := DominatedFiberDerivative.differential d hd
  have hrep := DominatedFiberDerivative.differential_coe d hd v
  have hL : HasFDerivAt (DominatedFiberDerivative.fiber f hf) D x :=
    hasFDerivAt_of_derivative_bound hr (fun z => (hf z).coeFn_toLp)
      (DominatedFiberDerivative.differential_coe d hd) hscalar hb hs
  have hv := (Lp.memLp (D v)).ae_eq hrep
  rw [ScalarFiberPairing.current_eq_integral hbar m _ x v (hf x) hv rfl (by
    rw [hL.fderiv]
    exact Lp.ext (hrep.trans hv.coeFn_toLp.symm))]
  apply congrArg (fun a : ℝ => (hbar / m) * a)
  exact integral_congr_ae (hscalar.mono fun y hy => by simp only [hy.fderiv])

end FoliationQM.DominatedFiberLimit
