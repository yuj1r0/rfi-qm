module

public import FoliationQM.JointL2Sections
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiating spatial fibers under an (L^2) remainder bound

The scalar Taylor remainder may have a different exceptional null set for
each retained displacement. Its common square-integrable envelope bounds
the Hilbert-space remainder. A locally Lipschitz scalar derivative supplies
the quadratic special case by the mean value inequality on a ball.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DominatedFiberDerivative

open LorentzCoordinates JointL2Sections MeasureTheory Filter Asymptotics
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The remote Hilbert-space class of a square-integrable scalar fiber. -/
def fiber (ψ : X → Spatial → ℂ) (hψ : ∀ z, MemLp (ψ z) 2 volume) (x : X) : Remote :=
  (hψ x).toLp (ψ x)

/-- An operator-norm-square-integrable field of scalar differentials defines
a bounded real-linear map from retained directions to remote wave classes. -/
def differential (d : Spatial → X →L[ℝ] ℂ) (hd : MemLp d 2 volume) : X →L[ℝ] Remote :=
  ((ContinuousLinearMap.apply ℝ ℂ).compLpL₂ 2 volume).flip (hd.toLp d)

/-- In every fixed direction the lifted differential represents scalar evaluation. -/
theorem differential_coe (d : Spatial → X →L[ℝ] ℂ) (hd : MemLp d 2 volume) (v : X) :
    (differential d hd v : Spatial → ℂ) =ᵐ[volume] fun y => d y v :=
  ((ContinuousLinearMap.apply ℝ ℂ v).coeFn_compLp' (hd.toLp d)).trans
    (hd.coeFn_toLp.fun_comp (fun f => f v))

/-- An almost-everywhere scalar Taylor estimate with an (L^2) envelope and a
little-o modulus implies genuine Fréchet differentiability in the remote Hilbert space. -/
theorem hasFDerivAt_of_remainder (ψ : X → Spatial → ℂ) (hψ : ∀ z, MemLp (ψ z) 2 volume)
    (x : X) (D : X →L[ℝ] Remote) (d : Spatial → X →L[ℝ] ℂ)
    (hD : ∀ v, (D v : Spatial → ℂ) =ᵐ[volume] fun y => d y v)
    (b : Spatial → ℝ) (hb : MemLp b 2 volume) (r : X → ℝ)
    (hr : r =o[𝓝 x] fun z => z - x)
    (hrem : ∀ᶠ z in 𝓝 x, ∀ᵐ y ∂volume,
      ‖ψ z y - ψ x y - d y (z - x)‖ ≤ ‖r z‖ * ‖b y‖) :
    HasFDerivAt (fiber ψ hψ) D x := by
  apply HasFDerivAt.of_isLittleO
  refine IsBigO.trans_isLittleO (g := r) (IsBigO.of_bound ‖hb.toLp b‖ ?_) hr
  filter_upwards [hrem] with z hz
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hsub := (Lp.coeFn_sub (fiber ψ hψ z - fiber ψ hψ x) (D (z - x))).trans
    (((Lp.coeFn_sub (fiber ψ hψ z) (fiber ψ hψ x)).trans
      ((hψ z).coeFn_toLp.sub (hψ x).coeFn_toLp)).sub (hD (z - x)))
  filter_upwards [hsub, hb.coeFn_toLp, hz] with y hy hyb h
  exact hy.symm ▸ hyb.symm ▸ h

/-- A uniform square-integrable bound times the squared displacement gives
a Fréchet derivative whose values are the lifted scalar differentials. -/
theorem hasFDerivAt_of_quadratic (ψ : X → Spatial → ℂ) (hψ : ∀ z, MemLp (ψ z) 2 volume)
    (x : X) (d : Spatial → X →L[ℝ] ℂ) (hd : MemLp d 2 volume)
    (b : Spatial → ℝ) (hb : MemLp b 2 volume)
    (hrem : ∀ᶠ z in 𝓝 x, ∀ᵐ y ∂volume,
      ‖ψ z y - ψ x y - d y (z - x)‖ ≤ ‖b y‖ * ‖z - x‖ ^ 2) :
    HasFDerivAt (fiber ψ hψ) (differential d hd) x := by
  apply hasFDerivAt_of_remainder ψ hψ x _ d (differential_coe d hd) b hb _
    (isLittleO_pow_sub_sub x one_lt_two)
  simpa [Real.norm_eq_abs, abs_of_nonneg, mul_comm] using hrem

/-- A square-integrably bounded local Lipschitz variation of the scalar
derivatives yields the actual remote-space derivative of the wave. -/
theorem hasFDerivAt_of_lipschitz_derivative (ψ : X → Spatial → ℂ)
    (hψ : ∀ z, MemLp (ψ z) 2 volume) (x : X) (R : ℝ) (hR : 0 < R)
    (d : X → Spatial → X →L[ℝ] ℂ) (hd : MemLp (d x) 2 volume)
    (b : Spatial → ℝ) (hb : MemLp b 2 volume)
    (hloc : ∀ᵐ y ∂volume, ∀ u ∈ Metric.ball x R,
      HasFDerivAt (fun w => ψ w y) (d u y) u ∧
      ‖d u y - d x y‖ ≤ ‖b y‖ * ‖u - x‖) :
    HasFDerivAt (fiber ψ hψ) (differential (d x) hd) x := by
  apply hasFDerivAt_of_quadratic ψ hψ x (d x) hd b hb
  filter_upwards [Metric.ball_mem_nhds x hR] with z hz
  filter_upwards [hloc] with y hy
  let s := Metric.closedBall x ‖z - x‖
  have hsub {u : X} (hu : u ∈ s) : u ∈ Metric.ball x R :=
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hu).trans_lt
      (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz))
  have hbound (u : X) (hu : u ∈ s) : ‖d u y - d x y‖ ≤ ‖b y‖ * ‖z - x‖ :=
    (hy u (hsub hu)).2.trans (mul_le_mul_of_nonneg_left
      (by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hu) (norm_nonneg _))
  have h := (convex_closedBall x ‖z - x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun u hu => (hy u (hsub hu)).1.hasFDerivWithinAt) hbound
    (Metric.mem_closedBall_self (norm_nonneg _))
    (show z ∈ s by simp [s, dist_eq_norm, Metric.mem_closedBall])
  simpa [pow_two, mul_assoc] using h

end FoliationQM.DominatedFiberDerivative
