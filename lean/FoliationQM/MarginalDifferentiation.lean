module

public import FoliationQM.TwoParticleMarginals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Differentiating the spatial marginal of a joint density

For v13 `prop:fisher_excess` and `eq:conditional_bayes`, the marginal is the Lebesgue integral
over the second particle's three spatial coordinates. A locally uniform
integrable envelope on the actual partial Fréchet derivative justifies
passing that derivative through the integral. The same envelope gives a
continuous derivative for the marginal of a jointly C¹ density.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MarginalDifferentiation

open MeasureTheory Filter LorentzCoordinates TwoParticleMarginals
open scoped Topology

/-- Partial Fréchet derivative in the first particle's three spatial coordinates. -/
def leftD (f : Spatial × Spatial → ℝ) (x y : Spatial) : Spatial →L[ℝ] ℝ :=
  fderiv ℝ (fun u => f (u,y)) x

/-- An integrable envelope for the operator norm of the first partial derivative,
uniform in the first variable near the chosen point almost everywhere in the second. -/
def DominatedAt (f : Spatial × Spatial → ℝ) (x : Spatial) : Prop :=
  ∃ s ∈ 𝓝 x, ∃ B : Spatial → ℝ, Integrable B ∧
    ∀ᵐ y, ∀ u ∈ s, ‖leftD f u y‖ ≤ B y

/-- Source density assumptions for two-particle marginal and conditional scores.
Both coordinate orders carry local derivative envelopes and finite fibers.
The joint mass is computed against six-dimensional Lebesgue volume. -/
structure Regular (f : Spatial × Spatial → ℝ) : Prop where
  smooth : ContDiff ℝ 1 f
  pos : ∀ z, 0 < f z
  integrable : Integrable f
  mass_one : ∫ z, f z = 1
  left_fiber : ∀ x, Integrable (fun y => f (x,y))
  right_fiber : ∀ y, Integrable (fun x => f (x,y))
  left_dom : ∀ x, DominatedAt f x
  right_dom : ∀ y, DominatedAt (TwoParticleMarginals.swap f) y

variable {f : Spatial × Spatial → ℝ}

/-- Exchanging particles preserves all density and derivative-envelope assumptions. -/
theorem Regular.swap (H : Regular f) : Regular (TwoParticleMarginals.swap f) where
  smooth := H.smooth.comp (contDiff_snd.prodMk contDiff_fst)
  pos z := H.pos z.swap
  integrable := H.integrable.swap
  mass_one := (integral_swap f).trans H.mass_one
  left_fiber := H.right_fiber
  right_fiber := H.left_fiber
  left_dom := H.right_dom
  right_dom := H.left_dom

/-- The first partial is the joint derivative composed with the inclusion v ↦ (v,0). -/
theorem leftD_eq_comp (hf : Differentiable ℝ f) (x y : Spatial) :
    leftD f x y = (fderiv ℝ f (x,y)).comp (ContinuousLinearMap.inl ℝ Spatial Spatial) :=
  ((hf (x,y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)).fderiv

/-- The operator-valued first partial of a jointly C¹ function is jointly continuous. -/
theorem continuous_leftD (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : Spatial × Spatial => leftD f z.1 z.2) := by
  simp_rw [leftD_eq_comp (hf.differentiable (by decide))]
  exact (hf.continuous_fderiv (by decide)).clm_comp continuous_const

private theorem leftD_measurable (hf : ContDiff ℝ 1 f) (x : Spatial) :
    AEStronglyMeasurable (leftD f x) volume :=
  ((continuous_leftD hf).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- A local operator-norm envelope implies genuine Bochner integrability of
the partial derivative on the selected fiber. -/
theorem integrable_leftD_at (hf : ContDiff ℝ 1 f) {x : Spatial} (hd : DominatedAt f x) :
    Integrable (leftD f x) := by
  obtain ⟨s, hs, B, hi, hB⟩ := hd
  exact hi.mono' (leftD_measurable hf x) (hB.mono fun _ hy => hy x (mem_of_mem_nhds hs))

/-- The local envelope and integrability of this one fiber suffice to differentiate
its marginal with the integral of the actual partial derivative as linear map. -/
theorem left_hasFDerivAt_of_dominated (hf : ContDiff ℝ 1 f) {x : Spatial}
    (hi : Integrable (fun y => f (x,y))) (hd : DominatedAt f x) :
    HasFDerivAt (left f) (∫ y, leftD f x y) x := by
  obtain ⟨s, hs, B, hB, hbound⟩ := hd
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun u y => f (u,y)) hs
    (Eventually.of_forall fun u =>
      (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hi (leftD_measurable hf x) hbound hB
  exact Eventually.of_forall fun y u _ =>
    ((hf.comp (contDiff_prodMk_left y)).differentiable (by decide) u).hasFDerivAt

/-- Derivative continuity at the parameter point follows by dominated convergence
for the integral of the first partial, with values in the continuous linear maps. -/
theorem continuousAt_integral_leftD (hf : ContDiff ℝ 1 f) {x : Spatial} (hd : DominatedAt f x) :
    ContinuousAt (fun u => ∫ y, leftD f u y) x := by
  obtain ⟨s, hs, B, hi, hB⟩ := hd
  exact continuousAt_of_dominated (Eventually.of_forall (leftD_measurable hf))
    (Filter.mem_of_superset hs fun u hu => hB.mono fun _ hy => hy u hu) hi
    (Eventually.of_forall fun y =>
      ((continuous_leftD hf).comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- Each derivative fiber is integrable for a regular joint density. -/
theorem integrable_leftD (H : Regular f) (x : Spatial) : Integrable (leftD f x) :=
  integrable_leftD_at H.smooth (H.left_dom x)

/-- Evaluating the partial derivative in a fixed direction preserves fiber integrability. -/
theorem integrable_leftD_apply (H : Regular f) (x v : Spatial) :
    Integrable (fun y => leftD f x y v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp (integrable_leftD H x)

/-- The first marginal has derivative given by the fiber integral of the first partial. -/
theorem left_hasFDerivAt (H : Regular f) (x : Spatial) :
    HasFDerivAt (left f) (∫ y, leftD f x y) x :=
  left_hasFDerivAt_of_dominated H.smooth (H.left_fiber x) (H.left_dom x)

/-- In each direction the first marginal derivative is the integral of the
directional derivative in the first coordinate of the joint density. -/
theorem left_fderiv_apply (H : Regular f) (x v : Spatial) :
    fderiv ℝ (left f) x v = ∫ y, leftD f x y v := by
  rw [(left_hasFDerivAt H x).fderiv, ContinuousLinearMap.integral_apply (integrable_leftD H x)]

/-- All first derivatives of the first marginal are continuous under the local bounds. -/
theorem contDiff_left (H : Regular f) : ContDiff ℝ 1 (left f) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_, continuous_iff_continuousAt.mpr
    (fun x => continuousAt_integral_leftD H.smooth (H.left_dom x)), left_hasFDerivAt H⟩

/-- The second marginal is C¹ under the same symmetric hypotheses. -/
theorem contDiff_right (H : Regular f) : ContDiff ℝ 1 (right f) := by
  rw [← left_swap]
  exact contDiff_left H.swap

end FoliationQM.MarginalDifferentiation
