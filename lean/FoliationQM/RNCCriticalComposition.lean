module

public import FoliationQM.PolarRegularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Critical-point Hessians for the normal-coordinate determinant factors

The C² chain rule on normed spaces determines the Hessian of the volume
and half-density factors in v13 Lemma 9.1 from the determinant jet at
the origin. At a critical inner map only the first outer derivative
acts on its Hessian.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCCriticalComposition

open ContinuousLinearMap
open scoped Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {g : E → F} {f : F → G} {x : E}

/-- The bilinear Hessian chain rule on arbitrary test directions obtained by
differentiating the composition of the two Fréchet differential maps. -/
theorem hessian_comp (hg : ContDiffAt ℝ 2 g x) (hf : ContDiffAt ℝ 2 f (g x)) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x u v =
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x u v) +
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) := by
  have he : fderiv ℝ (f ∘ g) =ᶠ[𝓝 x] fun z => (fderiv ℝ f (g z)).comp (fderiv ℝ g z) := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hg,
      hg.continuousAt.eventually (PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf)]
      with z hz hfz
    exact fderiv_comp z hfz hz
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdfg := hdf.hasFDerivAt.comp x (hg.differentiableAt (by norm_num)).hasFDerivAt
  have h := (hdfg.clm_comp hdg.hasFDerivAt).congr_of_eventuallyEq he
  rw [h.fderiv]
  rfl

/-- A critical inner map gives a critical composite. -/
theorem gradient_comp_critical (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f (g x))
    (hz : fderiv ℝ g x = 0) : fderiv ℝ (f ∘ g) x = 0 := by
  rw [fderiv_comp x hf hg, hz, comp_zero]

/-- At a critical inner map the first outer derivative acts on the entire bilinear Hessian. -/
theorem hessian_comp_critical (hg : ContDiffAt ℝ 2 g x) (hf : ContDiffAt ℝ 2 f (g x))
    (hz : fderiv ℝ g x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x u v = fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  simp only [hessian_comp hg hf, hz, zero_apply, map_zero, add_zero]

variable {s : E → ℝ}

/-- A real power of a normalized critical scalar has vanishing differential. -/
theorem rpow_gradient_at_one (hs : ContDiffAt ℝ 2 s x) (hval : s x = 1)
    (hz : fderiv ℝ s x = 0) (q : ℝ) : fderiv ℝ (fun z => s z ^ q) x = 0 := by
  have hn : s x ≠ 0 := hval ▸ one_ne_zero
  exact gradient_comp_critical (hs.differentiableAt (by norm_num))
    (Real.hasDerivAt_rpow_const (p := q) (Or.inl hn)).differentiableAt hz

/-- At a normalized critical scalar the Hessian of its real power scales by the exponent. -/
theorem rpow_hessian_at_one (hs : ContDiffAt ℝ 2 s x) (hval : s x = 1)
    (hz : fderiv ℝ s x = 0) (q : ℝ) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun z => s z ^ q)) x u v = q * fderiv ℝ (fderiv ℝ s) x u v := by
  have hn : s x ≠ 0 := hval ▸ one_ne_zero
  change fderiv ℝ (fderiv ℝ ((fun t : ℝ => t ^ q) ∘ s)) x u v = _
  rw [hessian_comp_critical hs (Real.contDiffAt_rpow_const_of_ne hn) hz,
    (Real.hasDerivAt_rpow_const (p := q) (Or.inl hn)).hasFDerivAt.fderiv, hval]
  simp [mul_comm]

/-- The square root of a normalized critical scalar has vanishing differential. -/
theorem sqrt_gradient_at_one (hs : ContDiffAt ℝ 2 s x) (hval : s x = 1)
    (hz : fderiv ℝ s x = 0) : fderiv ℝ (fun z => √(s z)) x = 0 := by
  have hn : s x ≠ 0 := hval ▸ one_ne_zero
  exact gradient_comp_critical (hs.differentiableAt (by norm_num))
    (Real.hasDerivAt_sqrt hn).differentiableAt hz

/-- The square root of a normalized volume factor halves its Hessian at a critical point. -/
theorem sqrt_hessian_at_one (hs : ContDiffAt ℝ 2 s x) (hval : s x = 1)
    (hz : fderiv ℝ s x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun z => √(s z))) x u v = fderiv ℝ (fderiv ℝ s) x u v / 2 := by
  have hn : s x ≠ 0 := hval ▸ one_ne_zero
  change fderiv ℝ (fderiv ℝ (Real.sqrt ∘ s)) x u v = _
  rw [hessian_comp_critical hs (Real.contDiffAt_sqrt hn) hz, (Real.hasDerivAt_sqrt hn).hasFDerivAt.fderiv,
    hval]
  simp [div_eq_mul_inv]

/-- The fourth root of the normalized positive determinant scales its critical Hessian by one quarter. -/
theorem fourth_root_hessian_at_one (hs : ContDiffAt ℝ 2 s x) (hval : s x = 1)
    (hz : fderiv ℝ s x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun z => s z ^ (1/4 : ℝ))) x u v = fderiv ℝ (fderiv ℝ s) x u v / 4 := by
  rw [rpow_hessian_at_one hs hval hz]
  ring

end FoliationQM.RNCCriticalComposition
