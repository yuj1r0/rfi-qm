module

public import FoliationQM.CurvedGradientCovariance
public import FoliationQM.CurvedFluxGreen

/-!
# Coordinate covariance of the complex kinetic pairing and scalar action

The real and imaginary parts of the complex sesquilinear contraction in
v13 `eq:curved_KG_action_thm` are combinations of real differential
pairings. Each is invariant under a regular coordinate pullback. The
metric volume then gives equality of the integrated pairing and of the
real action including any pulled-back scalar potential.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedKineticCovariance

open LorentzMatrixGroup RNCCoordinateVolumeChange RNCVolumeDensity RNCCoordinateConnection
  CurvedGradientCovariance CurvedFluxGreen MeasureTheory

variable {u f : Covector → ℂ} {x : Covector}

private theorem component_clm (L : ℂ →L[ℝ] ℝ) (hf : DifferentiableAt ℝ f x) (j : Fin 4) :
    components (L ∘ f) x j = L (fderiv ℝ f x (axis j)) :=
  congrArg (fun T : Covector →L[ℝ] ℝ => T (axis j)) (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- Both components of the Hermitian kinetic pairing in terms of real scalar gradients. -/
theorem kinetic_parts (g : Covector → Mat4) (hu : DifferentiableAt ℝ u x)
    (hf : DifferentiableAt ℝ f x) :
    (kinetic g u f x).re =
        pairing g (Complex.reCLM ∘ u) (Complex.reCLM ∘ f) x +
        pairing g (Complex.imCLM ∘ u) (Complex.imCLM ∘ f) x ∧
    (kinetic g u f x).im =
        pairing g (Complex.reCLM ∘ u) (Complex.imCLM ∘ f) x -
        pairing g (Complex.imCLM ∘ u) (Complex.reCLM ∘ f) x := by
  constructor
  · change Complex.reCLM (∑ i, ∑ j, (g x)⁻¹ i j •
      (star (fderiv ℝ u x (axis i)) * fderiv ℝ f x (axis j))) = _
    simp only [map_sum, map_smul, Complex.reCLM_apply, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, pairing, RNCHalfDensityJet.form_apply,
      component_clm _ hu, component_clm _ hf, Complex.imCLM_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · change Complex.imCLM (∑ i, ∑ j, (g x)⁻¹ i j •
      (star (fderiv ℝ u x (axis i)) * fderiv ℝ f x (axis j))) = _
    simp only [map_sum, map_smul, Complex.imCLM_apply, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, pairing, RNCHalfDensityJet.form_apply,
      component_clm _ hu, component_clm _ hf, Complex.reCLM_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

variable {φ : Covector → Covector} {D : Covector → Covector →L[ℝ] Covector}

/-- The entire complex kinetic contraction, including its imaginary part for distinct fields,
is invariant under regular coordinate changes. -/
theorem kinetic_pullback (g : Covector → Mat4) (hφ : HasFDerivAt φ (D x) x)
    (hJ : IsUnit (jacobianMatrix (D x)).det) (hu : DifferentiableAt ℝ u (φ x))
    (hf : DifferentiableAt ℝ f (φ x)) :
    kinetic (pullMetric g φ D) (u ∘ φ) (f ∘ φ) x = kinetic g u f (φ x) := by
  have hp (L M : ℂ →L[ℝ] ℝ) :
      pairing (pullMetric g φ D) (L ∘ (u ∘ φ)) (M ∘ (f ∘ φ)) x =
        pairing g (L ∘ u) (M ∘ f) (φ x) :=
    pairing_pullback (φ := φ) (D := D) (x := x) (f := L ∘ u) (k := M ∘ f) g hφ hJ
      (L.differentiableAt.comp (φ x) hu) (M.differentiableAt.comp (φ x) hf)
  have h₁ := kinetic_parts (pullMetric g φ D) (hu.comp x hφ.differentiableAt) (hf.comp x hφ.differentiableAt)
  have h₂ := kinetic_parts g hu hf
  exact Complex.ext (by rw [h₁.1, h₂.1, hp, hp]) (by rw [h₁.2, h₂.2, hp, hp])

variable {s : Set Covector}

/-- The metric-volume integral of the full complex sesquilinear kinetic pairing is chart invariant. -/
theorem integral_kinetic_pullback (g : Covector → Mat4) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : Set.InjOn φ s)
    (hJ : ∀ x ∈ s, IsUnit (jacobianMatrix (D x)).det)
    (hu : ∀ x ∈ s, DifferentiableAt ℝ u (φ x)) (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x)) :
    (∫ y in φ '' s, volumeFactor (g y) • kinetic g u f y) =
      ∫ x in s, volumeFactor (pullMetric g φ D x) • kinetic (pullMetric g φ D) (u ∘ φ) (f ∘ φ) x := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  calc
    _ = volumeFactor (pullMetric g φ D x) • kinetic g u f (φ x) := by
      rw [volume_pullMetric, mul_smul]
    _ = _ := congrArg (fun t : ℂ => volumeFactor (pullMetric g φ D x) • t)
      (kinetic_pullback g (hφ x hx) (hJ x hx) (hu x hx) (hf x hx)).symm

/-- Real scalar action density, before multiplication by the metric volume. -/
def actionDensity (g : Covector → Mat4) (V : Covector → ℝ) (ℏ : ℝ) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  ℏ ^ 2 * (kinetic g ψ ψ x).re - V x * Complex.normSq (ψ x)

/-- The action density of a field and scalar potential pulls back by composition. -/
theorem actionDensity_pullback (g : Covector → Mat4) (V : Covector → ℝ) (ℏ : ℝ)
    (hφ : HasFDerivAt φ (D x) x) (hJ : IsUnit (jacobianMatrix (D x)).det)
    (hf : DifferentiableAt ℝ f (φ x)) :
    actionDensity (pullMetric g φ D) (V ∘ φ) ℏ (f ∘ φ) x = actionDensity g V ℏ f (φ x) := by
  rw [actionDensity, kinetic_pullback g hφ hJ hf hf]
  rfl

/-- The integral of the scalar action with metric volume is invariant when its potential is pulled back. -/
theorem integral_action_pullback (g : Covector → Mat4) (V : Covector → ℝ) (ℏ : ℝ)
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : Set.InjOn φ s)
    (hJ : ∀ x ∈ s, IsUnit (jacobianMatrix (D x)).det) (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x)) :
    (∫ y in φ '' s, volumeFactor (g y) * actionDensity g V ℏ f y) =
      ∫ x in s, volumeFactor (pullMetric g φ D x) * actionDensity (pullMetric g φ D) (V ∘ φ) ℏ (f ∘ φ) x := by
  rw [integral_pullMetric hs (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  exact congrArg (fun t : ℝ => volumeFactor (pullMetric g φ D x) * t)
    (actionDensity_pullback g V ℏ (hφ x hx) (hJ x hx) (hf x hx)).symm

end FoliationQM.CurvedKineticCovariance
