module

public import FoliationQM.RNCScalarWaveCenter

/-!
# Divergence-form wave operator in a general metric chart

The volume-weighted inverse metric multiplies the actual differential of a
field with values in a real normed space. Differentiating this flux produces
the Hessian contraction and a first-order coefficient involving the
derivative of the volume-weighted inverse metric. The same operator acts on
complex-valued fields by real scalar multiplication.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedWaveDivergence

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCVolumeDensity
open scoped Matrix.Norms.Operator Topology BigOperators
set_option backward.isDefEq.respectTransparency false

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The coordinate volume times an inverse-metric coefficient. -/
def coefficient (g : Covector → Mat4) (x : Covector) (i j : Fin 4) : ℝ :=
  volumeFactor (g x) * (g x)⁻¹ i j

/-- The flux obtained by multiplying the actual differential by the volume-weighted inverse metric. -/
def flux (g : Covector → Mat4) (f : Covector → F) (x : Covector) (i : Fin 4) : F :=
  ∑ j, coefficient g x i j • fderiv ℝ f x (axis j)

/-- The wave operator is coordinate flux divergence divided by the metric volume. -/
def wave (g : Covector → Mat4) (f : Covector → F) (x : Covector) : F :=
  (volumeFactor (g x))⁻¹ • ∑ i, fderiv ℝ (fun y => flux g f y i) x (axis i)

/-- The first-order coefficient left by differentiating the volume-weighted inverse metric. -/
def drift (g : Covector → Mat4) (x : Covector) (j : Fin 4) : ℝ :=
  (volumeFactor (g x))⁻¹ * ∑ i, fderiv ℝ (fun y => coefficient g y i j) x (axis i)

variable {g : Covector → Mat4} {x : Covector} {f : Covector → F}

/-- The real specialization agrees with the existing scalar divergence-form operator. -/
theorem wave_real (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) :
    wave g f x = RNCScalarWaveCenter.wave g f x := by
  simp only [wave, flux, coefficient, smul_eq_mul, RNCScalarWaveCenter.wave,
    RNCScalarWaveCenter.flux, RNCScalarWaveCenter.raisedGradient, Finset.mul_sum, mul_assoc]

/-- The divergence of the flux of a constant field vanishes. -/
theorem wave_const (g : Covector → Mat4) (c : F) (x : Covector) : wave g (fun _ => c) x = 0 := by
  simp [wave, flux]

/-- A negative determinant gives a positive volume and differentiable flux coefficients at a differentiable metric. -/
theorem coefficient_differentiable (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0)
    (i j : Fin 4) : DifferentiableAt ℝ (fun y => coefficient g y i j) x := by
  let L : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hu := (g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet.ne)
  have hi := (LorentzCayleySmooth.contDiffAt_inverse 1 hu).differentiableAt_one.comp x hg
  exact ((RNCMetricHalfDensity.volume_smooth hdet 1).differentiableAt_one.comp x hg).fun_mul
    (L.differentiableAt.comp x hi)

/-- Differentiating each flux component gives a coefficient times the differentiated gradient and a coefficient-derivative term. -/
theorem hasFDerivAt_flux
    (hc : ∀ i j, DifferentiableAt ℝ (fun y => coefficient g y i j) x)
    (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
    HasFDerivAt (fun y => flux g f y i)
      (∑ j, (coefficient g x i j •
        ((ContinuousLinearMap.apply ℝ F (axis j)).comp (fderiv ℝ (fderiv ℝ f) x)) +
        (fderiv ℝ (fun y => coefficient g y i j) x).smulRight (fderiv ℝ f x (axis j)))) x := by
  unfold flux
  apply HasFDerivAt.fun_sum
  intro j _
  have hd := (ContinuousLinearMap.apply ℝ F (axis j)).hasFDerivAt.comp x
    ((hf.fderiv_right (m := 1) (by decide)).differentiableAt_one.hasFDerivAt)
  exact (hc i j).hasFDerivAt.fun_smul hd

/-- Product expansion of the metric divergence wherever its coefficients are differentiable and the volume is nonzero. -/
theorem wave_expansion_of_coefficients (hμ : volumeFactor (g x) ≠ 0)
    (hc : ∀ i j, DifferentiableAt ℝ (fun y => coefficient g y i j) x)
    (hf : ContDiffAt ℝ 2 f x) :
    wave g f x = (∑ i, ∑ j, (g x)⁻¹ i j • fderiv ℝ (fderiv ℝ f) x (axis i) (axis j)) +
      ∑ j, drift g x j • fderiv ℝ f x (axis j) := by
  have hcancel (i j) : (volumeFactor (g x))⁻¹ * coefficient g x i j = (g x)⁻¹ i j := by
    rw [coefficient, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  have hd (i : Fin 4) := (hasFDerivAt_flux hc hf i).fderiv
  simp only [wave, hd, sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply,
    Finset.smul_sum, smul_add, ← mul_smul, hcancel, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [drift, Finset.mul_sum, Finset.sum_smul]

/-- A differentiable metric with negative determinant supplies the coefficients and nonzero volume for the expansion. -/
theorem wave_expansion (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0) (hf : ContDiffAt ℝ 2 f x) :
    wave g f x = (∑ i, ∑ j, (g x)⁻¹ i j • fderiv ℝ (fderiv ℝ f) x (axis i) (axis j)) +
      ∑ j, drift g x j • fderiv ℝ f x (axis j) :=
  wave_expansion_of_coefficients (Real.sqrt_pos.2 (neg_pos.mpr hdet)).ne'
    (coefficient_differentiable hg hdet) hf

/-- Continuous real-linear observables commute with the divergence-form operator, including both complex projections. -/
theorem wave_clm (L : F →L[ℝ] H) (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0)
    (hf : ContDiffAt ℝ 2 f x) : wave g (L ∘ f) x = L (wave g f x) := by
  have he (i) : (fun y => flux g (L ∘ f) y i) =ᶠ[𝓝 x] L ∘ (fun y => flux g f y i) := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf] with y hy
    simp [flux, fderiv_comp y L.differentiableAt hy]
  have hd (i) : fderiv ℝ (fun y => flux g (L ∘ f) y i) x (axis i) =
      L (fderiv ℝ (fun y => flux g f y i) x (axis i)) := by
    rw [(he i).fderiv_eq, fderiv_comp x L.differentiableAt
      (hasFDerivAt_flux (coefficient_differentiable hg hdet) hf i).differentiableAt,
      L.hasFDerivAt.fderiv]
    rfl
  simp only [wave, hd, map_smul, map_sum]

variable {ψ : Covector → ℂ}

/-- Complex multiplication by a constant commutes with the coordinate wave operator. -/
theorem wave_complex_mul (c : ℂ) (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0)
    (hψ : ContDiffAt ℝ 2 ψ x) : wave g (fun y => c * ψ y) x = c * wave g ψ x :=
  wave_clm (ContinuousLinearMap.mul ℝ ℂ c) hg hdet hψ

/-- Projecting a complex wave onto its real part gives the scalar wave of the real part. -/
theorem wave_re (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0) (hψ : ContDiffAt ℝ 2 ψ x) :
    RNCScalarWaveCenter.wave g (fun y => (ψ y).re) x = (wave g ψ x).re := by
  rw [← wave_real]
  exact wave_clm Complex.reCLM hg hdet hψ

/-- Projecting a complex wave onto its imaginary part gives the scalar wave of the imaginary part. -/
theorem wave_im (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0) (hψ : ContDiffAt ℝ 2 ψ x) :
    RNCScalarWaveCenter.wave g (fun y => (ψ y).im) x = (wave g ψ x).im := by
  rw [← wave_real]
  exact wave_clm Complex.imCLM hg hdet hψ

end FoliationQM.CurvedWaveDivergence
