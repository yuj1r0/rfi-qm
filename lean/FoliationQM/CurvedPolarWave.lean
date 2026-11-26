module

public import FoliationQM.CurvedWaveDivergence
public import FoliationQM.CurvedGradientCovariance

/-!
# The actual curved wave operator on a polar field

The amplitude-phase identity follows by differentiating the genuine
volume-weighted metric flux. Every inverse-metric entry and every
derivative of its volume-weighted coefficient is retained. Symmetry of
the metric combines the two mixed amplitude-phase contractions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPolarWave

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCVolumeDensity CurvedWaveDivergence
  CurvedGradientCovariance PolarSecondDifferential MasterMetricAndCone
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {g : Covector → Mat4} {R Φ S : Covector → ℝ} {x : Covector}

/-- A locally C² amplitude and phase give a locally C² complex polar field. -/
theorem contDiffAt_amplitudeField (hR : ContDiffAt ℝ 2 R x) (hΦ : ContDiffAt ℝ 2 Φ x) :
    ContDiffAt ℝ 2 (amplitudeField R Φ) x := by
  have hRc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hR
  have hΦc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hΦ
  exact hRc.mul ((hΦc.mul (contDiffAt_const (c := Complex.I))).cexp)

/-- The actual polar flux contains both the amplitude flux and the phase flux. -/
theorem flux_amplitudeField (hR : DifferentiableAt ℝ R x) (hΦ : DifferentiableAt ℝ Φ x)
    (i : Fin 4) :
    flux g (amplitudeField R Φ) x i = phase (Φ x) *
      (((flux g R x i : ℝ) : ℂ) + Complex.I * (R x : ℂ) * ((flux g Φ x i : ℝ) : ℂ)) := by
  have hd (j : Fin 4) := directionalDerivative_amplitudeField hR hΦ (axis j)
  simp only [directionalDerivative, amplitudeTangent] at hd
  simp only [flux, hd, smul_eq_mul, Complex.real_smul, Complex.ofReal_sum, Complex.ofReal_mul,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Contracting a real differential with another field's actual flux recovers the full inverse-metric pairing. -/
theorem pairing_flux (hμ : volumeFactor (g x) ≠ 0) (f k : Covector → ℝ) :
    (volumeFactor (g x))⁻¹ * ∑ i, fderiv ℝ f x (axis i) * flux g k x i = pairing g f k x := by
  simp only [flux, coefficient, smul_eq_mul, pairing, RNCHalfDensityJet.form_apply, components,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- Symmetry of the inverse metric makes the actual scalar gradient pairing symmetric. -/
theorem pairing_symm (hs : (g x).IsSymm) (f k : Covector → ℝ) :
    pairing g f k x = pairing g k f x := by
  simp only [pairing, RNCHalfDensityJet.form_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs.inv.apply]
  ring

/-- Differentiating the actual polar flux keeps its amplitude, phase, and coefficient derivatives. -/
theorem fderiv_flux_amplitudeField (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : ContDiffAt ℝ 2 R x) (hΦ : ContDiffAt ℝ 2 Φ x) (i : Fin 4) (v : Covector) :
    fderiv ℝ (fun y => flux g (amplitudeField R Φ) y i) x v = phase (Φ x) *
      (((fderiv ℝ (fun y => flux g R y i) x v -
        fderiv ℝ Φ x v * R x * flux g Φ x i : ℝ) : ℂ) + Complex.I *
        ((fderiv ℝ Φ x v * flux g R x i + fderiv ℝ R x v * flux g Φ x i +
          R x * fderiv ℝ (fun y => flux g Φ y i) x v : ℝ) : ℂ)) := by
  have heq : (fun y => flux g (amplitudeField R Φ) y i) =ᶠ[𝓝 x] fun y =>
      phase (Φ y) * (((flux g R y i : ℝ) : ℂ) + Complex.I * (R y : ℂ) * ((flux g Φ y i : ℝ) : ℂ)) := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hR,
      PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hΦ] with y hyR hyΦ
    exact flux_amplitudeField hyR hyΦ i
  have hRc := Complex.ofRealCLM.hasFDerivAt.comp x (hR.differentiableAt (by decide)).hasFDerivAt
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x (hΦ.differentiableAt (by decide)).hasFDerivAt
  have hFr := hasFDerivAt_flux (coefficient_differentiable hg hd) hR i
  have hFφ := hasFDerivAt_flux (coefficient_differentiable hg hd) hΦ i
  have hFr' := Complex.ofRealCLM.hasFDerivAt.comp x hFr
  have hFφ' := Complex.ofRealCLM.hasFDerivAt.comp x hFφ
  have hp := (hΦc.mul_const Complex.I).cexp
  have hz : HasFDerivAt (fun y => phase (Φ y) *
      (((flux g R y i : ℝ) : ℂ) + Complex.I * (R y : ℂ) * ((flux g Φ y i : ℝ) : ℂ))) _ x :=
    hp.fun_mul (hFr'.fun_add ((hRc.const_mul Complex.I).fun_mul hFφ'))
  rw [heq.fderiv_eq, hz.fderiv, hFr.fderiv, hFφ.fderiv]
  simp only [phase, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Function.comp_apply, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The genuine curved divergence-form wave of an amplitude-phase field, including every metric coefficient derivative. -/
theorem wave_amplitudeField (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x) (hΦ : ContDiffAt ℝ 2 Φ x) :
    wave g (amplitudeField R Φ) x = phase (Φ x) *
      (((wave g R x - R x * pairing g Φ Φ x : ℝ) : ℂ) + Complex.I *
        ((2 * pairing g R Φ x + R x * wave g Φ x : ℝ) : ℂ)) := by
  have hμ : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hd)).ne'
  have hsum : (∑ i, fderiv ℝ (fun y => flux g (amplitudeField R Φ) y i) x (axis i)) =
      phase (Φ x) *
        (((∑ i, fderiv ℝ (fun y => flux g R y i) x (axis i)) -
          R x * ∑ i, fderiv ℝ Φ x (axis i) * flux g Φ x i : ℝ) : ℂ) +
      phase (Φ x) * Complex.I *
        (((∑ i, fderiv ℝ Φ x (axis i) * flux g R x i) +
          (∑ i, fderiv ℝ R x (axis i) * flux g Φ x i) +
          R x * ∑ i, fderiv ℝ (fun y => flux g Φ y i) x (axis i) : ℝ) : ℂ) := by
    simp only [fderiv_flux_amplitudeField hg hd hR hΦ, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sum, mul_add, mul_sub, Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 2
    all_goals first
      | apply Finset.sum_congr rfl; intro i _; ring
      | simp only [mul_assoc]
  have hcross : (∑ i, fderiv ℝ Φ x (axis i) * flux g R x i) =
      ∑ i, fderiv ℝ R x (axis i) * flux g Φ x i := by
    apply mul_left_cancel₀ (inv_ne_zero hμ)
    rw [pairing_flux hμ Φ R, pairing_flux hμ R Φ, pairing_symm hs Φ R]
  rw [wave, hsum, hcross]
  rw [← pairing_flux hμ Φ Φ, ← pairing_flux hμ R Φ]
  simp only [wave, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

/-- Constant real phase scaling commutes with the genuine curved wave operator. -/
theorem wave_div_const (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hS : ContDiffAt ℝ 2 S x) (c : ℝ) :
    wave g (fun y => S y / c) x = wave g S x / c := by
  have he := wave_clm (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) hg hd hS
  simpa only [smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Function.comp_def, div_eq_mul_inv, mul_comm] using he

/-- The curved polar wave identity with the physical phase S/ℏ and full inverse-metric contractions. -/
theorem wave_actionField (p : MassiveParameters) (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) :
    wave g (Madelung.actionField p R S) x = phase (S x / p.hbar) *
      (((wave g R x - R x * pairing g S S x / p.hbar ^ 2 : ℝ) : ℂ) + Complex.I *
        (((2 * pairing g R S x + R x * wave g S x) / p.hbar : ℝ) : ℂ)) := by
  have hc : components (fun y => S y / p.hbar) x = p.hbar⁻¹ • components S x := by
    funext i
    change directionalDerivative (fun y => S y / p.hbar) (axis i) x =
      p.hbar⁻¹ * directionalDerivative S (axis i) x
    rw [directionalDerivative_div_const (hS.differentiableAt (by decide))]
    ring
  have hp₁ : pairing g R (fun y => S y / p.hbar) x = p.hbar⁻¹ * pairing g R S x := by
    simp only [pairing, hc, map_smul, smul_eq_mul]
  have hp₂ : pairing g (fun y => S y / p.hbar) (fun y => S y / p.hbar) x =
      p.hbar⁻¹ * (p.hbar⁻¹ * pairing g S S x) := by
    simp only [pairing, hc, map_smul, smul_apply, smul_eq_mul]
  rw [Madelung.actionField, wave_amplitudeField hg hd hs hR (hS.div_const p.hbar), hp₁, hp₂,
    wave_div_const hg hd hS]
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

end FoliationQM.CurvedPolarWave
