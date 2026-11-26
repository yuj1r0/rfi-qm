module

public import FoliationQM.TidalModulusVariation
public import FoliationQM.TidalCovariantDivergence
public import FoliationQM.CurvedKGTestResidual

/-!
# The Euler–Lagrange equation of the action with the tidal term

Source: v13 `eq:tidal_KG_eq` (Conjecture 9.7), "adding this to the variation
`-ħ² √(-g) (□_g + m²c²/ħ² - 𝓡/6) ψ` of `𝒜_g` and dividing by `-ħ² √(-g)`
yields" the corrected equation, component kinds B and C. On an open set `U`
with a twice continuously differentiable symmetric Lorentzian metric, let `ψ`
be twice continuously differentiable and non-vanishing, and let `B^{μν}` be a
continuously differentiable symmetric tensor field. The relative action is
the volume-weighted Klein–Gordon action density plus the tidal density
`κ √(-g) B^{μν} ∂_μ|ψ| ∂_ν|ψ|`, each minus its value at `ψ`. Along `ψ + t η`
with a twice continuously differentiable compactly supported `η` in `U`, it
is differentiable at `t = 0` with derivative

`-2 Re ∫_U √(-g) η̄ [ħ² P ψ + κ (ψ/|ψ|) ∇_μ(B^{μν} ∇_ν|ψ|)]`,

so it is stationary for every smooth compactly supported `η` exactly when

`P ψ + ħ²/(12m²c⁴) · (1/|ψ|) ∇_μ(B^{μν} ∇_ν|ψ|) · ψ = 0` on `U`.

Here `P = □_g + m²c²/ħ² - 𝓡/6` is the operator of this development and the
covariant divergence is in divergence form. The tensor `B^{μν}` and the
external velocity entering it are held fixed. Nothing here supports the
physical ansatz of the conjecture or extends through zeros of the field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalEulerLagrange

open MeasureTheory Set Matrix LorentzMatrixGroup RNCVolumeDensity RNCCoordinateConnection
open RealLorentzFrame TidalAmplitudeVariation TidalCoefficient TidalFieldEquation
open TidalModulusVariation TidalCovariantDivergence CurvedWaveDivergence CurvedPolarAction
open CurvedKGFirstVariation CurvedKGTestResidual CurvedWeakEquation
open scoped Topology ComplexConjugate ContDiff Matrix.Norms.Operator

variable {g Bup : Covector → Mat4} {ψ η : Covector → ℂ} {U : Set Covector} {x : Covector}

/-- The tidal vector field `B^{μν} ∂_ν |ψ|`. -/
def tidalVector (Bup : Covector → Mat4) (ψ : Covector → ℂ) (y : Covector) : Fin 4 → ℝ :=
  Bup y *ᵥ grad (fun z => ‖ψ z‖) y

/-- The tidal term of the Euler–Lagrange residual,
`κ (ψ/|ψ|) ∇_μ(B^{μν} ∇_ν |ψ|)`. -/
def tidalTerm (p : MassiveParameters) (g Bup : Covector → Mat4) (ψ : Covector → ℂ)
    (x : Covector) : ℂ :=
  ((kappa p * covariantDivergence g (tidalVector Bup ψ) x : ℝ) : ℂ) * (ψ x / (‖ψ x‖ : ℂ))

/-- The Euler–Lagrange residual of the action with the tidal term. -/
def tidalResidual (p : MassiveParameters) (g Bup : Covector → Mat4) (ψ : Covector → ℂ)
    (x : Covector) : ℂ :=
  residual p g ψ x + tidalTerm p g Bup ψ x

/-- The action with the tidal term along `ψ + t η`, relative to its value at
`ψ`. -/
def relativeAction (p : MassiveParameters) (g Bup : Covector → Mat4) (ψ η : Covector → ℂ)
    (U : Set Covector) (t : ℝ) : ℝ :=
  (∫ x in U, volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x)) +
    ∫ x, (tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖perturb ψ η t y‖) x -
      tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖ψ y‖) x)

/-- The volume-weighted tidal vector field is continuously differentiable. -/
theorem contDiffAt_weighted (hg : ContDiffAt ℝ 2 g x) (hd : (g x).det < 0)
    (hψ : ContDiffAt ℝ 2 ψ x) (hne : ψ x ≠ 0)
    (hB : ∀ i j, ContDiffAt ℝ 1 (fun y => Bup y i j) x) (j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => volumeFactor (g y) * tidalVector Bup ψ y j) x := by
  have hvol : ContDiffAt ℝ 1 (fun y => volumeFactor (g y)) x :=
    (RNCMetricHalfDensity.volume_smooth hd 1).comp x (hg.of_le (by norm_num))
  have hR : ContDiffAt ℝ 2 (fun z => ‖ψ z‖) x := hψ.norm ℝ hne
  have hf : (fun y => tidalVector Bup ψ y j) = fun y =>
      ∑ i, Bup y j i * fderiv ℝ (fun z => ‖ψ z‖) y (axis i) := by
    funext y
    simp [tidalVector, mulVec, dotProduct, grad]
  have hV : ContDiffAt ℝ 1 (fun y => tidalVector Bup ψ y j) x := by
    rw [hf]
    exact ContDiffAt.sum fun i _ => (hB j i).mul
      ((hR.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  exact hvol.mul hV

/-- The tidal term is continuous where the data are regular and the field
does not vanish. -/
theorem tidalTerm_continuousAt (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hψ : ContDiffAt ℝ 2 ψ x) (hne : ψ x ≠ 0)
    (hB : ∀ i j, ContDiffAt ℝ 1 (fun y => Bup y i j) x) :
    ContinuousAt (tidalTerm p g Bup ψ) x := by
  have hvol : ContinuousAt (fun y => volumeFactor (g y)) x :=
    volumeFactor_continuous.continuousAt.comp hg.continuousAt
  have hv0 : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr hd)).ne'
  have hsum : ContinuousAt (fun y => ∑ j,
      fderiv ℝ (fun z => volumeFactor (g z) * tidalVector Bup ψ z j) y (axis j)) x :=
    tendsto_finsetSum _ fun j _ =>
      (((contDiffAt_weighted hg hd hψ hne hB j).fderiv_right (m := 0)
        (by norm_num)).continuousAt.clm_apply continuousAt_const)
  have hD : ContinuousAt (covariantDivergence g (tidalVector Bup ψ)) x :=
    (hvol.inv₀ hv0).mul hsum
  have hphase : ContinuousAt (fun y => ψ y / (‖ψ y‖ : ℂ)) x :=
    hψ.continuousAt.div (Complex.continuous_ofReal.continuousAt.comp hψ.continuousAt.norm)
      (by exact_mod_cast norm_ne_zero_iff.mpr hne)
  exact (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul hD)).mul hphase

/-- The Klein–Gordon part of the relative action has first variation
`-2 Re ∫_U √(-g) η̄ ħ² P ψ`. -/
theorem hasDerivAt_kg_relative (p : MassiveParameters) (hU : IsOpen U)
    (hsym : ∀ x ∈ U, (g x).IsSymm) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x in U,
        volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x))
      (-2 * testIntegral U g η (residual p g ψ)) 0 := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hA : Integrable (fun x => volumeFactor (g x) * (cross p g η ψ x).re)
      (volume.restrict U) := integrable_cross_re p hη1 hc hs hg hd hψ
  have hC : Integrable (fun x => volumeFactor (g x) * (cross p g η η x).re)
      (volume.restrict U) :=
    integrable_cross_re p hη1 hc hs hg hd fun x _ => hη.contDiffAt
  have hfun : (fun t : ℝ => ∫ x in U,
      volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x)) =
      fun t : ℝ => t * (2 * ∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) +
        t ^ 2 * ∫ x in U, volumeFactor (g x) * (cross p g η η x).re := by
    funext t
    have h1 : (∫ x in U,
        volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x)) =
        ∫ x in U, (t * (2 * (volumeFactor (g x) * (cross p g η ψ x).re)) +
          t ^ 2 * (volumeFactor (g x) * (cross p g η η x).re)) := by
      refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
      rw [density_perturb p (hsym x hx) ((hψ x hx).differentiableAt (by norm_num))
        (hη.differentiable (by norm_num) x), ← cross_self_re p g η x]
      ring
    rw [h1, integral_add ((hA.const_mul 2).const_mul t) (hC.const_mul (t ^ 2)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hfun]
  have h := (hasDerivAt_mul_const
      (2 * ∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) (x := (0 : ℝ))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const
      (∫ x in U, volumeFactor (g x) * (cross p g η η x).re))
  refine h.congr_deriv ?_
  rw [integral_cross_re p hη1 hc hs hg hd hψ]
  simp

/-- The tidal part of the relative action has first variation
`-2 Re ∫_U √(-g) η̄ κ (ψ/|ψ|) ∇_μ(B^{μν} ∇_ν|ψ|)`. -/
theorem hasDerivAt_tidal_relative (p : MassiveParameters) (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hne : ∀ x ∈ U, ψ x ≠ 0)
    (hB : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => Bup y i j) x)
    (hBsym : ∀ x ∈ U, (Bup x).IsSymm)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x,
        (tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖perturb ψ η t y‖) x -
          tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖ψ y‖) x))
      (-2 * testIntegral U g η (tidalTerm p g Bup ψ)) 0 := by
  have hT : ∀ i j, ∀ x ∈ U,
      ContDiffAt ℝ 1 (fun y => coefficientField (kappa p) g Bup y i j) x := by
    intro i j x hx
    have hvol : ContDiffAt ℝ 1 (fun y => volumeFactor (g y)) x :=
      (RNCMetricHalfDensity.volume_smooth (hd x hx) 1).comp x ((hg x hx).of_le (by norm_num))
    have hf : (fun y => coefficientField (kappa p) g Bup y i j) =
        fun y => kappa p * volumeFactor (g y) * Bup y i j := by
      funext y
      simp [coefficientField, Matrix.smul_apply]
    rw [hf]
    exact (contDiffAt_const.mul hvol).mul (hB i j x hx)
  have h := first_variation_modulus
    (fun x hx => coefficientField_isSymm (κ := kappa p) (g := g) (hBsym x hx)) hT hψ hne hη hc hs
  have hfun : (fun t : ℝ => ∫ x,
      (tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖perturb ψ η t y‖) x -
        tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖ψ y‖) x)) =
      fun t : ℝ => ∫ x,
        (tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖ψ y + (t : ℂ) * η y‖) x -
          tidalDensity (coefficientField (kappa p) g Bup) (fun y => ‖ψ y‖) x) := by
    funext t
    simp only [perturb, Complex.real_smul]
  rw [hfun]
  refine h.congr_deriv ?_
  congr 1
  have hz : ∀ x, x ∉ U → (conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
      (tidalDivergence (coefficientField (kappa p) g Bup) (fun y => ‖ψ y‖) x : ℂ))).re = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hs h)]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  unfold testIntegral
  refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
  have hv0 : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr (hd x hx))).ne'
  have hE : tidalVector Bup ψ = fun y => Bup y *ᵥ grad (fun z => ‖ψ z‖) y := rfl
  have hdiv := tidalDivergence_coefficientField (κ := kappa p) (R := fun z => ‖ψ z‖) hv0
    (fun j => (contDiffAt_weighted (hg x hx) (hd x hx) (hψ x hx) (hne x hx)
      (fun i j => hB i j x hx) j).differentiableAt one_ne_zero)
  rw [← hE] at hdiv
  rw [hdiv, tidalTerm]
  have e : conj (η x) * (ψ x / (‖ψ x‖ : ℂ) *
      ((kappa p * volumeFactor (g x) * covariantDivergence g (tidalVector Bup ψ) x : ℝ) : ℂ)) =
      ((volumeFactor (g x) : ℝ) : ℂ) * (conj (η x) *
        (((kappa p * covariantDivergence g (tidalVector Bup ψ) x : ℝ) : ℂ) *
          (ψ x / (‖ψ x‖ : ℂ)))) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]

/-- The weighted test pairing is additive in the tested field. -/
theorem testIntegral_add {F₁ F₂ : Covector → ℂ}
    (h₁ : IntegrableOn (fun x => volumeFactor (g x) * (conj (η x) * F₁ x).re) U)
    (h₂ : IntegrableOn (fun x => volumeFactor (g x) * (conj (η x) * F₂ x).re) U) :
    testIntegral U g η (fun x => F₁ x + F₂ x) =
      testIntegral U g η F₁ + testIntegral U g η F₂ := by
  unfold testIntegral
  rw [← integral_add h₁ h₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_add, Complex.add_re]

/-- The first variation of the action with the tidal term. -/
theorem first_variation (p : MassiveParameters) (hU : IsOpen U)
    (hsym : ∀ x ∈ U, (g x).IsSymm) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hne : ∀ x ∈ U, ψ x ≠ 0)
    (hB : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => Bup y i j) x)
    (hBsym : ∀ x ∈ U, (Bup x).IsSymm)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (relativeAction p g Bup ψ η U)
      (-2 * testIntegral U g η (tidalResidual p g Bup ψ)) 0 := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have h1 := hasDerivAt_kg_relative p hU hsym hg hd hψ hη hc hs
  have h2 := hasDerivAt_tidal_relative p hU hg hd hψ hne hB hBsym hη1 hc hs
  have hgc : ContinuousOn g U := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hpair {F : Covector → ℂ} (hF : ContinuousOn F U) :
      IntegrableOn (fun x => volumeFactor (g x) * (conj (η x) * F x).re) U := by
    have h := (integrable_pair hgc hF hη.continuous hc hs).re
    simpa only [Function.comp_apply, RCLike.re_eq_complex_re, Complex.smul_re, smul_eq_mul]
      using h.integrableOn
  have hadd : testIntegral U g η (tidalResidual p g Bup ψ) =
      testIntegral U g η (residual p g ψ) + testIntegral U g η (tidalTerm p g Bup ψ) :=
    testIntegral_add
      (hpair fun x hx =>
        (residual_continuousAt p (hg x hx) (hd x hx) (hψ x hx)).continuousWithinAt)
      (hpair fun x hx => (tidalTerm_continuousAt p (hg x hx) (hd x hx) (hψ x hx) (hne x hx)
        (fun i j => hB i j x hx)).continuousWithinAt)
  rw [hadd, mul_add]
  exact h1.add h2

/-- The Euler–Lagrange residual vanishes exactly when the corrected field
equation holds, with coefficient `+ħ²/(12m²c⁴)`. -/
theorem tidalResidual_eq_zero_iff (p : MassiveParameters) (g Bup : Covector → Mat4)
    (ψ : Covector → ℂ) (x : Covector) :
    tidalResidual p g Bup ψ x = 0 ↔
      kgOperator p g ψ x + ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) *
        covariantDivergence g (tidalVector Bup ψ) x / ‖ψ x‖ : ℝ) : ℂ) * ψ x = 0 := by
  have hh : (p.hbar : ℂ) ≠ 0 := by exact_mod_cast p.hbar_pos.ne'
  have e : tidalResidual p g Bup ψ x = (p.hbar : ℂ) ^ 2 * (kgOperator p g ψ x +
      ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) *
        covariantDivergence g (tidalVector Bup ψ) x / ‖ψ x‖ : ℝ) : ℂ) * ψ x) := by
    rw [tidalResidual, residual_eq_smul_operator, tidalTerm, ← kappa_div, Complex.real_smul]
    push_cast
    field_simp
  rw [e, mul_eq_zero]
  exact ⟨fun h => h.resolve_left (pow_ne_zero 2 hh), Or.inr⟩

/-- The action with the tidal term is stationary under every smooth compactly
supported variation exactly when the corrected field equation holds. -/
theorem stationary_iff (p : MassiveParameters) (hU : IsOpen U)
    (hsym : ∀ x ∈ U, (g x).IsSymm) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hne : ∀ x ∈ U, ψ x ≠ 0)
    (hB : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => Bup y i j) x)
    (hBsym : ∀ x ∈ U, (Bup x).IsSymm) :
    (∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      HasDerivAt (relativeAction p g Bup ψ η U) 0 0) ↔
    ∀ x ∈ U, kgOperator p g ψ x + ((p.hbar ^ 2 / (12 * p.m ^ 2 * p.c ^ 4) *
      covariantDivergence g (tidalVector Bup ψ) x / ‖ψ x‖ : ℝ) : ℂ) * ψ x = 0 := by
  have hgc : ContinuousOn g U := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hF : ContinuousOn (tidalResidual p g Bup ψ) U := fun x hx =>
    ((residual_continuousAt p (hg x hx) (hd x hx) (hψ x hx)).add
      (tidalTerm_continuousAt p (hg x hx) (hd x hx) (hψ x hx) (hne x hx)
        (fun i j => hB i j x hx))).continuousWithinAt
  have hvar (η : Covector → ℂ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
      (hs : tsupport η ⊆ U) := first_variation p hU hsym hg hd hψ hne hB hBsym
    (hη.of_le (by simp)) hc hs
  rw [← forall₂_congr fun x _ => tidalResidual_eq_zero_iff p g Bup ψ x,
    zero_iff_tests hU hgc hd hF]
  refine forall₄_congr fun η hη hc hs => ⟨fun h => ?_, fun h => ?_⟩
  · have hu := (hvar η hη hc hs).unique h
    linarith
  · have h' := hvar η hη hc hs
    rw [h, mul_zero] at h'
    exact h'

end FoliationQM.TidalEulerLagrange
