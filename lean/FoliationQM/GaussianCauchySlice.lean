module

public import FoliationQM.SpatialFisherEnergy
public import FoliationQM.ScalarDressedCurrent
public import FoliationQM.PolarTangentEquiv

/-!
# Gaussian Cauchy data and the ADM dilatation on the initial slice

For the parenthetical in v13 `eq:dilatation_coercivity_bound`, a real
initial profile specifies only one of the two data of the free KG equation.
Here the independently prescribed normal derivative is (K − iω)ψ in the
coordinate x⁰ = ct. The field theorem concerns any C² polar realization
satisfying KG on the slice. The algebraic second jet exhibits compatibility
for every K. No time evolution or frequency projection is constructed here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCauchySlice

open LorentzCoordinates OsmoticSliceFields ObserverFluxDensity PolarSecondDifferential
open DressedMassDensityVariation ActionDensity ScalarPhaseCurrent
open scoped ComplexConjugate ContDiff

/-- Three-dimensional Gaussian amplitude, with density variance parameter σ² per axis. -/
def amplitude (σ : ℝ) (y : Spatial) : ℝ := Real.exp (-speedSq y / (4 * σ ^ 2))

/-- The real Gaussian amplitude is positive throughout the spatial slice. -/
theorem amplitude_pos (σ : ℝ) (y : Spatial) : 0 < amplitude σ y := Real.exp_pos _

/-- The initial amplitude profile is smooth in all three spatial coordinates. -/
theorem smooth_amplitude (σ : ℝ) : ContDiff ℝ ∞ (amplitude σ) := by
  unfold amplitude speedSq spatialDot
  fun_prop

/-- At each spatial point the free KG equation fixes the real second normal derivative
to ΔR − (mc/ℏ)²R. The first normal derivative (K−iω)R is free for every K and ω.
The displayed complex residual is the full second-order KG jet in ct coordinates. -/
theorem compatible_second_jet (p : MassiveParameters) (R K freq : ℝ) (spatialSecond : Spatial) :
    ∃ d₀ d₀₀ : ℂ, d₀ = ((K : ℂ) - Complex.I * freq) * R ∧ d₀₀.im = 0 ∧
      d₀₀ - spatialSecond 0 - spatialSecond 1 - spatialSecond 2 +
        ((p.m^2 * p.c^2 / p.hbar^2 : ℝ) : ℂ) * R = 0 := by
  refine ⟨_, ((spatialSecond 0 + spatialSecond 1 + spatialSecond 2 -
    p.m^2 * p.c^2 / p.hbar^2 * R : ℝ) : ℂ), rfl, Complex.ofReal_im _, ?_⟩
  push_cast
  ring

private theorem derivative_components (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (i : Fin 4) :
    let ψ := actionField p ρ S
    let z := conj (ψ x) * directionalDerivative ψ (Madelung.coordinateVector i) x
    z.re = phaseDifferential ρ x i / 2 ∧
      z.im = ρ x * phaseDifferential S x i / p.hbar := by
  let v := Madelung.coordinateVector i
  let ψ := actionField p ρ S
  have hΦ : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv] using hS.mul_const p.hbar⁻¹
  have hder : directionalDerivative ψ v x =
      PolarTangentEquiv.tangent p (ρ x) (ψ x) (phaseDifferential ρ x i) (phaseDifferential S x i) := by
    change fderiv ℝ (PolarDifferential.polarField ρ (fun y => S y / p.hbar)) x v = _
    rw [PolarDifferential.fderiv_polarField_apply hρ hΦ hp, fderiv_action_phase_apply p hS]
    exact (PolarTangentEquiv.tangent_eq_polarTangent p _ _ _ _ hp).symm
  have hb := actionField_conj_mul p ρ S x hp.le
  change (conj (ψ x) * directionalDerivative ψ v x).re = _ ∧
    (conj (ψ x) * directionalDerivative ψ v x).im = _
  rw [hder, PolarTangentEquiv.conj_mul_tangent p hp hb]
  simp

/-- The complex Cauchy datum determines both the logarithmic normal density derivative
and the positive normal momentum, with the physical factor ℏ. -/
theorem normal_data (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (K freq : ℝ)
    (hd : directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) x =
      actionField p ρ S x * ((K : ℂ) - Complex.I * freq)) :
    normalScore ρ x = 2 * K ∧ normalMomentum S x = p.hbar * freq := by
  obtain ⟨hr, hi⟩ := derivative_components p hρ hS hp 0
  rw [hd, ← mul_assoc, actionField_conj_mul p ρ S x hp.le] at hr hi
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_im,
    Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    add_zero, zero_add, sub_zero, zero_sub] at hr hi
  constructor
  · change fderiv ℝ (fun y => Real.log (ρ y)) x (Madelung.coordinateVector 0) = _
    rw [PolarDifferential.fderiv_log_density_apply hρ hp]
    apply (div_eq_iff hp.ne').mpr
    change phaseDifferential ρ x 0 = _
    linarith
  · unfold normalMomentum
    field_simp [p.hbar_pos.ne'] at hi
    linarith

private theorem spatial_current_zero (p : MassiveParameters) {ρ S : Covector → ℝ}
    {R : Spatial → ℝ} {y : Spatial} (hR : DifferentiableAt ℝ R y)
    (hy : DifferentiableAt ℝ (actionField p ρ S) (slicePoint 0 y))
    (hslice : ∀ z, actionField p ρ S (slicePoint 0 z) = (R z : ℂ)) (i : Fin 3) :
    ScalarPhaseCurrent.current p (actionField p ρ S) (slicePoint 0 y) i.succ = 0 := by
  have hs := hy.hasFDerivAt.comp y (SpatialFisherEnergy.hasFDerivAt_slicePoint 0 y)
  have hr := Complex.ofRealCLM.hasFDerivAt.comp y hR.hasFDerivAt
  have heq : actionField p ρ S ∘ slicePoint 0 = Complex.ofRealCLM ∘ R := funext hslice
  rw [heq] at hs
  have he := hs.unique hr
  have hd := congrArg (fun L : Spatial →L[ℝ] ℂ => L (Pi.single i 1)) he
  simp only [ContinuousLinearMap.comp_apply, SpatialFisherEnergy.sliceTangent_unit,
    Complex.ofRealCLM_apply] at hd
  change -(p.hbar / p.m) * (conj (actionField p ρ S (slicePoint 0 y)) *
    fderiv ℝ (actionField p ρ S) (slicePoint 0 y) (Madelung.coordinateVector i.succ)).im = _
  rw [hslice, hd]
  simp

/-- The modulus of the real initial wave recovers the actual polar density on the slice. -/
theorem density_of_real_slice (p : MassiveParameters) {ρ S : Covector → ℝ} {R : Spatial → ℝ}
    (hslice : ∀ z, actionField p ρ S (slicePoint 0 z) = (R z : ℂ)) (y : Spatial)
    (hp : 0 ≤ ρ (slicePoint 0 y)) : ρ (slicePoint 0 y) = R y ^ 2 := by
  have h := actionField_conj_mul p ρ S (slicePoint 0 y) hp
  rw [hslice] at h
  have he := congrArg Complex.re h
  simpa [pow_two] using he.symm

/-- For a real initial spatial profile the actual complex current is purely temporal
and the spatial phase drift vanishes everywhere on the regular initial slice. -/
theorem slice_current (p : MassiveParameters) {ρ S : Covector → ℝ} {R : Spatial → ℝ}
    {y : Spatial} (hρ : DifferentiableAt ℝ ρ (slicePoint 0 y)) (hS : DifferentiableAt ℝ S (slicePoint 0 y))
    (hp : 0 < ρ (slicePoint 0 y)) (hR : DifferentiableAt ℝ R y)
    (hslice : ∀ z, actionField p ρ S (slicePoint 0 z) = (R z : ℂ))
    (K freq : ℝ) (hd : directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) (slicePoint 0 y)
      = actionField p ρ S (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq)) :
    ScalarPhaseCurrent.current p (actionField p ρ S) (slicePoint 0 y) =
      Pi.single 0 ((ρ (slicePoint 0 y) / p.m) * (p.hbar * freq)) ∧
    phaseDrift p.c S (slicePoint 0 y) = 0 := by
  let x := slicePoint 0 y
  have hΦ : DifferentiableAt ℝ (fun z => S z / p.hbar) (slicePoint 0 y) := by
    simpa only [div_eq_mul_inv] using hS.mul_const p.hbar⁻¹
  have hψ := PolarDifferential.differentiableAt_polarField hρ hΦ hp
  have hc (i : Fin 3) := spatial_current_zero p hR hψ hslice i
  have hm := (normal_data p hρ hS hp K freq hd).2
  change -phaseDifferential S x 0 = _ at hm
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [ScalarDressedCurrent.current_actionField p hρ hS hp, Pi.single_eq_same]
      change -(ρ x / p.m) * phaseDifferential S x 0 = _
      rw [← hm]
      ring
    · rw [hc, Pi.single_eq_of_ne (Fin.succ_ne_zero j)]
  · funext i
    have hz := hc i
    rw [ScalarDressedCurrent.current_actionField p hρ hS hp] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (div_ne_zero hp.ne' p.m_pos.ne'))
    simp [phaseDrift, hzero]

/-- On any regular massive KG realization of the Gaussian Cauchy data, drift is zero,
the normal log-density rate is 2K, and the physical dilatation is −2cK at time zero.
The width fixes the spatial profile independently of the prescribed normal datum K. -/
theorem gaussian_dilatation (p : MassiveParameters) {ρ S : Covector → ℝ} (σ K freq : ℝ)
    (_hσ : 0 < σ) (hfreq : 0 < freq) (hslice : ∀ y, actionField p ρ S (slicePoint 0 y) = (amplitude σ y : ℂ))
    (y : Spatial) (hρ : ContDiffAt ℝ 2 ρ (slicePoint 0 y)) (hS : ContDiffAt ℝ 2 S (slicePoint 0 y))
    (hp : 0 < ρ (slicePoint 0 y))
    (hd : directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) (slicePoint 0 y)
      = actionField p ρ S (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq))
    (hkg : box (actionField p ρ S) Madelung.coordinateVector (slicePoint 0 y) +
      (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * actionField p ρ S (slicePoint 0 y)) = 0) :
    phaseDrift p.c S (slicePoint 0 y) = 0 ∧ normalScore ρ (slicePoint 0 y) = 2 * K ∧
      dilatation p.c S (slicePoint 0 y) = -2 * p.c * K := by
  have hρ' := hρ.differentiableAt (by norm_num)
  have hS' := hS.differentiableAt (by norm_num)
  have ⟨hn, ha⟩ := normal_data p hρ' hS' hp K freq hd
  have hv := (slice_current p hρ' hS' hp ((smooth_amplitude σ).differentiable (by simp) y) hslice K freq hd).2
  have hf := NormalLogDensity.of_klein_gordon p hρ hS hp (ha ▸ mul_pos p.hbar_pos hfreq) hkg
  have hbal := normal_balance p.c_pos hf
  rw [hv, hn] at hbal
  simp [spatialDot] at hbal
  exact ⟨hv, hn, by linarith⟩

end FoliationQM.GaussianCauchySlice
