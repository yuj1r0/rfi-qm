module

public import FoliationQM.CurvedPolarKG
public import FoliationQM.CurvedWeakEquation
public import FoliationQM.CurvedScalarGradient
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Variation of the density alone in a curved chart

Source: v13 `sec:master_equation`, statement (III) with
`eq:master_dressed_mass`: "variation with respect to `ρ` at fixed clock"
gives the dressed mass relation, component kinds B and C. On an open
coordinate set with a twice continuously differentiable symmetric Lorentzian
metric, let `ρ > 0` and `S` be twice continuously differentiable. The
density–phase action integrand is
`ρ [g(∂S,∂S) − m²c² + (ħ²/4) g(∂ ln ρ, ∂ ln ρ) + (ħ²/6) 𝓡]`.

For a smooth compactly supported `a`, the action of `ρ + t a` minus the action
of `ρ`, at the same `S`, is differentiable in `t` at zero with derivative
`∫ √(-g) a [g(∂S,∂S) − m²c² − ħ² □_g√ρ/√ρ + ħ²𝓡/6]`. Hence the action is
stationary under all such variations of the density alone exactly when
`g(∂S,∂S)/m² = c² (1 + q)` on the set, with
`q = ℓ_C² (□_g √ρ/√ρ − 𝓡/6)`.

The path `ρ + t a` is not affine in the wave, so the derivative is taken under
the integral directly; the divergence term is removed by the Green identity
for the metric flux. Only differences of actions are integrated, so no
finiteness of the background action is assumed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedDensityVariation

open MeasureTheory Set Filter LorentzMatrixGroup RNCVolumeDensity RNCCoordinateCurvature
open CurvedPolarAction CurvedGradientCovariance CurvedWaveDivergence CurvedFluxGreen CurvedPolarKG
open RNCCoordinateConnection RealLorentzFrame RNCHalfDensityJet
open scoped ContDiff Topology Matrix.Norms.Operator

variable (p : MassiveParameters) {g : Covector → Mat4} {ρ S a : Covector → ℝ}
  {U : Set Covector} {x : Covector} {t : ℝ}

/-- The coefficient of the density in the density–phase integrand that does
not involve derivatives of the density. -/
def potential (p : MassiveParameters) (g : Covector → Mat4) (S : Covector → ℝ)
    (x : Covector) : ℝ :=
  pairing g S S x - p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 / 6 * scalar g x

/-- The density–phase integrand at a point along the density path `ρ + t a`,
as an explicit function of `t`. -/
def profile (p : MassiveParameters) (g : Covector → Mat4) (ρ S a : Covector → ℝ)
    (x : Covector) (t : ℝ) : ℝ :=
  (ρ x + t * a x) * potential p g S x + p.hbar ^ 2 / 4 *
    ((pairing g ρ ρ x + t * (pairing g ρ a x + pairing g a ρ x) + t ^ 2 * pairing g a a x) /
      (ρ x + t * a x))

/-- The derivative in `t` of the integrand along the density path. -/
def profileDeriv (p : MassiveParameters) (g : Covector → Mat4) (ρ S a : Covector → ℝ)
    (x : Covector) (t : ℝ) : ℝ :=
  a x * potential p g S x + p.hbar ^ 2 / 4 *
    ((pairing g ρ a x + pairing g a ρ x + 2 * t * pairing g a a x) / (ρ x + t * a x) -
      (pairing g ρ ρ x + t * (pairing g ρ a x + pairing g a ρ x) + t ^ 2 * pairing g a a x) *
        a x / (ρ x + t * a x) ^ 2)

/-- The amplitude direction `a / (2√ρ)` of the density direction `a`. -/
def amplitudeTest (ρ a : Covector → ℝ) (y : Covector) : ℝ := a y / (2 * √(ρ y))

/-- The action of the density `ρ + t a` minus the action of `ρ`, at the same
phase, over a coordinate set. -/
def densityRelativeAction (p : MassiveParameters) (g : Covector → Mat4) (ρ S a : Covector → ℝ)
    (U : Set Covector) (t : ℝ) : ℝ :=
  ∫ x in U, volumeFactor (g x) *
    (hydroDensity p g (fun y => ρ y + t * a y) S x - hydroDensity p g ρ S x)

/-- Stationarity of the density–phase action under all smooth compactly
supported variations of the density alone. -/
def DensityStationary (p : MassiveParameters) (g : Covector → Mat4) (ρ S : Covector → ℝ)
    (U : Set Covector) : Prop :=
  ∀ a : Covector → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
    HasDerivAt (densityRelativeAction p g ρ S a U) 0 0

/-- Coordinate components of the differential along the density path. -/
theorem components_affine (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x) (t : ℝ) :
    components (fun y => ρ y + t * a y) x = components ρ x + t • components a x := by
  funext i
  have h : HasFDerivAt (fun y => ρ y + t * a y) (fderiv ℝ ρ x + t • fderiv ℝ a x) x :=
    hρ.hasFDerivAt.add (ha.hasFDerivAt.const_mul t)
  simp only [components, h.fderiv, _root_.add_apply, _root_.smul_apply,
    Pi.add_apply, Pi.smul_apply]

/-- Coordinate components of the differential of the logarithm of a positive
density. -/
theorem components_log (hρ : DifferentiableAt ℝ ρ x) (hp : 0 < ρ x) :
    components (Real.log ∘ ρ) x = (ρ x)⁻¹ • components ρ x := by
  funext i
  have h := PolarDifferential.fderiv_log_density_apply hρ hp (axis i)
  simp only [components, Pi.smul_apply, smul_eq_mul]
  rw [show (Real.log ∘ ρ) = fun y => Real.log (ρ y) from rfl, h, div_eq_inv_mul]

/-- The density–phase integrand depends only on the germ of the density. -/
theorem hydroDensity_congr {ρ₁ ρ₂ : Covector → ℝ} (he : ρ₁ =ᶠ[𝓝 x] ρ₂) :
    hydroDensity p g ρ₁ S x = hydroDensity p g ρ₂ S x := by
  have hl : (Real.log ∘ ρ₁) =ᶠ[𝓝 x] (Real.log ∘ ρ₂) := he.fun_comp Real.log
  have hc : components (Real.log ∘ ρ₁) x = components (Real.log ∘ ρ₂) x :=
    funext fun i => by simp only [components, hl.fderiv_eq]
  simp only [hydroDensity, pairing, hc, he.eq_of_nhds]

/-- Along the density path the integrand is the explicit profile, where the
perturbed density is positive. -/
theorem hydroDensity_affine (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x)
    (hpos : 0 < ρ x + t * a x) :
    hydroDensity p g (fun y => ρ y + t * a y) S x = profile p g ρ S a x t := by
  have hd : DifferentiableAt ℝ (fun y => ρ y + t * a y) x := hρ.add (ha.const_mul t)
  have hl := components_log (ρ := fun y => ρ y + t * a y) hd hpos
  have hlog : pairing g (Real.log ∘ fun y => ρ y + t * a y) (Real.log ∘ fun y => ρ y + t * a y) x =
      (pairing g ρ ρ x + t * (pairing g ρ a x + pairing g a ρ x) + t ^ 2 * pairing g a a x) /
        (ρ x + t * a x) ^ 2 := by
    simp only [pairing, hl, components_affine hρ ha t, map_add, map_smul,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hydroDensity, hlog, profile, potential]
  field_simp
  ring

/-- The derivative of a linear term plus a quadratic over a linear function. -/
theorem hasDerivAt_ratio (r α w k A B C t : ℝ) (h : r + t * α ≠ 0) :
    HasDerivAt (fun s : ℝ => (r + s * α) * w + k * ((A + s * B + s ^ 2 * C) / (r + s * α)))
      (α * w + k * ((B + 2 * t * C) / (r + t * α) -
        (A + t * B + t ^ 2 * C) * α / (r + t * α) ^ 2)) t := by
  have hD : HasDerivAt (fun s : ℝ => r + s * α) α t := by
    simpa using ((hasDerivAt_id t).mul_const α).const_add r
  have h1 : HasDerivAt (fun s : ℝ => A + s * B) B t := by
    simpa using ((hasDerivAt_id t).mul_const B).const_add A
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * C) (2 * t * C) t := by
    simpa using (hasDerivAt_pow 2 t).mul_const C
  have hN : HasDerivAt (fun s : ℝ => A + s * B + s ^ 2 * C) (B + 2 * t * C) t := h1.add h2
  have key : HasDerivAt
      (fun s : ℝ => (r + s * α) * w + k * ((A + s * B + s ^ 2 * C) / (r + s * α)))
      (α * w + k * (((B + 2 * t * C) * (r + t * α) - (A + t * B + t ^ 2 * C) * α) /
        (r + t * α) ^ 2)) t :=
    (hD.mul_const w).add ((hN.div hD h).const_mul k)
  convert key using 1
  field_simp

/-- The explicit profile is differentiable in the path parameter. -/
theorem hasDerivAt_profile (h : ρ x + t * a x ≠ 0) :
    HasDerivAt (profile p g ρ S a x) (profileDeriv p g ρ S a x t) t :=
  hasDerivAt_ratio _ _ _ _ _ _ _ t h

/-- Coordinate components of the differential of the amplitude `√ρ`. -/
theorem components_sqrt (hρ : DifferentiableAt ℝ ρ x) (hp : 0 < ρ x) :
    components (fun y => √(ρ y)) x = (1 / (2 * √(ρ x))) • components ρ x := by
  funext i
  simp only [components, (hρ.hasFDerivAt.sqrt hp.ne').fderiv, _root_.smul_apply,
    Pi.smul_apply]

/-- Coordinate components of the differential of the amplitude direction. -/
theorem components_amplitudeTest (hρ : DifferentiableAt ℝ ρ x) (ha : DifferentiableAt ℝ a x)
    (hp : 0 < ρ x) :
    components (amplitudeTest ρ a) x =
      (1 / (2 * √(ρ x))) • components a x - (a x / (4 * √(ρ x) ^ 3)) • components ρ x := by
  have hr : 0 < √(ρ x) := Real.sqrt_pos.mpr hp
  have hs := (hρ.hasFDerivAt.sqrt hp.ne').const_mul 2
  have hne : 2 * √(ρ x) ≠ 0 := by positivity
  have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt x hs
  have he : amplitudeTest ρ a = fun y => a y * (2 * √(ρ y))⁻¹ :=
    funext fun y => div_eq_mul_inv _ _
  have hq : HasFDerivAt (amplitudeTest ρ a)
      (a x • (-((2 * √(ρ x)) ^ 2)⁻¹ • (2 : ℝ) • (1 / (2 * √(ρ x))) • fderiv ℝ ρ x) +
        (2 * √(ρ x))⁻¹ • fderiv ℝ a x) x := by
    rw [he]
    exact ha.hasFDerivAt.fun_mul hinv
  funext i
  simp only [components, hq.fderiv, _root_.add_apply, _root_.smul_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- At the base density the derivative of the profile is the potential term
plus the gradient pairing of the amplitude direction with the amplitude. -/
theorem profileDeriv_zero (hs : (g x).IsSymm) (hρ : DifferentiableAt ℝ ρ x)
    (ha : DifferentiableAt ℝ a x) (hp : 0 < ρ x) :
    profileDeriv p g ρ S a x 0 = a x * potential p g S x +
      2 * p.hbar ^ 2 * pairing g (amplitudeTest ρ a) (fun y => √(ρ y)) x := by
  have hr : 0 < √(ρ x) := Real.sqrt_pos.mpr hp
  have hsq : ρ x = √(ρ x) ^ 2 := (Real.sq_sqrt hp.le).symm
  have hsym : pairing g ρ a x = pairing g a ρ x := CurvedPolarWave.pairing_symm hs ρ a
  have hpair : pairing g (amplitudeTest ρ a) (fun y => √(ρ y)) x =
      pairing g a ρ x / (4 * √(ρ x) ^ 2) - a x * pairing g ρ ρ x / (8 * √(ρ x) ^ 4) := by
    simp only [pairing, components_amplitudeTest hρ ha hp, components_sqrt hρ hp, map_sub,
      map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [profileDeriv, hpair, hsym]
  simp only [zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  generalize √(ρ x) = r at hr hsq
  rw [hsq]
  field_simp
  ring

/-- The density direction times the Hamilton–Jacobi residual, in terms of the
amplitude direction and the wave operator of the amplitude. -/
theorem mul_hjResidual (hp : 0 < ρ x) :
    a x * hjResidual p g (fun y => √(ρ y)) S x = a x * potential p g S x -
      2 * p.hbar ^ 2 * (amplitudeTest ρ a x * wave g (fun y => √(ρ y)) x) := by
  have hr : 0 < √(ρ x) := Real.sqrt_pos.mpr hp
  simp only [hjResidual, potential, amplitudeTest]
  field_simp
  ring

/-- For real fields the kinetic pairing is the inverse-metric pairing of the
differentials. -/
theorem kinetic_eq_pairing (g : Covector → Mat4) (u f : Covector → ℝ) (x : Covector) :
    kinetic g u f x = pairing g u f x := by
  simp only [kinetic, pairing, form_apply, components, star_trivial, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The inverse-metric pairing of twice continuously differentiable fields is
continuous. -/
theorem continuousAt_pairing (hg : ContDiffAt ℝ 2 g x) (hd : (g x).det < 0) {f k : Covector → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hk : ContDiffAt ℝ 2 k x) : ContinuousAt (pairing g f k) x :=
  (CurvedScalarGradient.contDiffAt_pairing (hg.of_le (by norm_num))
    (isUnit_iff_ne_zero.mpr hd.ne) hf hk).continuousAt

/-- The potential coefficient is continuous. -/
theorem continuousAt_potential (hg : ContDiffAt ℝ 2 g x) (hd : (g x).det < 0)
    (hS : ContDiffAt ℝ 2 S x) : ContinuousAt (potential p g S) x :=
  ((continuousAt_pairing hg hd hS hS).sub continuousAt_const).add
    (continuousAt_const.mul (CurvedFluxRegularity.scalar_continuousAt hg hd))

/-- The Hamilton–Jacobi residual of a positive amplitude is continuous. -/
theorem continuousAt_hjResidual {R : Covector → ℝ} (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : R x ≠ 0) :
    ContinuousAt (hjResidual p g R S) x :=
  ((((continuousAt_pairing hg hd hS hS).sub continuousAt_const).sub
    ((continuousAt_const.mul
      (CurvedFluxRegularity.wave_continuousAt (hg.of_le (by norm_num)) hd hR)).div
        hR.continuousAt hp)).add
    ((continuousAt_const.mul (CurvedFluxRegularity.scalar_continuousAt hg hd)).div_const 6))

/-- The amplitude direction of a smooth compactly supported density direction
is a continuously differentiable test with support in that of the direction. -/
theorem amplitudeTest_data (hρ : ∀ x ∈ U, ContDiffAt ℝ 2 ρ x) (hp : ∀ x ∈ U, 0 < ρ x)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ U) :
    ContDiff ℝ 1 (amplitudeTest ρ a) ∧ HasCompactSupport (amplitudeTest ρ a) ∧
      tsupport (amplitudeTest ρ a) ⊆ tsupport a := by
  have he : amplitudeTest ρ a = fun y => a y * (2 * √(ρ y))⁻¹ :=
    funext fun y => div_eq_mul_inv _ _
  have hts : tsupport (amplitudeTest ρ a) ⊆ tsupport a := by
    rw [he]
    exact tsupport_mul_subset_left
  refine ⟨contDiff_iff_contDiffAt.mpr fun y => ?_,
    hc.mono' ((subset_tsupport _).trans hts), hts⟩
  by_cases hy : y ∈ tsupport a
  · have hr : 0 < √(ρ y) := Real.sqrt_pos.mpr (hp y (hs hy))
    have h2 : ContDiffAt ℝ 1 (fun z => 2 * √(ρ z)) y :=
      contDiffAt_const.mul (((hρ y (hs hy)).of_le (by norm_num)).sqrt (hp y (hs hy)).ne')
    exact (ha.contDiffAt.of_le (by simp)).div h2 (by positivity)
  · have hz : amplitudeTest ρ a =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [amplitudeTest, hz]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- The first variation of the density–phase action under a change of the
density alone is the Hamilton–Jacobi residual tested against the change. -/
theorem hasDerivAt_densityRelative (hU : IsOpen U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hsym : ∀ x ∈ U, (g x).IsSymm) (hd : ∀ x ∈ U, (g x).det < 0)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 2 ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ 2 S x)
    (hp : ∀ x ∈ U, 0 < ρ x) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    HasDerivAt (densityRelativeAction p g ρ S a U)
      (∫ x in U, volumeFactor (g x) * (a x * hjResidual p g (fun y => √(ρ y)) S x)) 0 := by
  classical
  set K : Set Covector := tsupport a with hKdef
  have hK : IsCompact K := hc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have ha2 : ∀ x, ContDiffAt ℝ 2 a x := fun x => ha.contDiffAt.of_le (by simp)
  have hρd : ∀ x ∈ K, DifferentiableAt ℝ ρ x := fun x hx =>
    (hρ x (hs hx)).differentiableAt (by norm_num)
  have had : ∀ x, DifferentiableAt ℝ a x := fun x => (ha2 x).differentiableAt (by norm_num)
  have hρK : ContinuousOn ρ K := fun x hx => (hρ x (hs hx)).continuousAt.continuousWithinAt
  have haK : ContinuousOn a K := ha.continuous.continuousOn
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (f := ρ) hρK (a := 0) (fun x hx => hp x (hs hx))
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha.continuous
  have hC1 : 0 < |C| + 1 := by positivity
  set δ : ℝ := m / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hpos' : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, 0 < ρ x + t * a x := by
    intro t ht x hx
    have h1 : |a x| ≤ |C| + 1 := by
      have := hC x
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_abs_self C).trans (by linarith))
    have h2 : |t * a x| ≤ δ * (|C| + 1) := by
      rw [abs_mul]
      exact mul_le_mul ht h1 (abs_nonneg _) hδ.le
    have h3 : δ * (|C| + 1) = m / 2 := by
      rw [hδdef]
      field_simp
    have h4 := hmK x hx
    have h5 := neg_abs_le (t * a x)
    linarith
  let Sset : Set (ℝ × Covector) := Metric.closedBall 0 δ ×ˢ K
  have hSc : IsCompact Sset := (isCompact_closedBall 0 δ).prod hK
  have hmemS : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, (t, x) ∈ Sset := fun t ht x hx =>
    ⟨mem_closedBall_zero_iff.mpr ((Real.norm_eq_abs t).le.trans ht), hx⟩
  have lift : ∀ {f : Covector → ℝ}, ContinuousOn f K →
      ContinuousOn (fun q : ℝ × Covector => f q.2) Sset :=
    fun hf => hf.comp continuousOn_snd fun q hq => hq.2
  have ht : ContinuousOn (fun q : ℝ × Covector => q.1) Sset := continuousOn_fst
  have hvK : ContinuousOn (fun x => volumeFactor (g x)) K := fun x hx =>
    (CurvedWeakEquation.volumeFactor_continuous.continuousAt.comp
      (hg x (hs hx)).continuousAt).continuousWithinAt
  have hwK : ContinuousOn (potential p g S) K := fun x hx =>
    (continuousAt_potential p (hg x (hs hx)) (hd x (hs hx)) (hS x (hs hx))).continuousWithinAt
  have hAK : ContinuousOn (pairing g ρ ρ) K := fun x hx =>
    (continuousAt_pairing (hg x (hs hx)) (hd x (hs hx)) (hρ x (hs hx))
      (hρ x (hs hx))).continuousWithinAt
  have hB1K : ContinuousOn (pairing g ρ a) K := fun x hx =>
    (continuousAt_pairing (hg x (hs hx)) (hd x (hs hx)) (hρ x (hs hx)) (ha2 x)).continuousWithinAt
  have hB2K : ContinuousOn (pairing g a ρ) K := fun x hx =>
    (continuousAt_pairing (hg x (hs hx)) (hd x (hs hx)) (ha2 x) (hρ x (hs hx))).continuousWithinAt
  have hCK : ContinuousOn (pairing g a a) K := fun x hx =>
    (continuousAt_pairing (hg x (hs hx)) (hd x (hs hx)) (ha2 x) (ha2 x)).continuousWithinAt
  have hden : ContinuousOn (fun q : ℝ × Covector => ρ q.2 + q.1 * a q.2) Sset :=
    (lift hρK).add (ht.mul (lift haK))
  have hdenne : ∀ q ∈ Sset, ρ q.2 + q.1 * a q.2 ≠ 0 := fun q hq =>
    (hpos' q.1 ((Real.norm_eq_abs q.1).ge.trans (mem_closedBall_zero_iff.mp hq.1)) q.2 hq.2).ne'
  have hnum : ContinuousOn (fun q : ℝ × Covector => pairing g ρ ρ q.2 +
      q.1 * (pairing g ρ a q.2 + pairing g a ρ q.2) + q.1 ^ 2 * pairing g a a q.2) Sset :=
    ((lift hAK).add (ht.mul ((lift hB1K).add (lift hB2K)))).add ((ht.pow 2).mul (lift hCK))
  have hnum' : ContinuousOn (fun q : ℝ × Covector => pairing g ρ a q.2 + pairing g a ρ q.2 +
      2 * q.1 * pairing g a a q.2) Sset :=
    ((lift hB1K).add (lift hB2K)).add ((continuousOn_const.mul ht).mul (lift hCK))
  let Γ : ℝ × Covector → ℝ := fun q => volumeFactor (g q.2) * profile p g ρ S a q.2 q.1
  let Φ : ℝ × Covector → ℝ := fun q => volumeFactor (g q.2) * profileDeriv p g ρ S a q.2 q.1
  have hΓ : ContinuousOn Γ Sset :=
    (lift hvK).mul ((hden.mul (lift hwK)).add (continuousOn_const.mul (hnum.div hden hdenne)))
  have hΦ : ContinuousOn Φ Sset :=
    (lift hvK).mul (((lift haK).mul (lift hwK)).add (continuousOn_const.mul
      ((hnum'.div hden hdenne).sub ((hnum.mul (lift haK)).div (hden.pow 2)
        fun q hq => pow_ne_zero 2 (hdenne q hq)))))
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hΦ
  let F : ℝ → Covector → ℝ := fun t x => volumeFactor (g x) *
    (hydroDensity p g (fun y => ρ y + t * a y) S x - hydroDensity p g ρ S x)
  let F' : ℝ → Covector → ℝ := fun t => K.indicator fun x => Φ (t, x)
  have hFout : ∀ t x, x ∉ K → F t x = 0 := by
    intro t x hx
    have hz : a =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : (fun y => ρ y + t * a y) =ᶠ[𝓝 x] ρ := hz.mono fun y hy => by simp [hy]
    simp only [F, hydroDensity_congr p he, sub_self, mul_zero]
  have h0 : ∀ x ∈ K, hydroDensity p g ρ S x = profile p g ρ S a x 0 := by
    intro x hx
    have h := hydroDensity_affine p (g := g) (S := S) (t := 0) (hρd x hx) (had x)
      (by simpa using hp x (hs hx))
    simpa only [zero_mul, add_zero] using h
  have hFin : ∀ t : ℝ, |t| ≤ δ → ∀ x ∈ K, F t x = Γ (t, x) - Γ (0, x) := by
    intro t ht x hx
    simp only [F, Γ, hydroDensity_affine p (hρd x hx) (had x) (hpos' t ht x hx), h0 x hx]
    ring
  have habs : ∀ t ∈ Metric.ball (0 : ℝ) δ, |t| ≤ δ := fun t ht =>
    (Real.norm_eq_abs t).ge.trans (mem_ball_zero_iff.mp ht).le
  have hdiff : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => F s x) (F' t x) t := by
    intro x t ht
    by_cases hx : x ∈ K
    · have h := ((hasDerivAt_profile p (g := g) (S := S)
        (hpos' t (habs t ht) x hx).ne').const_mul (volumeFactor (g x))).sub_const (Γ (0, x))
      have hev : (fun s => F s x) =ᶠ[𝓝 t]
          fun s => volumeFactor (g x) * profile p g ρ S a x s - Γ (0, x) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs'
        exact hFin s (habs s hs') x hx
      have hF' : F' t x = volumeFactor (g x) * profileDeriv p g ρ S a x t := by
        simp only [F', indicator_of_mem hx, Φ]
      rw [hF']
      exact h.congr_of_eventuallyEq hev
    · have hF' : F' t x = 0 := by simp only [F', indicator_of_notMem hx]
      rw [hF', show (fun s => F s x) = fun _ => 0 from funext fun s => hFout s x hx]
      exact hasDerivAt_const t 0
  have hbound : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖F' t x‖ ≤ K.indicator (fun _ => B) x := by
    intro x t ht
    by_cases hx : x ∈ K
    · simp only [F', indicator_of_mem hx]
      exact hB (t, x) (hmemS t (habs t ht) x hx)
    · simp [F', indicator_of_notMem hx]
  have hslice : ∀ t : ℝ, |t| ≤ δ → ∀ {f : ℝ × Covector → ℝ}, ContinuousOn f Sset →
      AEStronglyMeasurable (K.indicator fun x => f (t, x)) volume := by
    intro t ht f hf
    have hcont : ContinuousOn (fun x => f (t, x)) K :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => hmemS t ht x hx
    exact (aestronglyMeasurable_indicator_iff hKm).mpr (hcont.aestronglyMeasurable hKm)
  have hFmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) volume := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have hEq : F t = K.indicator fun x => (fun q : ℝ × Covector => Γ q - Γ (0, q.2)) (t, x) := by
      funext x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        exact hFin t (habs t ht) x hx
      · rw [indicator_of_notMem hx]
        exact hFout t x hx
    rw [hEq]
    exact hslice t (habs t ht) (hΓ.sub (hΓ.comp
      (continuous_const.prodMk continuous_snd).continuousOn
      fun q hq => hmemS 0 (by simpa using hδ.le) q.2 hq.2))
  have hF0 : Integrable (F 0) volume := by
    have h0' : F 0 = fun _ => 0 := by
      funext x
      simp [F]
    rw [h0']
    exact integrable_zero _ _ _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := K.indicator fun _ => B)
    (Metric.ball_mem_nhds (0 : ℝ) hδ) hFmeas hF0 (hslice 0 (by simpa using hδ.le) hΦ)
    (Filter.Eventually.of_forall hbound)
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKm)
    (Filter.Eventually.of_forall hdiff)
  obtain ⟨hβ, hβc, hβs⟩ := amplitudeTest_data hρ hp ha hc hs
  have hR : ∀ x ∈ U, ContDiffAt ℝ 2 (fun y => √(ρ y)) x := fun x hx =>
    (hρ x hx).sqrt (hp x hx).ne'
  have hg1 : ∀ x ∈ U, ContDiffAt ℝ 1 g x := fun x hx => (hg x hx).of_le (by norm_num)
  obtain ⟨hI2, hI3⟩ := integrable_pairings hβ hβc (hβs.trans hs) hg1 hd hR
  have hgreen := integral_green hβ hβc (hβs.trans hs) hg1 hd hR
  have hpoint : ∀ x ∈ U, volumeFactor (g x) * (a x * hjResidual p g (fun y => √(ρ y)) S x) =
      F' 0 x - 2 * p.hbar ^ 2 *
        (volumeFactor (g x) • kinetic g (amplitudeTest ρ a) (fun y => √(ρ y)) x +
          volumeFactor (g x) • (star (amplitudeTest ρ a x) * wave g (fun y => √(ρ y)) x)) := by
    intro x hx
    by_cases hxK : x ∈ K
    · have hF' : F' 0 x = volumeFactor (g x) * profileDeriv p g ρ S a x 0 := by
        simp only [F', indicator_of_mem hxK, Φ]
      rw [hF', profileDeriv_zero p (hsym x hx) (hρd x hxK) (had x) (hp x hx),
        mul_hjResidual p (hp x hx), kinetic_eq_pairing, star_trivial, smul_eq_mul, smul_eq_mul]
      ring
    · have hz : a =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxK
      have hβz : amplitudeTest ρ a =ᶠ[𝓝 x] fun _ => 0 :=
        hz.mono fun y hy => by simp [amplitudeTest, hy]
      have hkin : kinetic g (amplitudeTest ρ a) (fun y => √(ρ y)) x = 0 := by
        simp [kinetic, hβz.fderiv_eq]
      have hF' : F' 0 x = 0 := by simp only [F', indicator_of_notMem hxK]
      rw [hF', hkin, hβz.eq_of_nhds, hz.eq_of_nhds]
      simp
  have hval : (∫ x, F' 0 x) =
      ∫ x in U, volumeFactor (g x) * (a x * hjResidual p g (fun y => √(ρ y)) S x) := by
    have hF'U : (∫ x in U, F' 0 x) = ∫ x, F' 0 x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [F', indicator_of_notMem fun h => hx (hs h)]
    have hsum : (∫ x in U,
        (volumeFactor (g x) • kinetic g (amplitudeTest ρ a) (fun y => √(ρ y)) x +
          volumeFactor (g x) • (star (amplitudeTest ρ a x) * wave g (fun y => √(ρ y)) x))) = 0 := by
      rw [integral_add hI2 hI3, hgreen, neg_add_cancel]
    have h1 := setIntegral_congr_fun (μ := volume) hU.measurableSet hpoint
    have h2 : (∫ x in U, (F' 0 x - 2 * p.hbar ^ 2 *
        (volumeFactor (g x) • kinetic g (amplitudeTest ρ a) (fun y => √(ρ y)) x +
          volumeFactor (g x) • (star (amplitudeTest ρ a x) * wave g (fun y => √(ρ y)) x)))) =
        (∫ x in U, F' 0 x) - 2 * p.hbar ^ 2 * 0 := by
      have hI23 : IntegrableOn (fun x => 2 * p.hbar ^ 2 *
          (volumeFactor (g x) • kinetic g (amplitudeTest ρ a) (fun y => √(ρ y)) x +
            volumeFactor (g x) • (star (amplitudeTest ρ a x) * wave g (fun y => √(ρ y)) x))) U :=
        (hI2.add hI3).const_mul _
      rw [integral_sub key.1.integrableOn hI23, integral_const_mul, hsum]
    rw [h1, h2, mul_zero, sub_zero, hF'U]
  have hfun : densityRelativeAction p g ρ S a U = fun t => ∫ x, F t x :=
    funext fun t => setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hFout t x fun h => hx (hs h)
  rw [hfun, ← hval]
  exact key.2

/-- The density–phase action is stationary under all smooth compactly
supported variations of the density alone exactly when the Hamilton–Jacobi
residual of the amplitude `√ρ` vanishes. -/
theorem density_stationary_iff (hU : IsOpen U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hsym : ∀ x ∈ U, (g x).IsSymm) (hd : ∀ x ∈ U, (g x).det < 0)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 2 ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ 2 S x)
    (hp : ∀ x ∈ U, 0 < ρ x) :
    DensityStationary p g ρ S U ↔ ∀ x ∈ U, hjResidual p g (fun y => √(ρ y)) S x = 0 := by
  have hv : ∀ x ∈ U, volumeFactor (g x) ≠ 0 := fun x hx =>
    (Real.sqrt_pos.2 (neg_pos.mpr (hd x hx))).ne'
  have hcont : ContinuousOn
      (fun x => volumeFactor (g x) * hjResidual p g (fun y => √(ρ y)) S x) U := fun x hx =>
    ((CurvedWeakEquation.volumeFactor_continuous.continuousAt.comp (hg x hx).continuousAt).mul
      (continuousAt_hjResidual p (hg x hx) (hd x hx) ((hρ x hx).sqrt (hp x hx).ne') (hS x hx)
        (Real.sqrt_pos.mpr (hp x hx)).ne')).continuousWithinAt
  constructor
  · intro h
    have hz : ∀ x ∈ U, volumeFactor (g x) * hjResidual p g (fun y => √(ρ y)) S x = 0 := by
      apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ hU hcont continuousOn_const
      change ∀ᵐ x ∂volume.restrict U,
        volumeFactor (g x) * hjResidual p g (fun y => √(ρ y)) S x = 0
      rw [ae_restrict_iff' hU.measurableSet]
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hcont.locallyIntegrableOn hU.measurableSet)
      intro a ha hc hs
      have hi := (hasDerivAt_densityRelative p hU hg hsym hd hρ hS hp ha hc hs).unique
        (h a ha hc hs)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))])] at hi
      rw [← hi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    intro x hx
    exact (mul_eq_zero.mp (hz x hx)).resolve_left (hv x hx)
  · intro h a ha hc hs
    have hzero : (∫ x in U, volumeFactor (g x) *
        (a x * hjResidual p g (fun y => √(ρ y)) S x)) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [h x hx, mul_zero, mul_zero]
    exact hzero ▸ hasDerivAt_densityRelative p hU hg hsym hd hρ hS hp ha hc hs

/-- Stationarity under variation of the density alone is the dressed mass
relation `g(∂S,∂S)/m² = c² (1 + q)`. -/
theorem density_stationary_iff_dressed_mass (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hsym : ∀ x ∈ U, (g x).IsSymm)
    (hd : ∀ x ∈ U, (g x).det < 0) (hρ : ∀ x ∈ U, ContDiffAt ℝ 2 ρ x)
    (hS : ∀ x ∈ U, ContDiffAt ℝ 2 S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    DensityStationary p g ρ S U ↔ ∀ x ∈ U,
      pairing g S S x / p.m ^ 2 = p.c ^ 2 * (1 + defect p g (fun y => √(ρ y)) x) :=
  (density_stationary_iff p hU hg hsym hd hρ hS hp).trans
    (forall₂_congr fun x _ => hjResidual_zero_iff p g _ S x)

end FoliationQM.CurvedDensityVariation
