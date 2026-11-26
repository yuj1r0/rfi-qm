module

public import FoliationQM.TwoBodySchrodingerResidual

/-!
# Fisher variation and the two-body Bohm potential

A compact density variation induces the amplitude variation `a/(2R)`.
Integration by parts in the six spatial directions identifies its Fisher
first variation with the Bohm potential, on spacetime or on a fixed-time
configuration space.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyBohmGreen

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodySchrodingerResidual
open PolarSecondDifferential LorentzCoordinates
open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Amplitude test induced by the density test at a positive amplitude. -/
def testAmplitude (a R : X → ℝ) (p : X) : ℝ := a p / (2 * R p)

/-- The amplitude test inherits the regularity of the density test and amplitude. -/
theorem contDiff_testAmplitude {a R : X → ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a)
    (hR : ContDiff ℝ n R) (hp : ∀ p, 0 < R p) : ContDiff ℝ n (testAmplitude a R) :=
  ha.div (contDiff_const.mul hR) (fun p => mul_ne_zero (by norm_num) (hp p).ne')

omit [NormedSpace ℝ X] in
/-- The amplitude test vanishes outside the support of the density test. -/
theorem compact_testAmplitude {a R : X → ℝ} (hc : HasCompactSupport a) :
    HasCompactSupport (testAmplitude a R) := by
  change HasCompactSupport (fun z => a z / (2*R z))
  simpa only [div_eq_mul_inv, Pi.mul_def] using
    (hc.mul_right (f' := fun p => (2 * R p)⁻¹))

/-- Directional Fisher density for the six supplied physical axes. -/
def fisherOn (e : Index → X) (h m₁ m₂ : ℝ) (ρ : X → ℝ) (p : X) : ℝ :=
  ∑ j, h^2/(8*mass m₁ m₂ j) * ((directionalDerivative ρ (e j) p)^2 / ρ p)

/-- Linearization of the Fisher integrand in the original density coordinate. -/
def rawVariationOn (e : Index → X) (h m₁ m₂ : ℝ) (ρ a : X → ℝ) (p : X) : ℝ :=
  ∑ j, h^2/(8*mass m₁ m₂ j) * (2*directionalDerivative ρ (e j) p *
    directionalDerivative a (e j) p / ρ p - a p*(directionalDerivative ρ (e j) p)^2/(ρ p)^2)

/-- The amplitude-coordinate first variation, with the density test pulled back. -/
def amplitudeVariationOn (e : Index → X) (h m₁ m₂ : ℝ) (R a : X → ℝ) (p : X) : ℝ :=
  ∑ j, (2 * (h^2/(2*mass m₁ m₂ j))) *
    (directionalDerivative (testAmplitude a R) (e j) p * directionalDerivative R (e j) p)

/-- Bohm potential computed from the six genuine second directional derivatives. -/
def quantumOn (e : Index → X) (h m₁ m₂ : ℝ) (R : X → ℝ) (p : X) : ℝ :=
  -(∑ j, h^2/(2*mass m₁ m₂ j) * secondDirectionalDerivative R (e j) p) / R p

/-- The density-coordinate first variation on physical spacetime. -/
abbrev rawVariation := rawVariationOn axis

private theorem dir_affine {ρ a : X → ℝ} {p : X} (hρ : DifferentiableAt ℝ ρ p)
    (ha : DifferentiableAt ℝ a p) (v : X) (s : ℝ) :
    directionalDerivative (fun z => ρ z + s*a z) v p =
      directionalDerivative ρ v p + s*directionalDerivative a v p := by
  simp only [directionalDerivative, fderiv_fun_add hρ (ha.const_mul _), fderiv_const_mul ha,
    add_apply, smul_apply, smul_eq_mul]

/-- Actual derivative along an affine density variation wherever the denominator is nonzero. -/
theorem hasDerivAt_fisherOn_affine (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ} {p : X}
    (hρ : DifferentiableAt ℝ ρ p) (ha : DifferentiableAt ℝ a p) (s : ℝ)
    (hn : ρ p + s*a p ≠ 0) :
    HasDerivAt (fun t => fisherOn e h m₁ m₂ (fun z => ρ z + t*a z) p)
      (rawVariationOn e h m₁ m₂ (fun z => ρ z + s*a z) a p) s := by
  simp only [fisherOn, rawVariationOn, dir_affine hρ ha]
  apply HasDerivAt.fun_sum
  intro j _
  let u := directionalDerivative ρ (e j) p
  let v := directionalDerivative a (e j) p
  have H (r q : ℝ) : HasDerivAt (fun t => r + t*q) q s := by
    simpa using (((hasDerivAt_id s).mul_const q).const_add r)
  apply ((((H u v).pow 2).div (H (ρ p) (a p)) hn).const_mul (h^2/(8*mass m₁ m₂ j))).congr_deriv
  dsimp [u,v]
  field_simp [hn]

/-- Spacetime Fisher-density derivative for a density varied at fixed time and position. -/
theorem hasDerivAt_fisherL_affine (h m₁ m₂ : ℝ) {ρ a : Point → ℝ} {p : Point}
    (hρ : DifferentiableAt ℝ ρ p) (ha : DifferentiableAt ℝ a p) (s : ℝ)
    (hn : ρ p + s*a p ≠ 0) :
    HasDerivAt (fun t => fisherL h m₁ m₂ (fun z => ρ z + t*a z) p)
      (rawVariation h m₁ m₂ (fun z => ρ z + s*a z) a p) s :=
  hasDerivAt_fisherOn_affine axis h m₁ m₂ hρ ha s hn

/-- At a positive square density the raw Fisher variation agrees with the amplitude variation. -/
theorem rawVariationOn_sq_eq_amplitude (e : Index → X) (h m₁ m₂ : ℝ) {R a : X → ℝ}
    (hR : ContDiff ℝ 1 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a) (p : X) :
    rawVariationOn e h m₁ m₂ (fun z => R z^2) a p = amplitudeVariationOn e h m₁ m₂ R a p := by
  have ht := contDiff_testAmplitude ha hR hp
  have hR' := hR.differentiable (by norm_num) p
  have ht' := ht.differentiable (by norm_num) p
  have H : (fun z => (2*R z)*testAmplitude a R z) = a := by
    funext z
    dsimp only [testAmplitude]
    field_simp [(hp z).ne']
  apply Finset.sum_congr rfl
  intro j _
  have htest := congrArg (fun f : X → ℝ => fderiv ℝ f p (e j)) H
  simp only [fderiv_fun_mul (hR'.const_mul 2) ht', fderiv_const_mul hR', add_apply,
    smul_apply, smul_eq_mul] at htest
  have hs : directionalDerivative (fun z => R z^2) (e j) p =
      2*R p*directionalDerivative R (e j) p := by
    simp only [directionalDerivative, pow_two, fderiv_fun_mul hR' hR', add_apply, smul_apply,
      smul_eq_mul]
    ring
  rw [hs]
  simp only [directionalDerivative, ← htest, testAmplitude] at *
  by_cases hm : mass m₁ m₂ j = 0
  · simp [hm]
  · field_simp [(hp p).ne', hm]
    ring

private theorem dir_continuous {f : X → ℝ} (hf : ContDiff ℝ 1 f) (v : X) :
    Continuous (directionalDerivative f v) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

section Integration
variable [MeasureSpace X] [BorelSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]

omit [NormedSpace ℝ X] in
private theorem compact_pair {f g : X → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hg : Continuous g) : Integrable (fun p => f p * g p) :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_right

private theorem green (e : Index → X) (h m₁ m₂ : ℝ) {R a : X → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a)
    (parts : ∀ {q g : X → ℝ}, ContDiff ℝ 1 q → HasCompactSupport q → ContDiff ℝ 1 g →
      ∀ v : X, (∫ p, q p * directionalDerivative g v p) =
        -(∫ p, directionalDerivative q v p * g p)) :
    Integrable (amplitudeVariationOn e h m₁ m₂ R a) ∧
    Integrable (fun p => a p * quantumOn e h m₁ m₂ R p) ∧
    (∫ p, amplitudeVariationOn e h m₁ m₂ R a p) = ∫ p, a p * quantumOn e h m₁ m₂ R p := by
  let q := testAmplitude a R
  let g (j : Index) := directionalDerivative R (e j)
  let k (j : Index) := h^2/(2*mass m₁ m₂ j)
  have hq : ContDiff ℝ 1 q := contDiff_testAmplitude ha (hR.of_le (by norm_num)) hp
  have cq : HasCompactSupport q := compact_testAmplitude hc
  have hg (j : Index) : ContDiff ℝ 1 (g j) :=
    (hR.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hl (j : Index) : Integrable (fun p => (2*k j)*(directionalDerivative q (e j) p*g j p)) :=
    (compact_pair (dir_continuous hq _) (cq.fderiv_apply ℝ _) (hg j).continuous).const_mul _
  have hr (j : Index) : Integrable (fun p => (2*k j)*(q p*directionalDerivative (g j) (e j) p)) :=
    (compact_pair hq.continuous cq (dir_continuous (hg j) _)).const_mul _
  have hpoint : (fun p => a p * quantumOn e h m₁ m₂ R p) =
      fun p => -(∑ j, (2*k j)*(q p*directionalDerivative (g j) (e j) p)) := by
    funext p
    change a p * (-(∑ j, k j * directionalDerivative (g j) (e j) p) / R p) = _
    rw [show a p * (-(∑ j, k j * directionalDerivative (g j) (e j) p) / R p) =
      -((a p / R p) * (∑ j, k j * directionalDerivative (g j) (e j) p)) by ring,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [q, testAmplitude]
    field_simp [(hp p).ne']
  refine ⟨integrable_finsetSum _ (fun j _ => hl j), ?_, ?_⟩
  · rw [hpoint]
    exact (integrable_finsetSum _ (fun j _ => hr j)).neg
  · change (∫ p, ∑ j, (2*k j)*(directionalDerivative q (e j) p*g j p)) = _
    rw [hpoint, integral_neg, integral_finsetSum _ (fun j _ => hl j),
      integral_finsetSum _ (fun j _ => hr j), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_const_mul, parts hq cq (hg j) (e j)]
    ring

end Integration

/-- Compact tests make the Fisher amplitude pairing integrable on spacetime. -/
theorem integrable_amplitudeVariation (h m₁ m₂ : ℝ) {R a : Point → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) : Integrable (amplitudeVariationOn axis h m₁ m₂ R a) :=
  (green axis h m₁ m₂ hR hp ha hc TwoBodyPolarContinuity.compact_test_parts).1

/-- A compact test times the quantum potential is integrable on spacetime. -/
theorem integrable_test_quantum (h m₁ m₂ : ℝ) {R a : Point → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) : Integrable (fun p => a p * quantum h m₁ m₂ R p) :=
  (green axis h m₁ m₂ hR hp ha hc TwoBodyPolarContinuity.compact_test_parts).2.1

/-- Integration by parts identifies the amplitude pairing with the tested Bohm potential. -/
theorem integral_amplitudeVariation (h m₁ m₂ : ℝ) {R a : Point → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    (∫ p, amplitudeVariationOn axis h m₁ m₂ R a p) = ∫ p, a p * quantum h m₁ m₂ R p :=
  (green axis h m₁ m₂ hR hp ha hc TwoBodyPolarContinuity.compact_test_parts).2.2

/-- The density-coordinate Fisher variation on a positive square is integrable. -/
theorem integrable_rawVariation_sq (h m₁ m₂ : ℝ) {R a : Point → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) : Integrable (rawVariation h m₁ m₂ (fun z => R z^2) a) := by
  unfold rawVariation
  simpa only [← funext (rawVariationOn_sq_eq_amplitude axis h m₁ m₂ (hR.of_le (by norm_num)) hp ha)]
    using integrable_amplitudeVariation h m₁ m₂ hR hp ha hc

/-- The raw density variation integrated on spacetime is the Bohm first variation. -/
theorem integral_rawVariation_sq (h m₁ m₂ : ℝ) {R a : Point → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    (∫ p, rawVariation h m₁ m₂ (fun z => R z^2) a p) = ∫ p, a p * quantum h m₁ m₂ R p := by
  simpa only [rawVariation, rawVariationOn_sq_eq_amplitude axis h m₁ m₂
    (hR.of_le (by norm_num)) hp ha] using integral_amplitudeVariation h m₁ m₂ hR hp ha hc

/-- Six Cartesian axes on configuration space at fixed physical time. -/
def spatialAxis : Index → Spatial × Spatial :=
  Sum.elim (fun i => (ObserverGaussianFisher.axes i, 0)) (fun i => (0, ObserverGaussianFisher.axes i))

private theorem spatial_parts {q g : Spatial × Spatial → ℝ} (hq : ContDiff ℝ 1 q)
    (cq : HasCompactSupport q) (hg : ContDiff ℝ 1 g) (v : Spatial × Spatial) :
    (∫ p, q p * directionalDerivative g v p) = -(∫ p, directionalDerivative q v p * g p) := by
  let : (volume : Measure (Spatial × Spatial)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure Spatial) (volume : Measure Spatial)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (compact_pair (dir_continuous hq v) (cq.fderiv_apply ℝ v) hg.continuous)
    (compact_pair hq.continuous cq (dir_continuous hg v))
    (compact_pair hq.continuous cq hg.continuous)
    (fun x _ => hq.differentiable (by norm_num) x) (fun x _ => hg.differentiable (by norm_num) x)

/-- Both sides of the fixed-time Green identity are integrable on configuration space. -/
theorem integrable_spatial_rawVariation_sq (h m₁ m₂ : ℝ) {R a : Spatial × Spatial → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    Integrable (rawVariationOn spatialAxis h m₁ m₂ (fun z => R z^2) a) ∧
    Integrable (fun p => a p * quantumOn spatialAxis h m₁ m₂ R p) := by
  have H := green spatialAxis h m₁ m₂ hR hp ha hc spatial_parts
  refine ⟨?_, H.2.1⟩
  rw [funext (rawVariationOn_sq_eq_amplitude spatialAxis h m₁ m₂ (hR.of_le (by norm_num)) hp ha)]
  exact H.1

/-- Six-dimensional integration by parts gives the fixed-time functional derivative. -/
theorem integral_spatial_rawVariation_sq (h m₁ m₂ : ℝ) {R a : Spatial × Spatial → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    (∫ p, rawVariationOn spatialAxis h m₁ m₂ (fun z => R z^2) a p) =
      ∫ p, a p * quantumOn spatialAxis h m₁ m₂ R p := by
  simp_rw [rawVariationOn_sq_eq_amplitude spatialAxis h m₁ m₂ (hR.of_le (by norm_num)) hp ha]
  exact (green spatialAxis h m₁ m₂ hR hp ha hc spatial_parts).2.2

end FoliationQM.TwoBodyBohmGreen
