module

public import FoliationQM.TwoParticleGaussianModel
public import FoliationQM.TwoParticleFisher
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A pure state with a product density and a nonseparable phase

The two Gaussian amplitudes are multiplied by exp(iπ x₀ y₀). The density
has independent marginals and zero conditional Fisher excess. Four values
of the continuous wave rule out even an almost-everywhere product of two
single-particle wave functions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PhaseOnlyEntanglement

open MeasureTheory LorentzCoordinates TwoParticleGaussianModel TwoParticleMarginals
open TwoParticleFisher FisherNormalization ConditionalScoreCentering
open scoped ContDiff

/-- Positive real amplitude of one normalized standard spatial Gaussian. -/
def amplitude (x : Spatial) : ℝ := Real.sqrt (gaussian 1 x)

private theorem amplitude_pos (x : Spatial) : 0 < amplitude x :=
  Real.sqrt_pos.mpr (gaussian_pos one_pos x)

/-- Two real Gaussian amplitudes times a unit complex phase coupling their first coordinates. -/
def wave (z : Spatial × Spatial) : ℂ :=
  ((amplitude z.1 * amplitude z.2 : ℝ) : ℂ) * Complex.exp (((Real.pi * z.1 0 * z.2 0 : ℝ) : ℂ) * Complex.I)

/-- The coupled complex wave is smooth jointly in both spatial positions. -/
theorem wave_smooth : ContDiff ℝ ∞ wave := by
  have ha : ContDiff ℝ ∞ amplitude := (gaussian_smooth 1).sqrt (fun x => (gaussian_pos one_pos x).ne')
  have hp : ContDiff ℝ ∞ (fun z : Spatial × Spatial => Real.pi * z.1 0 * z.2 0) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp ((ha.comp contDiff_fst).mul (ha.comp contDiff_snd))).mul
    (((Complex.ofRealCLM.contDiff.comp hp).mul (contDiff_const (c := Complex.I))).cexp)

/-- The squared modulus of the complex pure-state wave. -/
def density (z : Spatial × Spatial) : ℝ := Complex.normSq (wave z)

/-- The modulus square is the product of the two normalized unit-width Gaussians. -/
theorem density_eq (x y : Spatial) : density (x,y) = gaussian 1 x * gaussian 1 y := by
  simp only [density, wave, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, sq_abs, mul_pow, amplitude,
    Real.sq_sqrt (gaussian_pos one_pos _).le]

/-- The spatial probability density is positive everywhere. -/
theorem density_pos (z : Spatial × Spatial) : 0 < density z :=
  (density_eq z.1 z.2).symm ▸ mul_pos (gaussian_pos one_pos _) (gaussian_pos one_pos _)

/-- The squared modulus is integrable on the full configuration space. -/
theorem density_integrable : Integrable density := by
  have he : density = fun z => gaussian 1 z.1 * gaussian 1 z.2 := funext fun z => density_eq z.1 z.2
  rw [he]
  exact (gaussian_integrable one_pos).mul_prod (gaussian_integrable one_pos)

/-- The six-dimensional probability mass of the wave equals one. -/
theorem normalized : (∫ z, density z) = 1 := by
  change (∫ z, density z ∂(volume.prod volume)) = 1
  rw [integral_prod density density_integrable]
  simp only [density_eq, integral_const_mul, integral_gaussian one_pos, mul_one]

/-- The smooth wave represents a square-integrable pure state. -/
theorem square_integrable : MemLp wave 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm wave_smooth.continuous.aestronglyMeasurable).2
  simp only [← Complex.normSq_eq_norm_sq]
  exact density_integrable

/-- Both actual integrated marginals are standard spatial Gaussian densities. -/
theorem marginals : left density = gaussian 1 ∧ right density = gaussian 1 := by
  constructor <;> funext x
  · simp only [left, density_eq, integral_const_mul, integral_gaussian one_pos, mul_one]
  · simp only [right, density_eq, integral_mul_const, integral_gaussian one_pos, one_mul]

/-- The two spatial outcomes are independent at the level of the wave's actual squared modulus. -/
theorem factorized_density (x y : Spatial) : density (x,y) = left density x * right density y := by
  rw [marginals.1, marginals.2, density_eq]

/-- Conditioning on the first position preserves the full second Gaussian law. -/
theorem conditional_eq (x y : Spatial) : conditional density x y = gaussian 1 y := by
  rw [conditional, marginals.1, density_eq]
  field_simp [(gaussian_pos one_pos x).ne']

/-- The physical spatial-amplitude excess of this wave vanishes for all parameter values. -/
theorem excess_zero (hbar m : ℝ) : excess hbar m density = 0 := by
  simp [excess, excessDensity, condScore, score, conditional_eq]

private theorem extend {f g : Spatial → ℂ} (he : f =ᵐ[volume] g) (hf : Continuous f)
    (hg : Continuous g) (x : Spatial) : f x = g x := congrFun (Measure.eq_of_ae_eq he hf hg) x

/-- Every continuous wave with an almost-everywhere product representation satisfies
the four-point identity everywhere, including on individual measure-zero slices. -/
theorem rectangle_of_product_ae {ψ : Spatial × Spatial → ℂ} {a b : Spatial → ℂ}
    (hψ : Continuous ψ) (he : ψ =ᵐ[volume] (fun z => a z.1 * b z.2)) (x x' y y' : Spatial) :
    ψ (x,y) * ψ (x',y') = ψ (x,y') * ψ (x',y) := by
  have good : ∀ᵐ u : Spatial, ∀ᵐ v : Spatial, ψ (u,v) = a u * b v := Measure.ae_ae_of_ae_prod he
  apply extend (f := fun s => ψ (s,y) * ψ (x',y')) (g := fun s => ψ (s,y') * ψ (x',y)) _ (by fun_prop) (by fun_prop) x
  filter_upwards [good] with s hs
  apply extend (f := fun t => ψ (s,y) * ψ (t,y')) (g := fun t => ψ (s,y') * ψ (t,y)) _ (by fun_prop) (by fun_prop) x'
  filter_upwards [good] with t ht
  apply extend (f := fun u => ψ (s,u) * ψ (t,y')) (g := fun u => ψ (s,y') * ψ (t,u)) _ (by fun_prop) (by fun_prop) y
  filter_upwards [hs, ht] with u hsu htu
  apply extend (f := fun v => ψ (s,u) * ψ (t,v)) (g := fun v => ψ (s,v) * ψ (t,u)) _ (by fun_prop) (by fun_prop) y'
  filter_upwards [hs, ht] with v hsv htv
  rw [hsu, htu, hsv, htv]
  ring

/-- The normalized smooth wave has no pure-product representation,
even up to sets of six-dimensional Lebesgue measure zero. -/
theorem not_product_ae : ¬ ∃ a b : Spatial → ℂ, wave =ᵐ[volume] (fun z => a z.1 * b z.2) := by
  rintro ⟨a, b, hp⟩
  have h := rectangle_of_product_ae wave_smooth.continuous hp 0 1 0 1
  simp [wave, Complex.exp_pi_mul_I] at h
  have h' := congrArg Complex.re h
  simp at h'
  nlinarith only [h', mul_pos (sq_pos_of_pos (amplitude_pos 0)) (sq_pos_of_pos (amplitude_pos 1))]

end FoliationQM.PhaseOnlyEntanglement
