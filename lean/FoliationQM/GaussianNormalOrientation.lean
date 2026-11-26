module

public import FoliationQM.GaussianCauchySlice
public import FoliationQM.GaussianCosineTest
public import FoliationQM.GaussianSpectralWitness

/-!
# Orientation of a real initial wave with imaginary normal derivative

The ADM domain in v13 lines 752–767 requires positive normal momentum. For a
real positive initial wave R and normal derivative −iH, both the scalar
current and the polar momentum detect the sign of the real coefficient H.
This allows a spectral test on H to address the actual physical domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianNormalOrientation
open LorentzCoordinates OsmoticSliceFields GaussianCauchySlice PolarSecondDifferential
open ActionDensity ObserverFluxDensity ScalarPhaseCurrent DressedMassDensityVariation
open scoped ComplexConjugate

/-- The normal component of the Noether current at a real initial value R with
normal derivative −iH is precisely (ℏ/m)RH in the lower-index convention. -/
theorem current_normal (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector} {R H : ℝ}
    (hv : ψ x = (R : ℂ))
    (hd : directionalDerivative ψ (Madelung.coordinateVector 0) x = -Complex.I * H) :
    current p ψ x 0 = (p.hbar / p.m) * R * H := by
  unfold current
  rw [hv, hd]
  simp [Complex.mul_im]
  ring

/-- On a positive real initial profile the sign of its normal current is exactly the
sign of the normal coefficient H; the equivalence includes sign-zero points. -/
theorem current_normal_sign (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector} {R H : ℝ}
    (hR : 0 < R) (hv : ψ x = (R : ℂ))
    (hd : directionalDerivative ψ (Madelung.coordinateVector 0) x = -Complex.I * H) :
    (0 < current p ψ x 0 ↔ 0 < H) ∧ (current p ψ x 0 < 0 ↔ H < 0) ∧
      (current p ψ x 0 = 0 ↔ H = 0) := by
  rw [current_normal p hv hd]
  have h := mul_pos (div_pos p.hbar_pos p.m_pos) hR
  simp [h, h.ne', mul_neg_iff, not_lt.mpr h.le]

/-- Differentiating the polar wave with normal datum −iH gives zero normal log-density
score and the signed temporal phase momentum ℏH/R, even when H vanishes. -/
theorem polar_normal (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector} {R H : ℝ}
    (hr : DifferentiableAt ℝ ρ x) (hs : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (hR : 0 < R)
    (hv : actionField p ρ S x = (R : ℂ))
    (hd : directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) x =
      -Complex.I * H) :
    normalScore ρ x = 0 ∧ normalMomentum S x = p.hbar * (H/R) := by
  have h : directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) x =
      actionField p ρ S x * (((0 : ℝ) : ℂ) - Complex.I * ((H/R : ℝ) : ℂ)) := by
    rw [hd, hv]
    push_cast
    have hne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp [hne]
    ring
  simpa using normal_data p hr hs hp 0 (H/R) h

/-- The spatial wave vector on the first laboratory coordinate axis. -/
def axis (q : ℝ) : Spatial := Pi.single 0 q

private theorem axis_scale (q : ℝ) : (2 : ℝ) • axis q = axis (2*q) := by
  ext i
  fin_cases i <;> simp [axis]

/-- If an integrable coefficient has the prescribed one-Compton positive-frequency
spectrum on one axis, a set of positive spatial volume has negative coefficient. -/
theorem negative_volume {H : Spatial → ℝ} {C μ σ : ℝ} (hH : MeasureTheory.Integrable H)
    (hC : 0 < C) (hμ : 0 < μ) (hσμ : σ*μ=1)
    (hspec : ∀ q, GaussianCosineTest.cosineTransform H (axis q) =
      GaussianSpectralWitness.profile C μ σ q) :
    0 < MeasureTheory.volume {y : Spatial | H y < 0} := by
  apply GaussianCosineTest.volume_neg_pos_of_difference_neg hH (u := axis (μ/4))
  have hz : axis 0 = 0 := by simp [axis]
  rw [GaussianCosineTest.difference, ← hz, axis_scale, hspec, hspec, hspec]
  exact GaussianSpectralWitness.compton_difference_neg hC hμ hσμ

/-- The scalar current of a Gaussian field with that integrable normal coefficient
is past-directed in its temporal component on a set of positive spatial volume. -/
theorem past_current_positive_volume (p : MassiveParameters) {ψ : Covector → ℂ}
    {H : Spatial → ℝ} {C μ σ : ℝ} (hH : MeasureTheory.Integrable H)
    (hC : 0 < C) (hμ : 0 < μ) (hσμ : σ*μ=1)
    (hspec : ∀ q, GaussianCosineTest.cosineTransform H (axis q) =
      GaussianSpectralWitness.profile C μ σ q)
    (hv : ∀ y, ψ (slicePoint 0 y) = (amplitude σ y : ℂ))
    (hd : ∀ y, directionalDerivative ψ (Madelung.coordinateVector 0) (slicePoint 0 y) =
      -Complex.I * H y) :
    0 < MeasureTheory.volume {y : Spatial | current p ψ (slicePoint 0 y) 0 < 0} := by
  have he : {y : Spatial | current p ψ (slicePoint 0 y) 0 < 0} = {y | H y < 0} := by
    ext y
    exact (current_normal_sign p (amplitude_pos σ y) (hv y) (hd y)).2.1
  rw [he]
  exact negative_volume hH hC hμ hσμ hspec

end FoliationQM.GaussianNormalOrientation
