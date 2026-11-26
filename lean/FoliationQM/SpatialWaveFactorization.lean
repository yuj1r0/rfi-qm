module

public import FoliationQM.FisherEquality

/-!
# Product waves and marginal densities

An almost-everywhere scalar product wave has a product Born density.
Normalization identifies the factors as the two marginals up to reciprocal
constants. Positive spatial Fisher excess therefore rules out an almost-
everywhere product wave, including for Hilbert-space representatives.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpatialWaveFactorization

open MeasureTheory MeasureTheory.Measure LorentzCoordinates TwoParticleMarginals MarginalDifferentiation TwoParticleFisher

variable {f : Spatial × Spatial → ℝ}

/-- An almost-everywhere real product representation of a normalized regular density
gives pointwise factorization into its actual marginal densities. -/
theorem marginals_of_ae_product (H : Regular f) {a b : Spatial → ℝ}
    (hab : f =ᵐ[volume] fun z => a z.1 * b z.2) :
    ∀ x y, f (x,y) = left f x * right f y := by
  have hm : (∫ x, a x) * (∫ y, b y) = 1 := by
    calc
      _ = ∫ z : Spatial × Spatial, a z.1 * b z.2 := (integral_prod_mul a b).symm
      _ = ∫ z, f z := integral_congr_ae hab.symm
      _ = 1 := H.mass_one
  have hl : left f =ᵐ[volume] fun x => a x * ∫ y, b y := by
    filter_upwards [ae_ae_of_ae_prod hab] with x hx
    exact (integral_congr_ae hx).trans (integral_const_mul _ _)
  have hswap : swap f =ᵐ[volume] fun z => a z.2 * b z.1 :=
    measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hab
  have hr : right f =ᵐ[volume] fun y => (∫ x, a x) * b y := by
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    exact (integral_congr_ae hy).trans (integral_mul_const _ _)
  apply (ConditionalDensityRigidity.factorization_iff_ae H).mpr
  filter_upwards [hab, quasiMeasurePreserving_fst.ae_eq_comp hl,
    quasiMeasurePreserving_snd.ae_eq_comp hr] with z hz hx hy
  change left f z.1 = a z.1 * ∫ y, b y at hx
  change right f z.2 = (∫ x, a x) * b z.2 at hy
  rw [hz, hx, hy]
  calc
    a z.1 * b z.2 = (a z.1 * b z.2) * ((∫ x, a x) * (∫ y, b y)) := by rw [hm, mul_one]
    _ = _ := by ring

/-- Positive spatial Fisher excess excludes every almost-everywhere product representation
of a complex scalar wave with the prescribed Born density. -/
theorem no_product_wave_of_excess_pos (H : Regular f) {hbar m₁ m₂ : ℝ}
    (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity hbar m₁ m₂ f)) (he : 0 < excess hbar m₁ f)
    {ψ : Spatial × Spatial → ℂ} (hd : f =ᵐ[volume] fun z => Complex.normSq (ψ z)) :
    ¬ ∃ u v : Spatial → ℂ, ψ =ᵐ[volume] fun z => u z.1 * v z.2 := by
  rintro ⟨u, v, hu⟩
  apply (FisherEquality.excess_pos_iff_not_factorized H hh hm₁ hm₂ hJ).mp he
  apply marginals_of_ae_product H (a := fun x => Complex.normSq (u x)) (b := fun y => Complex.normSq (v y))
  filter_upwards [hd, hu] with z hz hψ
  rw [hz, hψ, Complex.normSq_mul]

end FoliationQM.SpatialWaveFactorization
