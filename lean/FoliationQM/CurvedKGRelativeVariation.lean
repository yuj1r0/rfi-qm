module

public import FoliationQM.CurvedKGTestResidual

/-!
# The integrated first variation of the curved scalar action

On an open chart, a compactly supported field variation changes the
Klein–Gordon density by an integrable quadratic polynomial in the real
variation parameter. Integration of its two coefficients gives an actual
derivative of the relative action. A finite background action also admits
the ordinary absolute-action derivative.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedKGRelativeVariation

open LorentzMatrixGroup RNCVolumeDensity CurvedPolarAction CurvedKGFirstVariation
open MeasureTheory
open scoped Matrix.Norms.Operator

/-- The relative action integrates the volume-weighted change of density for a real affine field variation. -/
def relativeAction (p : MassiveParameters) (g : Covector → Mat4) (ψ η : Covector → ℂ)
    (U : Set Covector) (t : ℝ) : ℝ :=
  ∫ x in U, volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x)

variable (p : MassiveParameters) {U : Set Covector} {g : Covector → Mat4} {ψ η : Covector → ℂ}
    (hU : IsOpen U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hs : ∀ x ∈ U, (g x).IsSymm)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) (hsupp : tsupport η ⊆ U)

include hg hd hψ hη hc hsupp in
/-- The integrable coefficients of the relative action are the weighted real cross pairing
and the weighted self-density of the compact test field. -/
theorem integrable_coefficients :
    IntegrableOn (fun x => volumeFactor (g x) * (cross p g η ψ x).re) U ∧
    IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g η x) U := by
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by decide)
  refine ⟨CurvedKGTestResidual.integrable_cross_re p hη₁ hc hsupp hg hd hψ, ?_⟩
  simpa only [cross_self_re] using
    CurvedKGTestResidual.integrable_cross_re p hη₁ hc hsupp hg hd (fun x _ => hη.contDiffAt (x := x))

include hs hψ hη in
/-- On the integration region the actual density increment is exactly its linear and quadratic terms. -/
private theorem increment_eq (t : ℝ) : Set.EqOn
    (fun x => volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x))
    (fun x => (2 * t) * (volumeFactor (g x) * (cross p g η ψ x).re) +
      t ^ 2 * (volumeFactor (g x) * kgDensity p g η x)) U := by
  intro x hx
  dsimp only
  rw [density_perturb p (hs x hx) ((hψ x hx).differentiableAt (by decide))
    (hη.contDiffAt.differentiableAt (by decide))]
  ring

include hU hg hs hd hψ hη hc hsupp in
/-- Every finite-parameter density difference is integrable under the compact-interior test hypotheses. -/
theorem integrable_difference (t : ℝ) :
    IntegrableOn (fun x => volumeFactor (g x) * (kgDensity p g (perturb ψ η t) x - kgDensity p g ψ x)) U := by
  obtain ⟨h₁, h₂⟩ := integrable_coefficients p hg hd hψ hη hc hsupp
  apply ((h₁.const_mul (2 * t)).add (h₂.const_mul (t ^ 2))).congr
  exact (ae_restrict_mem hU.measurableSet).mono fun x hx => (increment_eq p hs hψ hη t hx).symm

include hU hg hs hd hψ hη hc hsupp in
/-- The exact relative action is a quadratic polynomial for every real parameter,
with the two coefficients obtained by integrating the local density expansion. -/
theorem relativeAction_eq (t : ℝ) :
    relativeAction p g ψ η U t =
      2 * t * (∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) + t ^ 2 * kgAction p g η U := by
  obtain ⟨h₁, h₂⟩ := integrable_coefficients p hg hd hψ hη hc hsupp
  unfold relativeAction kgAction
  rw [setIntegral_congr_fun hU.measurableSet (increment_eq p hs hψ hη t),
    integral_add (h₁.const_mul (2 * t)) (h₂.const_mul (t ^ 2)), integral_const_mul, integral_const_mul]

include hU hg hs hd hψ hη hc hsupp in
/-- Differentiating the integrated relative action gives the integrated real cross pairing. -/
theorem hasDerivAt_relative : HasDerivAt (relativeAction p g ψ η U)
    (2 * ∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) 0 := by
  simp_rw [show relativeAction p g ψ η U = _ from
    funext (relativeAction_eq p hU hg hs hd hψ hη hc hsupp)]
  convert! (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
    (∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (kgAction p g η U)) using 1
  simp

include hU hg hs hd hψ hη hc hsupp in
/-- For an integrable background the absolute action equals the background action plus its relative change. -/
theorem absolute_eq (hfin : IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g ψ x) U) (t : ℝ) :
    kgAction p g (perturb ψ η t) U = relativeAction p g ψ η U t + kgAction p g ψ U := by
  have hi := integrable_difference p hU hg hs hd hψ hη hc hsupp t
  unfold kgAction relativeAction
  rw [← integral_add hi hfin]
  exact setIntegral_congr_fun hU.measurableSet fun x _ => by ring

include hU hg hs hd hψ hη hc hsupp in
/-- A finite absolute action has the same first variation for each compactly supported interior test. -/
theorem hasDerivAt_absolute (hfin : IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g ψ x) U) :
    HasDerivAt (fun t => kgAction p g (perturb ψ η t) U)
      (2 * ∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) 0 := by
  simp_rw [absolute_eq p hU hg hs hd hψ hη hc hsupp hfin]
  exact (hasDerivAt_relative p hU hg hs hd hψ hη hc hsupp).add_const _

end FoliationQM.CurvedKGRelativeVariation
