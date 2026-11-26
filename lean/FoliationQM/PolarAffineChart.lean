module

public import FoliationQM.CompactPerturbation
public import FoliationQM.PolarLocalInverse
public import FoliationQM.PolarTestVariations

/-!
# Polar coordinates of affine complex variations

Source: v13 `thm:kahler`. On a supplied positive-density real-phase chart,
each compact complex test produces an exact nonlinear density/phase family.
Compactness supplies one parameter interval on which positivity and spatial
smoothness hold everywhere. The reconstructed field is the original affine
complex curve, with coordinate changes supported inside the original test.
The phase is relative to the supplied chart; no global phase across nodes or
nonzero winding is asserted.
-/
@[expose] public section

namespace FoliationQM.PolarAffineChart

open ActionDensity PolarDifferential PolarLocalInverse PolarTestVariations
open CompactPerturbation

variable {E : Type*}

/-- The actual Born density of the affine complex curve. -/
noncomputable def curveDensity (p : MassiveParameters) (ρ S : E → ℝ)
    (η : E → ℂ) (t : ℝ) (x : E) : ℝ :=
  Complex.normSq (actionField p ρ S x + (t : ℂ) * η x)

/-- A relative logarithmic phase, retaining the supplied background real lift. -/
noncomputable def curveAction (p : MassiveParameters) (ρ S : E → ℝ)
    (η : E → ℂ) (t : ℝ) (x : E) : ℝ :=
  S x + p.hbar * (Complex.log (1 + (t : ℂ) * η x / actionField p ρ S x)).im

/-- The recovered family starts at the supplied density. -/
theorem curveDensity_zero (p : MassiveParameters) (ρ S : E → ℝ) (η : E → ℂ)
    (x : E) (hpos : 0 ≤ ρ x) : curveDensity p ρ S η 0 x = ρ x := by
  simp only [curveDensity, Complex.ofReal_zero, zero_mul, add_zero, actionField]
  exact polarField_normSq ρ _ x hpos

/-- The recovered action phase starts at the supplied real lift exactly. -/
theorem curveAction_zero (p : MassiveParameters) (ρ S : E → ℝ) (η : E → ℂ)
    (x : E) : curveAction p ρ S η 0 x = S x := by
  simp [curveAction]

/-- Exact reconstruction of the affine complex curve. This algebraic identity
holds even when the perturbed value vanishes; admissible smooth coordinates
are supplied separately on a uniform parameter interval. -/
theorem curve_reconstruction (p : MassiveParameters) (ρ S : E → ℝ) (η : E → ℂ)
    (t : ℝ) (x : E) (hpos : 0 < ρ x) :
    actionField p (curveDensity p ρ S η t) (curveAction p ρ S η t) x =
      actionField p ρ S x + (t : ℂ) * η x := by
  let ψ := actionField p ρ S x
  let q := 1 + (t : ℂ) * η x / ψ
  have hnormsq : Complex.normSq ψ = ρ x := polarField_normSq ρ _ x hpos.le
  have hnz : ψ ≠ 0 := Complex.normSq_pos.mp (by rwa [hnormsq])
  have hfactor : ψ * q = ψ + (t : ℂ) * η x := by
    dsimp [q]
    field_simp [hnz]
  have hnormψ : ‖ψ‖ = Real.sqrt (ρ x) := by rw [Complex.norm_def, hnormsq]
  have hnorm : Real.sqrt (curveDensity p ρ S η t x) = Real.sqrt (ρ x) * ‖q‖ := by
    change Real.sqrt (Complex.normSq (ψ + (t : ℂ) * η x)) = _
    rw [← Complex.norm_def, ← hfactor, norm_mul, hnormψ]
  have hphase : (S x + p.hbar * (Complex.log q).im) / p.hbar =
      S x / p.hbar + (Complex.log q).im := by field_simp [ne_of_gt p.hbar_pos]
  change (Real.sqrt (curveDensity p ρ S η t x) : ℂ) *
    phase ((S x + p.hbar * (Complex.log q).im) / p.hbar) = _
  rw [hnorm, hphase]
  have hadd (a b : ℝ) : phase (a + b) = phase a * phase b := by
    simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [hadd, Complex.ofReal_mul]
  calc
    _ = ψ * ((‖q‖ : ℂ) * phase (Complex.log q).im) := by
      dsimp [ψ, actionField, polarField]
      ring
    _ = ψ * q := by rw [norm_mul_phase_log]
    _ = _ := hfactor

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The recovered Born density has the spatial regularity of the background
and complex variation, even beyond the interval where it is positive. -/
theorem contDiff_curveDensity (p : MassiveParameters) {ρ S : E → ℝ} {η : E → ℂ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hS : ContDiff ℝ n S)
    (hpos : ∀ x, 0 < ρ x) (hη : ContDiff ℝ n η) (t : ℝ) :
    ContDiff ℝ n (curveDensity p ρ S η t) :=
  (contDiff_normSq n).comp
    ((contDiff_actionField p hρ hS hpos).add (contDiff_const.mul hη))

/-- For each compact complex variation, a single parameter interval gives
positive density and smooth real coordinates throughout the spatial domain. -/
theorem exists_admissible_curve (p : MassiveParameters) {ρ S : E → ℝ} {η : E → ℂ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hS : ContDiff ℝ n S)
    (hpos : ∀ x, 0 < ρ x) (hη : ContDiff ℝ n η) (hc : HasCompactSupport η) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      (∀ x, 0 < curveDensity p ρ S η t x) ∧
      ContDiff ℝ n (curveDensity p ρ S η t) ∧
      ContDiff ℝ n (curveAction p ρ S η t) := by
  have hψ := contDiff_actionField p hρ hS hpos
  have hnz : ∀ x, actionField p ρ S x ≠ 0 := by
    intro x
    apply Complex.normSq_pos.mp
    rw [actionField, polarField_normSq ρ _ x (hpos x).le]
    exact hpos x
  obtain ⟨ε, hε, hslit⟩ := exists_slitPlane_affine_ratio hψ.continuous hnz hη.continuous hc
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hfactor (x : E) : actionField p ρ S x *
      (1 + (t : ℂ) * η x / actionField p ρ S x) =
      actionField p ρ S x + (t : ℂ) * η x := by field_simp [hnz x]
  refine ⟨?_, contDiff_curveDensity p hρ hS hpos hη t, ?_⟩
  · intro x
    apply Complex.normSq_pos.mpr
    rw [← hfactor x]
    exact mul_ne_zero (hnz x) (Complex.slitPlane_ne_zero (hslit t ht x))
  · have htη : ContDiff ℝ n (fun x => (t : ℂ) * η x) := contDiff_const.mul hη
    have hquot : ContDiff ℝ n (fun x => (t : ℂ) * η x / actionField p ρ S x) :=
      by simpa only [div_eq_mul_inv, Pi.inv_apply] using htη.mul (hψ.inv hnz)
    have hratio : ContDiff ℝ n (fun x => 1 + (t : ℂ) * η x / actionField p ρ S x) :=
      contDiff_const.add hquot
    have hlog : ContDiff ℝ n (fun x =>
        Complex.log (1 + (t : ℂ) * η x / actionField p ρ S x)) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact ((Complex.contDiffAt_log (hslit t ht x)).restrict_scalars ℝ).comp x
        hratio.contDiffAt
    exact hS.add (contDiff_const.mul (Complex.imCLM.contDiff.comp hlog))

omit [NormedSpace ℝ E] in
/-- Recovered density changes introduce no support outside the complex test. -/
theorem hasCompactSupport_curveDensity_sub (p : MassiveParameters) {ρ S : E → ℝ}
    {η : E → ℂ} (hpos : ∀ x, 0 ≤ ρ x) (hc : HasCompactSupport η) (t : ℝ) :
    HasCompactSupport (fun x => curveDensity p ρ S η t x - ρ x) := by
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
  simp only [curveDensity, hx, mul_zero, add_zero, actionField,
    polarField_normSq ρ _ x (hpos x), sub_self]

omit [NormedSpace ℝ E] in
/-- Recovered real-phase changes introduce no support outside the complex test. -/
theorem hasCompactSupport_curveAction_sub (p : MassiveParameters) (ρ S : E → ℝ)
    {η : E → ℂ} (hc : HasCompactSupport η) (t : ℝ) :
    HasCompactSupport (fun x => curveAction p ρ S η t x - S x) := by
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
  simp [curveAction, hx]

end FoliationQM.PolarAffineChart
