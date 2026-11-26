module

public import FoliationQM.LatticeMidpointCurrent
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Interior site current from the two incident links

The numerator of the site velocity in v13 lines 224–226 averages the
rightward currents through the two faces. At an interior site with smooth
physical samples on both sides, this average is exactly a centered
difference quotient in the sampling width.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeCenteredSiteCurrent

open LatticeLinkCurrent Filter
open scoped Topology Asymptotics

/-- Mean of the outgoing and incoming rightward currents at the physical site x. -/
def centered (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (link p h (R x) (R (x + h)) ((p.c / p.ellC) * τ x) ((p.c / p.ellC) * τ (x + h)) +
    link p h (R (x - h)) (R x) ((p.c / p.ellC) * τ (x - h)) ((p.c / p.ellC) * τ x)) / 2

/-- Smooth oriented-current numerator from the site to its displaced sample. -/
def numerator (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (p.ellC * p.c * R x) * R (x + h) * Real.sin ((p.c / p.ellC) * (τ (x + h) - τ x))

/-- The discrete incident-link average equals the centered difference of one smooth numerator. -/
theorem centered_eq_quotient (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) :
    centered p R τ x h = (numerator p R τ x h - numerator p R τ x (-h)) / (2 * h) := by
  simp only [centered, link, numerator, ← sub_eq_add_neg, ← mul_sub]
  rw [← neg_sub (τ (x - h)) (τ x), mul_neg, Real.sin_neg]
  ring

/-- C³ spatial profiles give a C³ numerator as the displacement varies. -/
theorem numerator_contDiff (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) : ContDiff ℝ 3 (numerator p R τ x) := by
  unfold numerator
  fun_prop

/-- The numerator derivative at zero displacement is the physical continuum current. -/
theorem numerator_derivative (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : DifferentiableAt ℝ R x) (hτ : DifferentiableAt ℝ τ x) :
    HasDerivAt (numerator p R τ x) (p.c ^ 2 * (R x) ^ 2 * deriv τ x) 0 := by
  have shift {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f x) :
      HasDerivAt (fun h => f (x + h)) (deriv f x) 0 := by
    have hd : HasDerivAt f (deriv f x) (x + 0) := by simpa using hf.hasDerivAt
    simpa only [Function.comp_def, id_eq, mul_one] using
      hd.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add x)
  apply (((shift hR).const_mul (p.ellC * p.c * R x)).mul
    (((shift hτ).sub_const (τ x)).const_mul (p.c / p.ellC)).sin).congr_deriv
  simp
  field_simp [(ClockScales.ellC_pos p).ne']

/-- The site mean of the two physical link currents has second-order error
as positive sampling width tends to zero. -/
theorem centered_error (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) :
    (fun h => centered p R τ x h - p.c ^ 2 * (R x) ^ 2 * deriv τ x)
      =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  have hd := (numerator_derivative p R τ x (hR.differentiable (by decide) x)
    (hτ.differentiable (by decide) x)).deriv
  exact (LatticeCenteredTaylor.centered_error _ (numerator_contDiff p R τ x hR hτ)).congr_left
    (fun h => by rw [centered_eq_quotient, hd])

/-- The averaged incident current converges to the physical current at the site. -/
theorem centered_tendsto (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) :
    Tendsto (centered p R τ x) (𝓝[>] 0) (𝓝 (p.c ^ 2 * (R x) ^ 2 * deriv τ x)) := by
  have hsmall : Tendsto (fun h : ℝ => h^2) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hi.pow 2
  have hd := (centered_error p R τ x hR hτ).trans_tendsto hsmall
  exact tendsto_sub_nhds_zero_iff.mp hd

/-- A zero amplitude at the site annihilates both incident currents at every width. -/
theorem centered_eq_zero_of_node (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) (hx : R x = 0) :
    centered p R τ x h = 0 := by simp [centered, link, hx]

end FoliationQM.LatticeCenteredSiteCurrent
