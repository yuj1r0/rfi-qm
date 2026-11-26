module

public import FoliationQM.LatticeLinkCurrent
public import FoliationQM.LatticeCenteredTaylor
public import FoliationQM.ClockScales
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Second-order midpoint accuracy of the physical link current

In v13 line 226 the lag-clock current samples the signed amplitude and
clock at the two ends of an edge. At a fixed physical midpoint, reversing
the width exchanges those ends. The numerator is odd, so the symmetric
difference estimate yields a quadratic error for the current itself.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeMidpointCurrent

open LatticeLinkCurrent
open scoped Topology Asymptotics

/-- Eq. 9 evaluated at the two points equidistant from the edge midpoint. -/
def sampledLink (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  link p h (R (x - h / 2)) (R (x + h / 2))
    ((p.c / p.ellC) * τ (x - h / 2)) ((p.c / p.ellC) * τ (x + h / 2))

/-- The smooth numerator before division by the signed edge width. -/
def numerator (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (p.ellC * p.c) * (R (x - h / 2) * R (x + h / 2)) *
    Real.sin ((p.c / p.ellC) * (τ (x + h / 2) - τ (x - h / 2)))

/-- Reversing a signed edge reverses its numerator. -/
theorem numerator_odd (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) :
    numerator p R τ x (-h) = -numerator p R τ x h := by
  rw [numerator, numerator, neg_div, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [← neg_sub (τ (x + h / 2)) (τ (x - h / 2)), mul_neg, Real.sin_neg]
  ring

/-- Three continuous derivatives of the signed fields give three continuous
derivatives of the current numerator with respect to edge width. -/
theorem numerator_contDiff (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) : ContDiff ℝ 3 (numerator p R τ x) := by
  unfold numerator
  fun_prop

/-- Only the derivative of the clock contributes at zero width. The amplitude
may vanish at the midpoint. -/
theorem numerator_derivative (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : DifferentiableAt ℝ R x) (hτ : DifferentiableAt ℝ τ x) :
    HasDerivAt (numerator p R τ x) (p.c ^ 2 * (R x) ^ 2 * deriv τ x) 0 := by
  have hp : HasDerivAt (fun h : ℝ => x + h / 2) (1 / 2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add x
  have hm : HasDerivAt (fun h : ℝ => x - h / 2) (-(1 / 2)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 2).const_sub x
  have plus {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f x) :
      HasDerivAt (fun h => f (x + h / 2)) (deriv f x * (1 / 2)) 0 :=
    (show HasDerivAt f (deriv f x) (x + (0 : ℝ) / 2) by simpa using hf.hasDerivAt).comp 0 hp
  have minus {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f x) :
      HasDerivAt (fun h => f (x - h / 2)) (deriv f x * -(1 / 2)) 0 :=
    (show HasDerivAt f (deriv f x) (x - (0 : ℝ) / 2) by simpa using hf.hasDerivAt).comp 0 hm
  apply ((((minus hR).mul (plus hR)).const_mul (p.ellC * p.c)).mul
    (((plus hτ).sub (minus hτ)).const_mul (p.c / p.ellC)).sin).congr_deriv
  simp [Pi.mul_apply, Pi.sub_apply]
  field_simp [(ClockScales.ellC_pos p).ne']
  ring

/-- The actual sampled current is exactly the centered difference quotient of
its numerator, with both amplitudes and both lag samples retained. -/
theorem sampledLink_eq_centered (p : MassiveParameters) (R τ : ℝ → ℝ) (x h : ℝ) :
    sampledLink p R τ x h = (numerator p R τ x h - numerator p R τ x (-h)) / (2*h) := by
  rw [numerator_odd]
  simp only [sampledLink, link, numerator, ← mul_sub]
  ring

/-- At every fixed physical midpoint the difference from the continuum current
c²R²τ′ is O(h²) as positive spacing tends to zero. -/
theorem midpoint_error (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) :
    (fun h => sampledLink p R τ x h - p.c ^ 2 * (R x) ^ 2 * deriv τ x)
      =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  have hd := (numerator_derivative p R τ x (hR.differentiable (by decide) x)
    (hτ.differentiable (by decide) x)).deriv
  exact (LatticeCenteredTaylor.centered_error _ (numerator_contDiff p R τ x hR hτ)).congr_left
    (fun h => by rw [sampledLink_eq_centered, hd])

end FoliationQM.LatticeMidpointCurrent
