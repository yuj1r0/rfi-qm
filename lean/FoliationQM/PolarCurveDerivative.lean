module

public import FoliationQM.PolarAffineChart

/-!
# Actual derivatives of the inverse polar variation curves

Sources: v13 `thm:kahler` and `eq:master_variational_equivalence`.
The relative logarithmic polar curves reconstruct an affine complex variation.
Here their actual real-parameter derivatives at zero are proved to be the
explicit inverse density and action-phase tangents. This is pointwise in the
spatial argument and does not interchange differentiation with an integral.
-/
@[expose] public section

namespace FoliationQM.PolarCurveDerivative

open ActionDensity PolarAffineChart PolarTangentEquiv
open scoped ComplexConjugate

/-- The actual Born-density derivative along an affine complex curve. -/
theorem hasDerivAt_normSq_affine (ψ η : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.normSq (ψ + (t : ℂ) * η))
      (densityVariation ψ η) 0 := by
  have hre : HasDerivAt (fun t : ℝ => ψ.re + t * η.re) η.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const η.re).const_add ψ.re
  have him : HasDerivAt (fun t : ℝ => ψ.im + t * η.im) η.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const η.im).const_add ψ.im
  convert (hre.pow 2).add (him.pow 2) using 1
  · ext t
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, Pi.pow_apply, Pi.add_apply]
    ring
  · simp only [densityVariation, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      zero_mul, add_zero, Nat.cast_ofNat]
    ring

/-- Differentiating the actual relative complex logarithm at the identity.
This formula also holds for the totalized quotient when `ψ = 0`; regular
polar interpretations below separately impose positive density. -/
theorem hasDerivAt_log_affine_ratio (ψ η : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.log (1 + (t : ℂ) * η / ψ)) (η / ψ) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt
  have hq : HasDerivAt (fun t : ℝ => 1 + (t : ℂ) * η / ψ) (η / ψ) 0 := by
    simpa using ((ht.mul_const η).div_const ψ).const_add 1
  simpa using hq.clog_real (by simp)

variable {E : Type*}

/-- The inverse polar density curve realizes the density tangent recovered
from its complex variation, at every spatial point. -/
theorem hasDerivAt_curveDensity (p : MassiveParameters) (ρ S : E → ℝ)
    (η : E → ℂ) (x : E) :
    HasDerivAt (fun t : ℝ => curveDensity p ρ S η t x)
      (densityVariation (actionField p ρ S x) (η x)) 0 :=
  hasDerivAt_normSq_affine (actionField p ρ S x) (η x)

/-- The inverse relative phase curve realizes the recovered action-phase
tangent. Positive density supplies the nonvanishing polar background. -/
theorem hasDerivAt_curveAction (p : MassiveParameters) (ρ S : E → ℝ)
    (η : E → ℂ) (x : E) (hpos : 0 < ρ x) :
    HasDerivAt (fun t : ℝ => curveAction p ρ S η t x)
      (phaseVariation p (ρ x) (actionField p ρ S x) (η x)) 0 := by
  let ψ := actionField p ρ S x
  have hl := hasDerivAt_log_affine_ratio ψ (η x)
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hl
  have hd := (hi.const_mul p.hbar).const_add (S x)
  have hnorm : Complex.normSq ψ = ρ x := polarField_normSq ρ _ x hpos.le
  have heq : p.hbar * (η x / ψ).im = phaseVariation p (ρ x) ψ (η x) := by
    simp only [phaseVariation, Complex.div_im, hnorm, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Function.comp_def, Complex.imCLM_apply, heq, curveAction, ψ] using hd

end FoliationQM.PolarCurveDerivative
