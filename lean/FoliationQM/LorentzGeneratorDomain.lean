module
public import FoliationQM.CliffordCommutators
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The real Lorentz-generator domain is an explicit additional condition

Source: the body-connection expansion premise in v13 `lem:maurer_cartan`.
The central imaginary identity is anti-self-adjoint for the Dirac adjoint and
commutes with gamma5, but cannot be a Lorentz-generator combination because
its trace is nonzero. Thus these two infinitesimal constraints alone cannot
replace the source's actual Spin/Lorentz expansion premise.
-/
@[expose] public section
noncomputable section
namespace FoliationQM.LorentzGeneratorDomain
open DiracMatrices DiracAdjoint CliffordCommutators

/-- Each actual sigma bivector matrix has zero trace. -/
theorem sigma_trace (a b : Fin 4) : Matrix.trace (sigma a b) = 0 := by
  rw [sigma, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_mul_comm (gamma a) (gamma b), sub_self, smul_zero]

/-- Every actual coefficient-expanded Lorentz generator has zero trace. -/
theorem generator_trace (omega : Fin 4 → Fin 4 → ℝ) :
    Matrix.trace (generator omega) = 0 := by
  simp only [generator, Matrix.trace_sum, Matrix.trace_smul, sigma_trace, smul_zero,
    Finset.sum_const_zero]

/-- The central imaginary identity satisfies the infinitesimal Dirac-isometry constraint. -/
theorem central_diracAdjoint :
    diracAdjoint (Complex.I • (1 : Mat)) = -(Complex.I • (1 : Mat)) := by
  simp [diracAdjoint_smul, diracAdjoint_one]

/-- The central imaginary identity satisfies the gamma5 commutation constraint. -/
theorem central_commute_gamma5 : Commute (Complex.I • (1 : Mat)) gamma5 := by
  change (Complex.I • (1 : Mat)) * gamma5 = gamma5 * (Complex.I • (1 : Mat))
  simp

/-- The two infinitesimal constraints do not force membership in the Lorentz-generator span. -/
theorem central_not_generator (omega : Fin 4 → Fin 4 → ℝ) :
    Complex.I • (1 : Mat) ≠ generator omega := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [generator_trace] at ht
  norm_num [Matrix.trace_smul, Matrix.trace_one] at ht

end FoliationQM.LorentzGeneratorDomain
