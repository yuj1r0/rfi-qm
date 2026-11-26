module
public import FoliationQM.RegularPolarReconstruction
public import Mathlib.Tactic.Ring
/-!
# Exact fibers of the concrete regular polar matrix parameters

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`, with the startup
strict regular domain and simultaneous sign identification. A nonzero
complex amplitude and an actual determinant-one two-by-two matrix encode
an actual spinor through the proved real-linear coordinate inverse.
The complex amplitude multiplies the encoded matrix, not the Dirac spinor.

The determinant proves that equal encoded matrices have equal amplitude
squares. Nonzero amplitude then makes the only possibilities equality of
both parameters or simultaneous negation of both. The spinor statement
uses the actual coordinate bijection, and the final bridge identifies the
actual source polar ansatz at its real amplitude and half-angle phase.
No quotient construction, smooth angle choice, abstract Spin-group
classification, or Lorentz covering classification is assumed here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarMatrixFibers
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSpinorBilinears ChiralSpinorMatrix

/-- The actual spinor encoded by complex scalar multiplication of a two-by-two matrix. -/
def parameterSpinor (t : ℂ) (A : Mat2) : Spinor := ofMatrix (t • A)

/-- Encoding the parameterized spinor recovers its actual amplitude-scaled matrix. -/
theorem toMatrix_parameterSpinor (t : ℂ) (A : Mat2) :
    toMatrix (parameterSpinor t A) = t • A := toMatrix_ofMatrix _

/-- A determinant-one matrix gives the squared complex amplitude as the actual spinor determinant. -/
theorem det_parameterSpinor (t : ℂ) (A : Mat2) (hA : A.det = 1) :
    Matrix.det (toMatrix (parameterSpinor t A)) = t^2 := by
  rw [toMatrix_parameterSpinor, Matrix.det_smul, hA]
  norm_num

/-- Nonzero complex amplitude and determinant one produce a strictly invariant-regular actual spinor. -/
theorem regular_parameterSpinor (t : ℂ) (A : Mat2) (ht : t ≠ 0) (hA : A.det = 1) :
    Regular (parameterSpinor t A) := by
  apply (det_ne_zero_iff_regular _).mp
  rw [det_parameterSpinor t A hA]
  exact pow_ne_zero 2 ht

/-- The invariant density of the actual parameterized spinor is the squared complex amplitude norm. -/
theorem density_parameterSpinor (t : ℂ) (A : Mat2) (hA : A.det = 1) :
    invariantDensity (parameterSpinor t A) = ‖t‖^2 := by
  rw [← norm_det_toMatrix, det_parameterSpinor t A hA, norm_pow]

/-- Two nonzero amplitude and determinant-one matrix parameters encode the same matrix exactly when they agree or are both negated. -/
theorem matrix_fibers_iff (t s : ℂ) (A B : Mat2)
    (ht : t ≠ 0) (hs : s ≠ 0) (hA : A.det = 1) (hB : B.det = 1) :
    t • A = s • B ↔ (t = s ∧ A = B) ∨ (t = -s ∧ A = -B) := by
  constructor
  · intro heq
    have hd := congrArg Matrix.det heq
    simp only [Matrix.det_smul, Fintype.card_fin, hA, hB, mul_one] at hd
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hd with hts | hts
    · left
      refine ⟨hts, ?_⟩
      subst s
      have hh := congrArg (fun M : Mat2 => t⁻¹ • M) heq
      simpa [smul_smul, ht] using hh
    · right
      refine ⟨hts, ?_⟩
      rw [hts] at heq
      have hh := congrArg (fun M : Mat2 => s⁻¹ • M) heq
      have hab : -A = B := by simpa [smul_smul, hs] using hh
      exact neg_eq_iff_eq_neg.mp hab
  · rintro (⟨hts, hab⟩ | ⟨hts, hab⟩)
    · rw [hts, hab]
    · rw [hts, hab]
      simp

/-- The actual spinor parameterization has exactly the equality and simultaneous-sign fibers on its regular parameter domain. -/
theorem parameterSpinor_fibers_iff (t s : ℂ) (A B : Mat2)
    (ht : t ≠ 0) (hs : s ≠ 0) (hA : A.det = 1) (hB : B.det = 1) :
    parameterSpinor t A = parameterSpinor s B ↔
      (t = s ∧ A = B) ∨ (t = -s ∧ A = -B) := by
  constructor
  · intro h
    apply (matrix_fibers_iff t s A B ht hs hA hB).mp
    have hh := congrArg toMatrix h
    simpa only [toMatrix_parameterSpinor] using hh
  · intro h
    exact congrArg ofMatrix ((matrix_fibers_iff t s A B ht hs hA hB).mpr h)

/-- Simultaneous negation of amplitude and matrix leaves the actual encoded spinor unchanged. -/
theorem parameterSpinor_neg_neg (t : ℂ) (A : Mat2) :
    parameterSpinor (-t) (-A) = parameterSpinor t A := by
  simp [parameterSpinor]

/-- The encoded spinor at the real square-root amplitude and complex half-angle phase is the actual source polar spinor. -/
theorem parameterSpinor_polarAmplitude (rho beta : ℝ) (A : Mat2) :
    parameterSpinor ((Real.sqrt rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ) / 2)) A =
      polarSpinor rho beta (spin A) := by
  apply toMatrix_injective
  rw [toMatrix_parameterSpinor, toMatrix_polarSpinor, spin_rest_matrix]

end FoliationQM.PolarMatrixFibers
