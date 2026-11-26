module
public import FoliationQM.SpecialLinearSpin
public import FoliationQM.ChiralSpinorMatrix
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-!
# Constructive pointwise polar reconstruction on the strict regular domain

Source: v13 `prop:takabayasi`, `eq:takabayasi_polar`, and the strict regular
domain required by the startup specification. The density is the existing
actual scalar-pseudoscalar invariant density. The full chiral angle is the
principal argument of the actual spinor-matrix determinant; its half-angle
amplitude is proved to square to that determinant. Strict regularity alone
makes this amplitude invertible, giving an explicit determinant-one matrix
and its concrete Dirac representative.

The actual source polar spinor then reconstructs the input spinor by the
injective real-linear matrix encoding. No decomposition, frame, normalized
representative, or angle identity is supplied as a premise. The constructed
representative is an actual Dirac isometry, is invertible and commutes with
gamma5. Two-pi sign change, simultaneous angle/matrix sign identification,
and four-pi periodicity remain explicit.

The principal argument is used only for pointwise existence. No global
continuous angle, quotient inverse, smooth reconstruction, abstract Spin
image classification, or Lorentz covering theorem is asserted here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RegularPolarReconstruction
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin SpinorRegularity
open PolarSpinorBilinears ChiralSpinorMatrix

/-- The pointwise principal full chiral angle determined by the actual spinor determinant. -/
def determinantPhase (psi : Spinor) : ℝ := Complex.arg (Matrix.det (toMatrix psi))

/-- The actual complex square-root amplitude with the half of the chosen full chiral angle. -/
def amplitudePhase (psi : Spinor) : ℂ :=
  (Real.sqrt (invariantDensity psi) : ℂ)*Complex.exp (Complex.I*(determinantPhase psi : ℂ)/2)

/-- The explicit matrix normalization candidate, with determinant one on the strict regular domain. -/
def normalizedMatrix (psi : Spinor) : Mat2 := (amplitudePhase psi)⁻¹ • toMatrix psi

/-- The concrete four-dimensional Dirac representative reconstructed from the normalized matrix. -/
def reconstructedSpin (psi : Spinor) : Mat := spin (normalizedMatrix psi)

private theorem sqrt_norm_exp_half_square (z : ℂ) :
    ((Real.sqrt ‖z‖ : ℂ)*Complex.exp (Complex.I*(Complex.arg z : ℂ)/2))^2 = z := by
  rw [mul_pow]
  have hs : (Real.sqrt ‖z‖ : ℂ)^2 = (‖z‖ : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (norm_nonneg z)
  rw [hs, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2:ℂ)*(Complex.I*(Complex.arg z:ℂ)/2)=(Complex.arg z:ℂ)*Complex.I := by ring
  rw [he, Complex.norm_mul_exp_arg_mul_I]

/-- Squaring the actual half-angle amplitude gives the full invariant determinant, for every spinor. -/
theorem amplitudePhase_sq (psi : Spinor) : (amplitudePhase psi)^2=Matrix.det (toMatrix psi) := by
  simpa only [amplitudePhase, determinantPhase, norm_det_toMatrix] using
    sqrt_norm_exp_half_square (Matrix.det (toMatrix psi))

/-- The actual half-angle amplitude is nonzero precisely on the strict invariant regular domain. -/
theorem amplitudePhase_ne_zero_iff_regular (psi : Spinor) :
    amplitudePhase psi ≠ 0 ↔ Regular psi := by
  rw [← det_ne_zero_iff_regular, ← amplitudePhase_sq]
  constructor
  · exact pow_ne_zero 2
  · intro h hz
    exact h (by rw [hz]; norm_num)

/-- Strict regularity guarantees that the explicit half-angle amplitude can be inverted. -/
theorem amplitudePhase_ne_zero {psi : Spinor} (hpsi : Regular psi) : amplitudePhase psi ≠ 0 :=
  (amplitudePhase_ne_zero_iff_regular psi).mpr hpsi

/-- The constructed matrix has actual determinant one whenever the spinor is regular. -/
theorem normalizedMatrix_det {psi : Spinor} (hpsi : Regular psi) :
    Matrix.det (normalizedMatrix psi) = 1 := by
  rw [normalizedMatrix, Matrix.det_smul]
  norm_num only [Fintype.card_fin]
  rw [← amplitudePhase_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (amplitudePhase_ne_zero hpsi))]

/-- The invertible half-angle amplitude exactly restores the encoded spinor from its normalized matrix. -/
theorem amplitudePhase_smul_normalizedMatrix {psi : Spinor} (hpsi : Regular psi) :
    amplitudePhase psi • normalizedMatrix psi=toMatrix psi := by
  simp [normalizedMatrix, smul_smul, amplitudePhase_ne_zero hpsi]

/-- The reconstructed determinant-one representative is an actual Dirac isometry. -/
theorem reconstructedSpin_dirac_isometry {psi : Spinor} (hpsi : Regular psi) :
    diracAdjoint (reconstructedSpin psi)*reconstructedSpin psi=1 :=
  spin_dirac_isometry _ (normalizedMatrix_det hpsi)

/-- The reconstructed representative is an actually invertible four-by-four complex matrix. -/
theorem reconstructedSpin_isUnit {psi : Spinor} (hpsi : Regular psi) : IsUnit (reconstructedSpin psi) :=
  spin_isUnit _ (normalizedMatrix_det hpsi)

/-- The reconstructed representative commutes with the actual gamma5 matrix. -/
theorem reconstructedSpin_gamma5_commute (psi : Spinor) : Commute (reconstructedSpin psi) gamma5 :=
  spin_gamma5_commute _

/-- The selected full chiral angle lies in the pointwise principal-argument interval, without a global continuity claim. -/
theorem determinantPhase_bounds (psi : Spinor) :
    -Real.pi < determinantPhase psi ∧ determinantPhase psi ≤ Real.pi :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

/-- Every strictly regular actual spinor is reconstructed by its invariant density, chosen full angle and constructed determinant-one representative, without supplied polar data. -/
theorem regular_reconstruction {psi : Spinor} (hpsi : Regular psi) :
    psi = polarSpinor (invariantDensity psi) (determinantPhase psi) (reconstructedSpin psi) := by
  apply toMatrix_injective
  rw [toMatrix_polarSpinor, reconstructedSpin, spin_rest_matrix]
  exact (amplitudePhase_smul_normalizedMatrix hpsi).symm

/-- Every regular spinor has a concrete polar representation by an actual determinant-one two-by-two matrix. -/
theorem exists_specialLinear_polar {psi : Spinor} (hpsi : Regular psi) :
    ∃ beta : ℝ, ∃ A : Mat2, Matrix.det A=1 ∧
      psi=polarSpinor (invariantDensity psi) beta (spin A) := by
  exact ⟨determinantPhase psi, normalizedMatrix psi, normalizedMatrix_det hpsi,
    regular_reconstruction hpsi⟩

/-- A two-pi shift of the reconstructed full angle alone negates the actual regular spinor. -/
theorem reconstruction_add_two_pi {psi : Spinor} (hpsi : Regular psi) :
    polarSpinor (invariantDensity psi) (determinantPhase psi+2*Real.pi)
      (reconstructedSpin psi) = -psi := by
  rw [polarSpinor_add_two_pi, ← regular_reconstruction hpsi]

/-- The constructed regular-spinor decomposition respects the exact simultaneous two-pi full-angle shift and spin-matrix sign flip. -/
theorem reconstruction_shift_neg {psi : Spinor} (hpsi : Regular psi) :
    psi=polarSpinor (invariantDensity psi) (determinantPhase psi+2*Real.pi)
      (-reconstructedSpin psi) := by
  rw [polarSpinor_shift_neg]
  exact regular_reconstruction hpsi

/-- The constructed actual polar spinor is unchanged by a four-pi full-angle shift with its reconstructed matrix fixed. -/
theorem reconstruction_add_four_pi {psi : Spinor} (hpsi : Regular psi) :
    psi=polarSpinor (invariantDensity psi) (determinantPhase psi+4*Real.pi)
      (reconstructedSpin psi) := by
  exact (regular_reconstruction hpsi).trans
    ((polarSpinor_periodic (invariantDensity psi) (reconstructedSpin psi))
      (determinantPhase psi)).symm

end FoliationQM.RegularPolarReconstruction
