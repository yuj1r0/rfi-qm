module
public import FoliationQM.PrincipalPolarSmooth
/-!
# The rotated polar branch and an explicit two-chart regular cover

Source: local regular polar reconstruction in v13 `prop:takabayasi` and
`eq:takabayasi_polar`. The actual real-linear spinor rotation multiplies
its encoded two-by-two matrix by minus i. Its determinant therefore
changes sign while the actual invariant density is preserved. Pulling the
principal branch back by this concrete rotation gives the second open
branch, with full angle strictly between zero and two pi.

The second branch reconstructs the original spinor, not merely the rotated
one. Its matrix has determinant one and its actual Dirac representative
is invertible, Dirac-isometric and gamma5-commuting. The existing smooth
principal inverse maps and the genuine continuous-linear rotation prove
smoothness of all three rotated inverse components.

The two branches cover exactly the strict regular domain. No globally
chosen smooth real angle, abstract Spin-group classification or Lorentz
covering theorem is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RotatedPolarChart
open DiracMatrices DiracAdjoint SpinorMatrix SpinorRegularity SpecialLinearSpin SpinorMatrixSmooth
open RegularPolarReconstruction PrincipalPolarSmooth PolarSpinorBilinears ChiralSpinorMatrix

/-- The actual real-linear rotation of spinor matrix coordinates by minus i. -/
def rotate (psi : Spinor) : Spinor := ofMatrix ((-Complex.I) • toMatrix psi)

/-- The second reconstruction branch is the inverse image of the principal branch under the actual rotation. -/
def RotatedDomain : Set Spinor := {psi | rotate psi ∈ PrincipalDomain}

/-- The second branch's full angle is pi plus the principal determinant angle after rotation. -/
def rotatedPhase (psi : Spinor) : ℝ := Real.pi+determinantPhase (rotate psi)

/-- The second branch's actual determinant-one matrix is the principal normalization after rotation. -/
def rotatedMatrix (psi : Spinor) : Mat2 := normalizedMatrix (rotate psi)

/-- The actual four-by-four representative of the second branch's reconstructed matrix. -/
def rotatedSpin (psi : Spinor) : Mat := spin (rotatedMatrix psi)

/-- The actual rotation is the composite of the real continuous-linear encoding, complex scalar action on matrices, and inverse encoding. -/
def rotateCLM : Spinor →L[ℝ] Spinor :=
  continuousLinearEquiv.symm.toContinuousLinearMap.comp
    (((-Complex.I) • (ContinuousLinearMap.id ℝ Mat2)).comp
      continuousLinearEquiv.toContinuousLinearMap)

/-- The continuous-linear rotation map evaluates to the actual rotated spinor. -/
theorem rotateCLM_apply (psi : Spinor) : rotateCLM psi=rotate psi := rfl

/-- The actual rotation is real-smooth to every order on the entire spinor space. -/
theorem contDiff_rotate (n : WithTop ℕ∞) : ContDiff ℝ n rotate := rotateCLM.contDiff

/-- Encoding the actual rotated spinor gives minus i times the original encoded matrix. -/
theorem toMatrix_rotate (psi : Spinor) : toMatrix (rotate psi)=(-Complex.I) • toMatrix psi :=
  toMatrix_ofMatrix _

/-- The actual spinor determinant changes sign under the chosen rotation. -/
theorem det_rotate (psi : Spinor) : Matrix.det (toMatrix (rotate psi))= -Matrix.det (toMatrix psi) := by
  rw [toMatrix_rotate, Matrix.det_smul]
  norm_num

/-- The actual invariant density is preserved by the rotation. -/
theorem invariantDensity_rotate (psi : Spinor) : invariantDensity (rotate psi)=invariantDensity psi := by
  rw [← norm_det_toMatrix, det_rotate, norm_neg, norm_det_toMatrix]

/-- The actual rotation preserves the strict invariant regular domain. -/
theorem regular_rotate_iff (psi : Spinor) : Regular (rotate psi) ↔ Regular psi := by
  simp only [Regular, invariantDensity_rotate]

/-- The second branch is open because it is the inverse image of the open principal branch by the actual continuous rotation. -/
theorem rotatedDomain_isOpen : IsOpen RotatedDomain :=
  principalDomain_isOpen.preimage (contDiff_rotate 0).continuous

/-- Every spinor in the second branch is strictly invariant-regular. -/
theorem rotatedDomain_regular {psi : Spinor} (hpsi : psi ∈ RotatedDomain) : Regular psi :=
  (regular_rotate_iff psi).mp (principalDomain_regular hpsi)

/-- Every strictly regular actual spinor lies in at least one of the two explicit determinant branches. -/
theorem regular_two_chart_cover {psi : Spinor} (hpsi : Regular psi) :
    psi ∈ PrincipalDomain ∨ psi ∈ RotatedDomain := by
  by_cases h : psi ∈ PrincipalDomain
  · exact Or.inl h
  · right
    change Matrix.det (toMatrix (rotate psi)) ∈ Complex.slitPlane
    rw [det_rotate, Complex.mem_slitPlane_iff]
    have hbad : ¬(0 < (Matrix.det (toMatrix psi)).re ∨ (Matrix.det (toMatrix psi)).im ≠ 0) := h
    push Not at hbad
    rcases hbad with ⟨hre, him⟩
    have hn : (Matrix.det (toMatrix psi)).re ≠ 0 := by
      intro he
      apply (det_ne_zero_iff_regular psi).mpr hpsi
      exact Complex.ext he him
    left
    simpa only [Complex.neg_re] using neg_pos.mpr (lt_of_le_of_ne hre hn)

/-- The two explicit open branches cover exactly the strict regular domain. -/
theorem regular_iff_two_charts (psi : Spinor) :
    Regular psi ↔ psi ∈ PrincipalDomain ∨ psi ∈ RotatedDomain := by
  constructor
  · exact regular_two_chart_cover
  · rintro (h | h)
    · exact principalDomain_regular h
    · exact rotatedDomain_regular h

/-- The second branch's full angle lies strictly between zero and two pi. -/
theorem rotatedPhase_bounds {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    0 < rotatedPhase psi ∧ rotatedPhase psi < 2*Real.pi := by
  have h := determinantPhase_bounds_strict hpsi
  change 0 < Real.pi+determinantPhase (rotate psi) ∧
    Real.pi+determinantPhase (rotate psi) < 2*Real.pi
  constructor <;> linarith

/-- The second branch's matrix has actual determinant one. -/
theorem rotatedMatrix_det {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    Matrix.det (rotatedMatrix psi)=1 := normalizedMatrix_det (principalDomain_regular hpsi)

/-- The second branch's actual Dirac representative is a Dirac isometry. -/
theorem rotatedSpin_dirac_isometry {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    diracAdjoint (rotatedSpin psi)*rotatedSpin psi=1 := spin_dirac_isometry _ (rotatedMatrix_det hpsi)

/-- The second branch's actual four-by-four representative is invertible. -/
theorem rotatedSpin_isUnit {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    IsUnit (rotatedSpin psi) := spin_isUnit _ (rotatedMatrix_det hpsi)

/-- The second branch's actual representative commutes with gamma5. -/
theorem rotatedSpin_gamma5_commute (psi : Spinor) : Commute (rotatedSpin psi) gamma5 :=
  spin_gamma5_commute _

private theorem amplitude_shift_pi (rho beta : ℝ) :
    (Real.sqrt rho:ℂ)*Complex.exp (Complex.I*((Real.pi+beta:ℝ):ℂ)/2) =
      Complex.I*((Real.sqrt rho:ℂ)*Complex.exp (Complex.I*(beta:ℂ)/2)) := by
  have he : Complex.I*((Real.pi+beta:ℝ):ℂ)/2=
      (Real.pi:ℂ)/2*Complex.I+Complex.I*(beta:ℂ)/2 := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  ring

/-- Every actual spinor in the second branch reconstructs from its preserved invariant density, rotated full angle and constructed representative. -/
theorem rotated_reconstruction {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    psi=polarSpinor (invariantDensity psi) (rotatedPhase psi) (rotatedSpin psi) := by
  apply toMatrix_injective
  rw [toMatrix_polarSpinor, rotatedSpin, spin_rest_matrix]
  simp only [rotatedPhase, rotatedMatrix]
  rw [amplitude_shift_pi, ← invariantDensity_rotate psi]
  change toMatrix psi=(Complex.I*amplitudePhase (rotate psi)) • normalizedMatrix (rotate psi)
  rw [mul_smul, amplitudePhase_smul_normalizedMatrix (principalDomain_regular hpsi),
    toMatrix_rotate, smul_smul]
  simp

/-- The actual second-branch full angle is smooth at every point of its branch. -/
theorem contDiffAt_rotatedPhase (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ RotatedDomain) : ContDiffAt ℝ n rotatedPhase psi := by
  exact contDiffAt_const.add ((contDiffAt_determinantPhase n hpsi).comp psi (contDiff_rotate n).contDiffAt)

/-- The actual second-branch normalized matrix is smooth at every point of its branch. -/
theorem contDiffAt_rotatedMatrix (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ RotatedDomain) : ContDiffAt ℝ n rotatedMatrix psi :=
  (contDiffAt_normalizedMatrix n hpsi).comp psi (contDiff_rotate n).contDiffAt

/-- The actual second-branch Dirac representative is smooth at every point of its branch. -/
theorem contDiffAt_rotatedSpin (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ RotatedDomain) : ContDiffAt ℝ n rotatedSpin psi :=
  (contDiff_spin n).contDiffAt.comp psi (contDiffAt_rotatedMatrix n hpsi)

/-- The actual second-branch full angle is smooth throughout its open domain. -/
theorem contDiffOn_rotatedPhase (n : WithTop ℕ∞) : ContDiffOn ℝ n rotatedPhase RotatedDomain :=
  fun _ hpsi => (contDiffAt_rotatedPhase n hpsi).contDiffWithinAt

/-- The actual second-branch normalized matrix is smooth throughout its open domain. -/
theorem contDiffOn_rotatedMatrix (n : WithTop ℕ∞) : ContDiffOn ℝ n rotatedMatrix RotatedDomain :=
  fun _ hpsi => (contDiffAt_rotatedMatrix n hpsi).contDiffWithinAt

/-- The actual second-branch Dirac representative is smooth throughout its open domain. -/
theorem contDiffOn_rotatedSpin (n : WithTop ℕ∞) : ContDiffOn ℝ n rotatedSpin RotatedDomain :=
  fun _ hpsi => (contDiffAt_rotatedSpin n hpsi).contDiffWithinAt

end FoliationQM.RotatedPolarChart
