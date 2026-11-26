module
public import FoliationQM.RotatedPolarChart
public import FoliationQM.PolarAngleFibers
public import Mathlib.Analysis.Calculus.FDeriv.Congr
/-!
# Actual transitions between the two regular polar branches

Sources: v13 `prop:takabayasi`, `eq:takabayasi_polar`, and the explicit
simultaneous full-angle/matrix sign identification. The principal and
rotated determinant branches overlap exactly where the determinant has
nonzero imaginary part. On the upper half-plane their full angles and
normalized matrices agree. On the lower half-plane the rotated full angle
is the principal angle plus two pi and the normalized matrix is negated.

The phase identities use the actual principal argument. The matrix
identities follow from actual reconstructed spinors, their injective
matrix encoding, and cancellation of the nonzero invariant amplitude.
The actual four-by-four representatives and Frechet derivatives follow
from the proved sign identities on the two open overlap components.
No abstract Lorentz covering or quotient-bundle classification is assumed.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.PolarChartTransitions
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open RegularPolarReconstruction PrincipalPolarSmooth RotatedPolarChart

private theorem complex_overlap_iff (z : ℂ) :
    z ∈ Complex.slitPlane ∧ -z ∈ Complex.slitPlane ↔ z.im ≠ 0 := by
  simp only [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im, neg_ne_zero]
  constructor
  · rintro ⟨hp, hn⟩ hzero
    simp [hzero] at hp hn
    linarith
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

/-- The two actual determinant branches overlap exactly at spinors whose determinant has nonzero imaginary part. -/
theorem principal_rotated_overlap_iff (psi : Spinor) :
    psi ∈ PrincipalDomain ∧ psi ∈ RotatedDomain ↔
      (Matrix.det (toMatrix psi)).im ≠ 0 := by
  change Matrix.det (toMatrix psi) ∈ Complex.slitPlane ∧
    Matrix.det (toMatrix (rotate psi)) ∈ Complex.slitPlane ↔ _
  rw [det_rotate]
  exact complex_overlap_iff _

/-- On the upper determinant half-plane the actual rotated full angle equals the actual principal full angle. -/
theorem rotatedPhase_eq_of_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    rotatedPhase psi = determinantPhase psi := by
  change Real.pi + Complex.arg (Matrix.det (toMatrix (rotate psi))) =
    Complex.arg (Matrix.det (toMatrix psi))
  rw [det_rotate, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
  ring

/-- On the lower determinant half-plane the actual rotated full angle is the principal full angle plus two pi. -/
theorem rotatedPhase_eq_add_two_pi_of_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    rotatedPhase psi = determinantPhase psi + 2*Real.pi := by
  change Real.pi + Complex.arg (Matrix.det (toMatrix (rotate psi))) =
    Complex.arg (Matrix.det (toMatrix psi)) + 2*Real.pi
  rw [det_rotate, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
  ring

private theorem regular_of_im_ne_zero {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im ≠ 0) : Regular psi := by
  apply (det_ne_zero_iff_regular psi).mp
  intro hz
  exact h (by rw [hz]; rfl)

private theorem rotated_amplitude_smul_matrix {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    ((Real.sqrt (invariantDensity psi) : ℂ) *
      Complex.exp (Complex.I * (rotatedPhase psi : ℂ) / 2)) • rotatedMatrix psi =
        toMatrix psi := by
  have hh := congrArg toMatrix (rotated_reconstruction hpsi)
  simpa only [ChiralSpinorMatrix.toMatrix_polarSpinor, rotatedSpin,
    spin_rest_matrix] using hh.symm

/-- On the upper overlap component the actual reconstructed determinant-one matrices agree. -/
theorem rotatedMatrix_eq_of_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    rotatedMatrix psi = normalizedMatrix psi := by
  have hr := regular_of_im_ne_zero h.ne'
  have hh := rotated_amplitude_smul_matrix
    ((principal_rotated_overlap_iff psi).mpr h.ne').2
  rw [rotatedPhase_eq_of_im_pos h] at hh
  change amplitudePhase psi • rotatedMatrix psi = toMatrix psi at hh
  have he : amplitudePhase psi • rotatedMatrix psi =
      amplitudePhase psi • normalizedMatrix psi :=
    hh.trans (amplitudePhase_smul_normalizedMatrix hr).symm
  have hi := congrArg (fun M : Mat2 => (amplitudePhase psi)⁻¹ • M) he
  simpa [smul_smul, amplitudePhase_ne_zero hr] using hi

/-- On the lower overlap component the actual reconstructed determinant-one matrices are negatives. -/
theorem rotatedMatrix_eq_neg_of_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    rotatedMatrix psi = -normalizedMatrix psi := by
  have hr := regular_of_im_ne_zero h.ne
  have hh := rotated_amplitude_smul_matrix
    ((principal_rotated_overlap_iff psi).mpr h.ne).2
  rw [rotatedPhase_eq_add_two_pi_of_im_neg h] at hh
  have hp := PolarAngleFibers.halfPhase_add_two_pi (determinantPhase psi)
  change Complex.exp (Complex.I * ((determinantPhase psi + 2 * Real.pi : ℝ) : ℂ) / 2) =
    -Complex.exp (Complex.I * (determinantPhase psi : ℂ) / 2) at hp
  rw [hp, mul_neg] at hh
  change (-amplitudePhase psi) • rotatedMatrix psi = toMatrix psi at hh
  have he : (-amplitudePhase psi) • rotatedMatrix psi =
      amplitudePhase psi • normalizedMatrix psi :=
    hh.trans (amplitudePhase_smul_normalizedMatrix hr).symm
  have hi := congrArg (fun M : Mat2 => (amplitudePhase psi)⁻¹ • M) he
  have hn : -rotatedMatrix psi = normalizedMatrix psi := by
    simpa [smul_smul, amplitudePhase_ne_zero hr] using hi
  exact neg_eq_iff_eq_neg.mp hn

/-- On the upper overlap component the actual four-by-four reconstructed Dirac representatives agree. -/
theorem rotatedSpin_eq_of_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    rotatedSpin psi = reconstructedSpin psi := by
  simp only [rotatedSpin, reconstructedSpin, rotatedMatrix_eq_of_im_pos h]

/-- On the lower overlap component the actual reconstructed Dirac representatives undergo the matching sign reversal. -/
theorem rotatedSpin_eq_neg_of_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    rotatedSpin psi = -reconstructedSpin psi := by
  rw [rotatedSpin, rotatedMatrix_eq_neg_of_im_neg h]
  exact SpinorMatrixSmooth.spinCLM.map_neg _

/-- Every overlap point obeys exactly one of the displayed equality or simultaneous two-pi/matrix-sign transition alternatives. -/
theorem overlap_transition {psi : Spinor}
    (hprincipal : psi ∈ PrincipalDomain) (hrotated : psi ∈ RotatedDomain) :
    (rotatedPhase psi = determinantPhase psi ∧ rotatedMatrix psi = normalizedMatrix psi) ∨
      (rotatedPhase psi = determinantPhase psi + 2*Real.pi ∧
        rotatedMatrix psi = -normalizedMatrix psi) := by
  have hn := (principal_rotated_overlap_iff psi).mp ⟨hprincipal, hrotated⟩
  rcases lt_or_gt_of_ne hn with h | h
  · exact Or.inr ⟨rotatedPhase_eq_add_two_pi_of_im_neg h, rotatedMatrix_eq_neg_of_im_neg h⟩
  · exact Or.inl ⟨rotatedPhase_eq_of_im_pos h, rotatedMatrix_eq_of_im_pos h⟩

private theorem eventually_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    ∀ᶠ q in 𝓝 psi, 0 < (Matrix.det (toMatrix q)).im := by
  have hc := Complex.continuous_im.comp (SpinorMatrixSmooth.contDiff_spinorDet 0).continuous
  exact (isOpen_lt continuous_const hc).mem_nhds h

private theorem eventually_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    ∀ᶠ q in 𝓝 psi, (Matrix.det (toMatrix q)).im < 0 := by
  have hc := Complex.continuous_im.comp (SpinorMatrixSmooth.contDiff_spinorDet 0).continuous
  exact (isOpen_lt hc continuous_const).mem_nhds h

/-- The actual full-angle Frechet derivatives agree on the upper overlap component by local equality of the smooth branches. -/
theorem fderiv_rotatedPhase_eq_of_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    fderiv ℝ rotatedPhase psi = fderiv ℝ determinantPhase psi := by
  have he : rotatedPhase =ᶠ[𝓝 psi] determinantPhase :=
    (eventually_im_pos h).mono fun _ hq => rotatedPhase_eq_of_im_pos hq
  exact he.fderiv_eq

/-- The actual full-angle Frechet derivatives agree on the lower overlap component because the branch difference is the constant two pi. -/
theorem fderiv_rotatedPhase_eq_of_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    fderiv ℝ rotatedPhase psi = fderiv ℝ determinantPhase psi := by
  have he : rotatedPhase =ᶠ[𝓝 psi] (fun q => determinantPhase q + 2*Real.pi) :=
    (eventually_im_neg h).mono fun _ hq => rotatedPhase_eq_add_two_pi_of_im_neg hq
  rw [he.fderiv_eq, fderiv_add_const]

/-- The actual matrix Frechet derivatives agree on the upper overlap component by local equality of the normalized matrices. -/
theorem fderiv_rotatedMatrix_eq_of_im_pos {psi : Spinor}
    (h : 0 < (Matrix.det (toMatrix psi)).im) :
    fderiv ℝ rotatedMatrix psi = fderiv ℝ normalizedMatrix psi := by
  have he : rotatedMatrix =ᶠ[𝓝 psi] normalizedMatrix :=
    (eventually_im_pos h).mono fun _ hq => rotatedMatrix_eq_of_im_pos hq
  exact he.fderiv_eq

/-- The actual matrix Frechet derivatives have the matching negative sign on the lower overlap component. -/
theorem fderiv_rotatedMatrix_eq_neg_of_im_neg {psi : Spinor}
    (h : (Matrix.det (toMatrix psi)).im < 0) :
    fderiv ℝ rotatedMatrix psi = -fderiv ℝ normalizedMatrix psi := by
  have he : rotatedMatrix =ᶠ[𝓝 psi] (-normalizedMatrix) :=
    (eventually_im_neg h).mono fun _ hq => rotatedMatrix_eq_neg_of_im_neg hq
  rw [he.fderiv_eq]
  simpa using! (fderiv_neg (𝕜 := ℝ) (f := normalizedMatrix) (x := psi))

end FoliationQM.PolarChartTransitions
