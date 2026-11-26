module
public import FoliationQM.ReconstructedFrameGeometry
/-!
# Future time orientation of the constructed frame

Sources: v13 `prop:takabayasi` and `eq:vector_axial_bilinears`.
The actual positive Hermitian square fixes the future sign, while the
derived Clifford normalization bounds the physical time component.
Strict invariant regularity is retained for original-spinor reconstruction.
This does not classify the complete proper Lorentz image or spin covering.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpecialLinearTimeOrientation
open DiracMatrices DiracAdjoint SpinorRegularity
/-- The actual positive Hermitian square vanishes exactly at the zero spinor. -/
theorem hermitianSquare_eq_zero_iff (psi : Spinor) : hermitianSquare psi = 0 ↔ psi = 0 := by
  rw [hermitianSquare, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (psi i))]
  constructor
  · intro h
    funext i
    exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _
    simp [h]
/-- The actual Hermitian square is positive exactly for nonzero spinors. -/
theorem hermitianSquare_pos_iff (psi : Spinor) : 0 < hermitianSquare psi ↔ psi ≠ 0 := by
  constructor
  · intro h hz
    rw [hz] at h
    simp [hermitianSquare] at h
  · intro h
    exact lt_of_le_of_ne (hermitianSquare_nonneg psi)
      (Ne.symm ((hermitianSquare_eq_zero_iff psi).not.mpr h))
/-- Strict invariant regularity implies a positive actual vector-current time component. -/
theorem vector_time_pos_of_regular {psi : Spinor} (hpsi : Regular psi) :
    0 < (bilinear psi (gamma 0) psi).re := by
  rw [← hermitianSquare_vector_time]
  exact (hermitianSquare_pos_iff psi).mpr (regular_ne_zero hpsi)
open ReconstructedFrameGeometry PolarVectorGeometry SpecialLinearFrame
open SpinorMatrix SpecialLinearSpin PolarSpinorBilinears RealLorentzFrame

/-- Every determinant-one representative has a future-directed actual physical time column. -/
theorem frame_time_pos (A : Mat2) (hA : A.det = 1) :
    0 < timeVector (frame A) 0 := by
  let psi := polarSpinor 1 0 (spin A)
  have hr : Regular psi := regular_polar_of_pos 1 0 (spin A) (by norm_num)
    (spin_dirac_isometry A hA) (spin_gamma5_commute A)
  have he := polar_vector_frame 1 0 (L:=spin A) (u:=frame A) (by norm_num)
    (spin_isUnit A hA) (spin_dirac_isometry A hA) (frame_expansion A hA) 0
  have hre := congrArg Complex.re he
  have hp := vector_time_pos_of_regular hr
  change 0 < (bilinear (polarSpinor 1 0 (spin A)) (gamma 0) (polarSpinor 1 0 (spin A))).re at hp
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_re] at hre
  rw [hre] at hp
  exact hp

/-- The actual determinant-one frame time component is at least one by positivity and timelike normalization. -/
theorem frame_time_ge_one (A : Mat2) (hA : A.det = 1) :
    1 ≤ timeVector (frame A) 0 := by
  have hp := frame_time_pos A hA
  have hn := inverse_velocity_normalized (spin_isUnit A hA) (frame_expansion A hA)
  change minkowski (timeVector (frame A)) (timeVector (frame A))=1 at hn
  simp only [minkowski] at hn
  nlinarith [sq_nonneg (timeVector (frame A) 1), sq_nonneg (timeVector (frame A) 2),
    sq_nonneg (timeVector (frame A) 3)]

/-- The time vector reconstructed from an original regular spinor is future directed. -/
theorem reconstructed_time_pos {psi : Spinor} (hpsi : Regular psi) :
    0 < reconstructedTime psi 0 :=
  frame_time_pos _ (RegularPolarReconstruction.normalizedMatrix_det hpsi)

/-- The original regular spinor gives a reconstructed physical time component at least one. -/
theorem reconstructed_time_ge_one {psi : Spinor} (hpsi : Regular psi) :
    1 ≤ reconstructedTime psi 0 :=
  frame_time_ge_one _ (RegularPolarReconstruction.normalizedMatrix_det hpsi)

/-- Positive speed of light gives a positive reconstructed velocity time component. -/
theorem reconstructed_velocity_time_pos {psi : Spinor} (hpsi : Regular psi)
    {c : ℝ} (hc : 0 < c) : 0 < reconstructedVelocity c psi 0 :=
  mul_pos hc (reconstructed_time_pos hpsi)

/-- Nonnegative speed of light bounds the reconstructed velocity time component from below. -/
theorem reconstructed_velocity_time_ge_c {psi : Spinor} (hpsi : Regular psi)
    {c : ℝ} (hc : 0 ≤ c) : c ≤ reconstructedVelocity c psi 0 := by
  change c ≤ c * reconstructedTime psi 0
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (reconstructed_time_ge_one hpsi) hc

end FoliationQM.SpecialLinearTimeOrientation
