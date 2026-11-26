module
public import FoliationQM.SpecialLinearFrameLaws
public import FoliationQM.PolarChartTransitions
public import FoliationQM.PhysicalFrameDifferential
/-!
# Actual frame geometry reconstructed from regular spinors

Sources: v13 `prop:takabayasi` and `eq:vector_axial_bilinears`.
The determinant-one matrix is constructed from the original regular spinor.
Its concrete Dirac representative has a proved real gamma-frame expansion,
so no real frame or normalized velocity and spin are supplied as premises.
The actual vector and axial bilinears of the original spinor identify the
physical time and spin columns, with the explicit speed-of-light factor.
Their Minkowski normalization and orthogonality follow from Clifford algebra.

The rotated smooth branch supplies the same geometry, and the exact
simultaneous two-pi/representative sign transition leaves the entire real
frame unchanged on the overlap. The principal reconstruction is pointwise
on the whole strict regular domain; no global smooth principal angle,
abstract Spin covering, or quotient-bundle classification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.ReconstructedFrameGeometry
open DiracMatrices DiracAdjoint SpinorMatrix SpinorRegularity
open RegularPolarReconstruction RotatedPolarChart RealLorentzFrame
open PolarSpinorBilinears PolarVectorGeometry PhysicalFrameDifferential
open PrincipalPolarSmooth PolarChartTransitions

/-- The actual upper-gamma real frame obtained from the constructed determinant-one matrix. -/
def reconstructedFrame (psi : Spinor) : Fin 4 → Covector :=
  SpecialLinearFrame.frame (normalizedMatrix psi)

/-- The actual upper-gamma real frame obtained from the rotated branch matrix. -/
def rotatedFrame (psi : Spinor) : Fin 4 → Covector :=
  SpecialLinearFrame.frame (rotatedMatrix psi)

/-- The reconstructed physical dimensionless time vector is the temporal inverse-frame column. -/
def reconstructedTime (psi : Spinor) : Covector := timeVector (reconstructedFrame psi)

/-- The reconstructed physical spin vector is the third spatial inverse-frame column. -/
def reconstructedSpinVector (psi : Spinor) : Covector := spinVector (reconstructedFrame psi)

/-- The reconstructed physical velocity is the speed of light times its time vector. -/
def reconstructedVelocity (c : ℝ) (psi : Spinor) : Covector := velocity c (reconstructedFrame psi)

/-- The rotated branch physical time vector uses its actual inverse-frame temporal column. -/
def rotatedTime (psi : Spinor) : Covector := timeVector (rotatedFrame psi)

/-- The rotated branch physical spin vector uses its actual inverse-frame third spatial column. -/
def rotatedSpinVector (psi : Spinor) : Covector := spinVector (rotatedFrame psi)

/-- The rotated branch physical velocity includes the source speed-of-light factor. -/
def rotatedVelocity (c : ℝ) (psi : Spinor) : Covector := velocity c (rotatedFrame psi)

/-- Strict regularity alone gives the original constructed representative its actual real upper-gamma frame expansion. -/
theorem reconstructed_frame_expansion {psi : Spinor} (hpsi : Regular psi) (a : Fin 4) :
    reconstructedSpin psi * gamma a * (reconstructedSpin psi)⁻¹ =
      gammaExpansion (reconstructedFrame psi a) :=
  SpecialLinearFrame.frame_expansion (normalizedMatrix psi) (normalizedMatrix_det hpsi) a

/-- The reconstructed physical source tetrad gives the actual lower-gamma expansion with both metric index signs retained. -/
theorem reconstructed_physical_frame_expansion {psi : Spinor} (hpsi : Regular psi)
    (a : Fin 4) :
    reconstructedSpin psi * gammaLower a * (reconstructedSpin psi)⁻¹ =
      ∑ mu, (physicalFrame (reconstructedFrame psi) a mu : ℂ) • gammaLower mu := by
  simpa only [physicalFrame_eq_inverseColumn] using
    physical_frame_expansion (reconstructed_frame_expansion hpsi) a

/-- The whole physical tetrad constructed from a regular spinor is Minkowski orthonormal without a supplied frame premise. -/
theorem reconstructed_physical_frame_orthonormal {psi : Spinor} (hpsi : Regular psi)
    (a b : Fin 4) :
    minkowski (physicalFrame (reconstructedFrame psi) a)
      (physicalFrame (reconstructedFrame psi) b) = if a = b then sign a else 0 :=
  physicalFrame_orthonormal (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi) a b

/-- The actual vector bilinear of the original regular spinor equals its invariant density times the reconstructed time vector. -/
theorem original_vector {psi : Spinor} (hpsi : Regular psi) (mu : Fin 4) :
    bilinear psi (gamma mu) psi =
      (invariantDensity psi : ℂ) * (reconstructedTime psi mu : ℂ) := by
  have h := polar_vector_frame (invariantDensity psi) (determinantPhase psi)
    (le_of_lt hpsi) (reconstructedSpin_isUnit hpsi)
    (reconstructedSpin_dirac_isometry hpsi) (reconstructed_frame_expansion hpsi) mu
  rw [← regular_reconstruction hpsi] at h
  exact h

/-- The actual axial bilinear of the original regular spinor equals its invariant density times the reconstructed spin vector. -/
theorem original_axial {psi : Spinor} (hpsi : Regular psi) (mu : Fin 4) :
    bilinear psi (gamma mu * gamma5) psi =
      (invariantDensity psi : ℂ) * (reconstructedSpinVector psi mu : ℂ) := by
  have h := polar_axial_frame (invariantDensity psi) (determinantPhase psi)
    (le_of_lt hpsi) (reconstructedSpin_isUnit hpsi)
    (reconstructedSpin_dirac_isometry hpsi) (reconstructedSpin_gamma5_commute psi)
    (reconstructed_frame_expansion hpsi) mu
  rw [← regular_reconstruction hpsi] at h
  exact h

/-- The source physical vector identity includes the exact density-over-speed normalization. -/
theorem original_vector_velocity {psi : Spinor} (hpsi : Regular psi) (c : ℝ)
    (hc : c ≠ 0) (mu : Fin 4) :
    bilinear psi (gamma mu) psi =
      ((invariantDensity psi / c : ℝ) : ℂ) * (reconstructedVelocity c psi mu : ℂ) := by
  have h := polar_vector_velocity (invariantDensity psi) (determinantPhase psi) c hc
    (le_of_lt hpsi) (reconstructedSpin_isUnit hpsi)
    (reconstructedSpin_dirac_isometry hpsi) (reconstructed_frame_expansion hpsi) mu
  rw [← regular_reconstruction hpsi] at h
  exact h

/-- The real vector component is exactly the invariant density times the constructed real time component. -/
theorem original_vector_re {psi : Spinor} (hpsi : Regular psi) (mu : Fin 4) :
    (bilinear psi (gamma mu) psi).re = invariantDensity psi * reconstructedTime psi mu := by
  simpa using congrArg Complex.re (original_vector hpsi mu)

/-- The real axial component is exactly the invariant density times the constructed real spin component. -/
theorem original_axial_re {psi : Spinor} (hpsi : Regular psi) (mu : Fin 4) :
    (bilinear psi (gamma mu * gamma5) psi).re =
      invariantDensity psi * reconstructedSpinVector psi mu := by
  simpa using congrArg Complex.re (original_axial hpsi mu)

/-- The physical time vector constructed from the actual regular spinor has unit timelike Minkowski norm. -/
theorem reconstructed_time_normalized {psi : Spinor} (hpsi : Regular psi) :
    minkowski (reconstructedTime psi) (reconstructedTime psi) = 1 :=
  inverse_velocity_normalized (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi)

/-- The actual reconstructed physical velocity has Minkowski norm squared c squared. -/
theorem reconstructed_velocity_normalized {psi : Spinor} (hpsi : Regular psi) (c : ℝ) :
    minkowski (reconstructedVelocity c psi) (reconstructedVelocity c psi) = c^2 :=
  PolarVectorGeometry.velocity_normalized c (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi)

/-- The actual reconstructed physical spin has unit spacelike Minkowski norm. -/
theorem reconstructed_spin_normalized {psi : Spinor} (hpsi : Regular psi) :
    minkowski (reconstructedSpinVector psi) (reconstructedSpinVector psi) = -1 :=
  spin_normalized (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi)

/-- The actual reconstructed time and spin vectors are Minkowski orthogonal. -/
theorem reconstructed_time_spin_orthogonal {psi : Spinor} (hpsi : Regular psi) :
    minkowski (reconstructedTime psi) (reconstructedSpinVector psi) = 0 :=
  inverse_velocity_spin_orthogonal (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi)

/-- The actual reconstructed physical velocity and spin are Minkowski orthogonal. -/
theorem reconstructed_velocity_spin_orthogonal {psi : Spinor} (hpsi : Regular psi) (c : ℝ) :
    minkowski (reconstructedVelocity c psi) (reconstructedSpinVector psi) = 0 :=
  velocity_spin_orthogonal c (reconstructedSpin_isUnit hpsi) (reconstructed_frame_expansion hpsi)

/-- The rotated branch representative has a derived actual real upper-gamma expansion. -/
theorem rotated_frame_expansion {psi : Spinor} (hpsi : psi ∈ RotatedDomain) (a : Fin 4) :
    rotatedSpin psi * gamma a * (rotatedSpin psi)⁻¹ = gammaExpansion (rotatedFrame psi a) :=
  SpecialLinearFrame.frame_expansion (rotatedMatrix psi) (rotatedMatrix_det hpsi) a

/-- The full rotated physical tetrad inherits Minkowski orthonormality from its actual gamma expansion. -/
theorem rotated_physical_frame_orthonormal {psi : Spinor} (hpsi : psi ∈ RotatedDomain)
    (a b : Fin 4) :
    minkowski (physicalFrame (rotatedFrame psi) a) (physicalFrame (rotatedFrame psi) b) =
      if a = b then sign a else 0 :=
  physicalFrame_orthonormal (rotatedSpin_isUnit hpsi) (rotated_frame_expansion hpsi) a b

/-- The original spinor vector bilinear is realized by the actual time column on the rotated branch. -/
theorem original_vector_rotated {psi : Spinor} (hpsi : psi ∈ RotatedDomain) (mu : Fin 4) :
    bilinear psi (gamma mu) psi =
      (invariantDensity psi : ℂ) * (rotatedTime psi mu : ℂ) := by
  have h := polar_vector_frame (invariantDensity psi) (rotatedPhase psi)
    (le_of_lt (rotatedDomain_regular hpsi)) (rotatedSpin_isUnit hpsi)
    (rotatedSpin_dirac_isometry hpsi) (rotated_frame_expansion hpsi) mu
  rw [← rotated_reconstruction hpsi] at h
  exact h

/-- The original spinor axial bilinear is realized by the actual spin column on the rotated branch. -/
theorem original_axial_rotated {psi : Spinor} (hpsi : psi ∈ RotatedDomain) (mu : Fin 4) :
    bilinear psi (gamma mu * gamma5) psi =
      (invariantDensity psi : ℂ) * (rotatedSpinVector psi mu : ℂ) := by
  have h := polar_axial_frame (invariantDensity psi) (rotatedPhase psi)
    (le_of_lt (rotatedDomain_regular hpsi)) (rotatedSpin_isUnit hpsi)
    (rotatedSpin_dirac_isometry hpsi) (rotatedSpin_gamma5_commute psi)
    (rotated_frame_expansion hpsi) mu
  rw [← rotated_reconstruction hpsi] at h
  exact h

/-- The actual rotated-branch physical velocity has Minkowski norm squared c squared. -/
theorem rotated_velocity_normalized {psi : Spinor} (hpsi : psi ∈ RotatedDomain) (c : ℝ) :
    minkowski (rotatedVelocity c psi) (rotatedVelocity c psi) = c^2 :=
  PolarVectorGeometry.velocity_normalized c (rotatedSpin_isUnit hpsi) (rotated_frame_expansion hpsi)

/-- The actual rotated-branch physical spin has unit spacelike Minkowski norm. -/
theorem rotated_spin_normalized {psi : Spinor} (hpsi : psi ∈ RotatedDomain) :
    minkowski (rotatedSpinVector psi) (rotatedSpinVector psi) = -1 :=
  spin_normalized (rotatedSpin_isUnit hpsi) (rotated_frame_expansion hpsi)

/-- The actual rotated-branch physical velocity and spin are Minkowski orthogonal. -/
theorem rotated_velocity_spin_orthogonal {psi : Spinor} (hpsi : psi ∈ RotatedDomain) (c : ℝ) :
    minkowski (rotatedVelocity c psi) (rotatedSpinVector psi) = 0 :=
  velocity_spin_orthogonal c (rotatedSpin_isUnit hpsi) (rotated_frame_expansion hpsi)

/-- The rotated branch and pointwise principal reconstruction give the same entire real frame, including at the principal argument cut, by the actual polar-fiber sign classification. -/
theorem rotatedFrame_eq {psi : Spinor} (hr : psi ∈ RotatedDomain) :
    rotatedFrame psi = reconstructedFrame psi := by
  have hreg := rotatedDomain_regular hr
  have heq : polarSpinor (invariantDensity psi) (rotatedPhase psi)
      (SpecialLinearSpin.spin (rotatedMatrix psi)) =
      polarSpinor (invariantDensity psi) (determinantPhase psi)
        (SpecialLinearSpin.spin (normalizedMatrix psi)) :=
    (rotated_reconstruction hr).symm.trans (regular_reconstruction hreg)
  have hf := (PolarAngleFibers.polarSpinor_fixedDensity_phase_fibers
    (invariantDensity psi) (rotatedPhase psi) (determinantPhase psi)
    (rotatedMatrix psi) (normalizedMatrix psi) hreg (rotatedMatrix_det hr)
    (normalizedMatrix_det hreg)).mp heq
  rcases hf with h | h
  · simp only [rotatedFrame, reconstructedFrame, h.2]
  · simp only [rotatedFrame, reconstructedFrame, h.2, SpecialLinearFrameLaws.frame_neg]

/-- The entire reconstructed real frame is unchanged across the explicit principal-to-rotated overlap transition. -/
theorem rotatedFrame_eq_on_overlap {psi : Spinor} (_hp : psi ∈ PrincipalDomain)
    (hr : psi ∈ RotatedDomain) : rotatedFrame psi = reconstructedFrame psi :=
  rotatedFrame_eq hr

/-- The rotated and pointwise principal reconstructions give the same physical time vector on the whole rotated branch. -/
theorem rotatedTime_eq {psi : Spinor} (hr : psi ∈ RotatedDomain) :
    rotatedTime psi = reconstructedTime psi := by
  rw [rotatedTime, reconstructedTime, rotatedFrame_eq hr]

/-- The rotated and pointwise principal reconstructions give the same physical spin vector on the whole rotated branch. -/
theorem rotatedSpinVector_eq {psi : Spinor} (hr : psi ∈ RotatedDomain) :
    rotatedSpinVector psi = reconstructedSpinVector psi := by
  rw [rotatedSpinVector, reconstructedSpinVector, rotatedFrame_eq hr]

/-- The rotated and pointwise principal reconstructions give the same physical velocity on the whole rotated branch. -/
theorem rotatedVelocity_eq {psi : Spinor} (hr : psi ∈ RotatedDomain) (c : ℝ) :
    rotatedVelocity c psi = reconstructedVelocity c psi := by
  rw [rotatedVelocity, reconstructedVelocity, rotatedFrame_eq hr]

end FoliationQM.ReconstructedFrameGeometry
