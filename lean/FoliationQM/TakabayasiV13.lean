module
public import FoliationQM.CliffordSpinCocycleSections
public import FoliationQM.ReconstructedFrameConnection

/-!
# Observable angle and bilinears in the v13 Takabayasi proposition

The global smooth data of `prop:takabayasi` are the positive density and
the Clifford frame sign class. A real angle in [0,2π) selects a unique
pointwise representative. Its spin rotor determines the same physical
tetrad as the original regular spinor. Smooth real representatives are
local, and use the already established polar covering charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TakabayasiV13
open Set DiracMatrices DiracAdjoint SpinorRegularity PolarSpinorBilinears RegularPolarReconstruction
open CliffordSpinMap CliffordSpinEquivalence CliffordSpinPolarRealization PolarAmplitudeTopology
open ChiralAngleCircle SpecialLinearSpin PolarVectorGeometry ReconstructedFrameGeometry
open PhysicalFrameDifferential RealLorentzFrame

private theorem unique_in_half_period {ρ : PositiveDensity} {a b : ℝ} (ha : a ∈ Ico 0 (2*Real.pi))
    (hb : b ∈ Ico 0 (2*Real.pi)) {s t : Spin}
    (he : polarSpinor ρ a (CliffordMinkowski.dirac s.val) = polarSpinor ρ b (CliffordMinkowski.dirac t.val)) :
    a = b ∧ s = t := by
  let d := (ρ, (a : Angle), s)
  let e := (ρ, (b : Angle), t)
  have hd : realizeSource d = realizeSource e := Subtype.ext (by simpa only [d, e, realizeSource_coe] using he)
  have h := ((realizeSource_coordinate_fibers d e).mp hd).2
  let : Fact (0 < 4 * Real.pi) := ⟨by positivity⟩
  have mem {y : ℝ} (hy : y ∈ Ico 0 (2*Real.pi)) : y ∈ Ico (0 : ℝ) (0+4*Real.pi) :=
    ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,_⟩
  · exact ⟨(AddCircle.coe_eq_coe_iff_of_mem_Ico (mem ha) (mem hb)).mp h₁,h₂⟩
  · have hb' : b+2*Real.pi ∈ Ico (0:ℝ) (0+4*Real.pi) := ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2]⟩
    have h' : (a : Angle) = ((b+2*Real.pi : ℝ) : Angle) := by
      simpa only [AddCircle.coe_add] using h₁
    have ha' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (mem ha) hb').mp h'
    exfalso
    linarith [ha.2, hb.1]

/-- Every strictly regular spinor has exactly one genuine Clifford-Spin representative
when its real chiral angle is required to lie in [0,2π). -/
theorem regular_representative {ψ : Spinor} (hψ : Regular ψ) :
    ∃! p : Ico (0 : ℝ) (2 * Real.pi) × Spin,
      ψ = polarSpinor (invariantDensity ψ) p.1.val (CliffordMinkowski.dirac p.2.val) := by
  let b := determinantPhase ψ
  let A : SourcePolarDatum.SpecialLinearMatrix := ⟨normalizedMatrix ψ, normalizedMatrix_det hψ⟩
  let s := spinEquiv.symm A
  have hb := determinantPhase_bounds ψ
  have hs : CliffordMinkowski.dirac s.val = reconstructedSpin ψ := dirac_spinEquiv_symm A
  have hrep : ∃ p : Ico (0 : ℝ) (2 * Real.pi) × Spin,
      ψ = polarSpinor (invariantDensity ψ) p.1.val (CliffordMinkowski.dirac p.2.val) := by
    by_cases hz : 0 ≤ b
    · exact ⟨(⟨b, hz, by dsimp [b]; linarith [hb.2, Real.pi_pos]⟩, s), hs ▸ regular_reconstruction hψ⟩
    · have hneg : CliffordMinkowski.dirac (negativeOne * s).val = -reconstructedSpin ψ := by
        change CliffordMinkowski.dirac (negativeOne.val * s.val) = _
        rw [map_mul, negativeOne_coe, map_neg, map_one, neg_one_mul, hs]
      refine ⟨(⟨b + 2*Real.pi, ?_, ?_⟩, negativeOne*s), ?_⟩
      · dsimp [b]; linarith [hb.1, Real.pi_pos]
      · linarith
      · rw [hneg]
        exact reconstruction_shift_neg hψ
  obtain ⟨p, hp⟩ := hrep
  refine ⟨p, hp, fun q hq => ?_⟩
  have hu := unique_in_half_period (ρ := ⟨invariantDensity ψ, hψ⟩) q.1.property p.1.property (hq.symm.trans hp)
  exact Prod.ext (Subtype.ext hu.1) hu.2

/-- The Dirac matrix of an actual Spin rotor has adjoint equal to inverse. Its lower-index
forward conjugation and upper-index inverse conjugation give the same physical tetrad. -/
theorem rotor_tetrad (s : Spin) :
    let L := CliffordMinkowski.dirac s.val
    let T := physicalFrame (SpecialLinearFrame.frame (toMatrix s).val)
    diracAdjoint L = L⁻¹ ∧
    (∀ a, L * gammaLower a * L⁻¹ = ∑ μ, (T a μ : ℂ) • gammaLower μ) ∧
    (∀ μ, L⁻¹ * gamma μ * L = ∑ a, (T a μ : ℂ) • gamma a) ∧
    (∀ a b, minkowski (T a) (T b) = if a = b then sign a else 0) := by
  rw [dirac_eq_spin]
  dsimp only
  have hd := (toMatrix s).property
  have hunit := spin_isUnit _ hd
  have hf := SpecialLinearFrame.frame_expansion _ hd
  refine ⟨(spin_inverse _ hd).symm, fun a => ?_, fun μ => ?_, physicalFrame_orthonormal hunit hf⟩
  · simpa only [physicalFrame_eq_inverseColumn] using physical_frame_expansion hf a
  · simpa only [physicalFrame_eq_inverseColumn, gammaExpansion] using inverse_expansion hunit hf μ

/-- Any genuine representative of a positive-density spinor gives its scalar and
pseudoscalar bilinears, the physical vector and axial-vector components, and the
normalized velocity and spin of the same represented tetrad. -/
theorem representative_observables {ψ : Spinor} {ρ : PositiveDensity} {β : ℝ} {s : Spin}
    (hψ : ψ = polarSpinor ρ β (CliffordMinkowski.dirac s.val)) (c : ℝ) (hc : c ≠ 0) :
    let u := SpecialLinearFrame.frame (toMatrix s).val
    invariantDensity ψ = (ρ : ℝ) ∧ reconstructedFrame ψ = u ∧
    bilinear ψ 1 ψ = (ρ : ℂ) * (Real.cos β : ℂ) ∧
    -Complex.I * bilinear ψ gamma5 ψ = (ρ : ℂ) * (Real.sin β : ℂ) ∧
    (∀ μ, bilinear ψ (gamma μ) ψ = ((ρ / c : ℝ) : ℂ) * (velocity c u μ : ℂ) ∧
      bilinear ψ (gamma μ * gamma5) ψ = (ρ : ℂ) * (spinVector u μ : ℂ)) ∧
    minkowski (velocity c u) (velocity c u) = c^2 ∧
    minkowski (spinVector u) (spinVector u) = -1 ∧ minkowski (velocity c u) (spinVector u) = 0 := by
  rw [dirac_eq_spin] at hψ
  subst ψ
  let A := (toMatrix s).val
  have hd : A.det = 1 := (toMatrix s).property
  have hi := spin_dirac_isometry A hd
  have h5 := spin_gamma5_commute A
  have hu := spin_isUnit A hd
  have hf := SpecialLinearFrame.frame_expansion A hd
  exact ⟨invariantDensity_polar ρ β (spin A) ρ.property.le hi h5,
    ReconstructedFrameConnection.reconstructedFrame_of_polar ρ β A ρ.property hd,
    polar_scalar ρ β (spin A) ρ.property.le hi h5, polar_pseudoscalar ρ β (spin A) ρ.property.le hi h5,
    fun μ => ⟨polar_vector_velocity ρ β c hc ρ.property.le hu hi hf μ,
      polar_axial_frame ρ β ρ.property.le hu hi h5 hf μ⟩,
    PolarVectorGeometry.velocity_normalized c hu hf, spin_normalized hu hf, velocity_spin_orthogonal c hu hf⟩

end FoliationQM.TakabayasiV13
