module

public import FoliationQM.ConeRadialCompletion
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Radial rigidity of arbitrary tip-preserving completed Euclidean isometries

Source: v13 `lem:uniqueness`, a structural step toward coordinate-independent
necessity. An arbitrary isometry of the genuine cone completion to the complex
plane which sends its tip to zero preserves positive radial scaling. This is
derived from exact intrinsic radial distances and strict convexity of the
Euclidean norm, without prescribing a power-coordinate formula. After removing
the source radial scale, its angular part is an actual circle homeomorphism.
No existence of such an isometry, or canonical-coupling necessity, is assumed
or concluded by this reduction.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.ConeIsometryRigidity

open ConeCompletion ConeRadial UniformSpace

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]
variable (E : Completed hbar coupling ≃ᵢ ℂ) (hE : E (tip hbar coupling) = 0)

include hE

/-- Any tip-preserving completed Euclidean isometry has the exact intrinsic
radial norm, independent of its possible angular behavior. -/
theorem norm_image (x : Completed hbar coupling) :
    ‖E x‖ = radialScale hbar coupling * ‖coordinate hbar coupling x‖ := by
  have h := E.dist_eq x (tip hbar coupling)
  rw [hE, dist_zero_right, ConeRadialCompletion.dist_tip] at h
  exact h

/-- Equality in the reverse triangle inequality forces images of positive
physical radial multiples onto the same Euclidean ray. -/
theorem sameRay_image (p q : ConeManifold.Point hbar coupling)
    (s : ℝ) (hs : 0 < s) (hq : q.value = (s : ℂ) * p.value) :
    SameRay ℝ (E (p : Completed hbar coupling)) (E (q : Completed hbar coupling)) := by
  apply sameRay_iff_norm_sub.mpr
  rw [← dist_eq_norm, E.dist_eq, Completion.dist_eq,
    dist_smul hbar coupling p q s hs hq,
    norm_image hbar coupling E hE, norm_image hbar coupling E hE,
    coordinate_coe, coordinate_coe, hq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]
  have ha := radialScale_pos hbar coupling Fact.out Fact.out
  calc
    radialScale hbar coupling * |1 - s| * ‖p.value‖ =
        |radialScale hbar coupling * ‖p.value‖ * (1 - s)| := by
      rw [abs_mul, abs_mul, abs_of_pos ha, abs_norm]
      ring
    _ = |radialScale hbar coupling * ‖p.value‖ -
        radialScale hbar coupling * (s * ‖p.value‖)| := by congr 1; ring

/-- An arbitrary tip-preserving completed Euclidean isometry is homogeneous
on every positive physical radial ray. No coordinate ansatz is imposed. -/
theorem image_smul (p q : ConeManifold.Point hbar coupling)
    (s : ℝ) (hs : 0 < s) (hq : q.value = (s : ℂ) * p.value) :
    E (q : Completed hbar coupling) = s • E (p : Completed hbar coupling) := by
  have h := (sameRay_image hbar coupling E hE p q s hs hq).norm_smul_eq
  have hn : ‖E (q : Completed hbar coupling)‖ =
      s * ‖E (p : Completed hbar coupling)‖ := by
    rw [norm_image hbar coupling E hE, norm_image hbar coupling E hE,
      coordinate_coe, coordinate_coe, hq, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
    ring
  have hp : ‖E (p : Completed hbar coupling)‖ ≠ 0 := by
    rw [norm_image hbar coupling E hE, coordinate_coe]
    exact mul_ne_zero (radialScale_pos hbar coupling Fact.out Fact.out).ne'
      (norm_ne_zero_iff.mpr p.value_ne_zero)
  rw [hn, mul_comm s, mul_smul] at h
  exact (smul_right_injective ℂ hp) h

/-- The physical-coordinate conjugate of an arbitrary completed isometry,
normalized by its forced positive radial scale. -/
def normalizedHomeomorph : ℂ ≃ₜ ℂ :=
  ((complexHomeomorph hbar coupling).symm.trans E.toHomeomorph).trans
    (Homeomorph.smulOfNeZero (radialScale hbar coupling)
      (radialScale_pos hbar coupling Fact.out Fact.out).ne' : ℂ ≃ₜ ℂ).symm

/-- The normalized homeomorphism preserves physical amplitude exactly. -/
theorem norm_normalizedHomeomorph (z : ℂ) :
    ‖normalizedHomeomorph hbar coupling E z‖ = ‖z‖ := by
  change ‖(radialScale hbar coupling)⁻¹ •
    E ((complexHomeomorph hbar coupling).symm z)‖ = ‖z‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos
    (inv_pos.mpr (radialScale_pos hbar coupling Fact.out Fact.out)),
    norm_image hbar coupling E hE]
  change (radialScale hbar coupling)⁻¹ *
    (radialScale hbar coupling * ‖(complexHomeomorph hbar coupling)
      ((complexHomeomorph hbar coupling).symm z)‖) = ‖z‖
  rw [Homeomorph.apply_symm_apply, inv_mul_cancel_left₀
    (radialScale_pos hbar coupling Fact.out Fact.out).ne']

/-- Every arbitrary tip-preserving completed Euclidean isometry induces an
actual homeomorphism of the physical phase circle after radial normalization. -/
def angularHomeomorph : Circle ≃ₜ Circle :=
  (normalizedHomeomorph hbar coupling E).subtype (fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      normalizedHomeomorph hbar coupling E z ∈ Metric.sphere (0 : ℂ) 1
    simp only [mem_sphere_zero_iff_norm, norm_normalizedHomeomorph hbar coupling E hE])

/-- The angular homeomorphism is the normalized image of the completed point
with the supplied unit physical complex coordinate. -/
theorem angularHomeomorph_coe (q : Circle) :
    (angularHomeomorph hbar coupling E hE q : ℂ) =
      (radialScale hbar coupling)⁻¹ •
        E ((complexHomeomorph hbar coupling).symm (q : ℂ)) := rfl

/-- Every arbitrary isometry has a polar formula with the forced radial scale
and its induced circle homeomorphism. The physical phase here is exactly
`p.value / norm p.value`, supplied by the existing polar inverse. -/
theorem image_polar (p : ConeManifold.Point hbar coupling) :
    E (p : Completed hbar coupling) =
      (radialScale hbar coupling * ‖p.value‖) •
        (angularHomeomorph hbar coupling E hE
          (ConeIntrinsicMetric.canonicalEquiv hbar coupling p).phase : ℂ) := by
  let u : Circle := (ConeIntrinsicMetric.canonicalEquiv hbar coupling p).phase
  let q : ConeManifold.Point hbar coupling := ⟨(u : ℂ), u.coe_ne_zero⟩
  have hu : (u : ℂ) = p.value / (‖p.value‖ : ℂ) := rfl
  have hp : 0 < ‖p.value‖ := norm_pos_iff.mpr p.value_ne_zero
  have hq : p.value = ((‖p.value‖ : ℝ) : ℂ) * q.value := by
    change p.value = (‖p.value‖ : ℂ) * (u : ℂ)
    rw [hu]
    field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
  have hcoe : (complexHomeomorph hbar coupling).symm (u : ℂ) =
      (q : Completed hbar coupling) := by
    apply (complexHomeomorph hbar coupling).injective
    rw [Homeomorph.apply_symm_apply]
    exact (coordinate_coe hbar coupling q).symm
  change E (p : Completed hbar coupling) =
    (radialScale hbar coupling * ‖p.value‖) •
      (angularHomeomorph hbar coupling E hE u : ℂ)
  rw [angularHomeomorph_coe, hcoe, ← mul_smul]
  have hcancel : (radialScale hbar coupling * ‖p.value‖) *
      (radialScale hbar coupling)⁻¹ = ‖p.value‖ := by
    field_simp [(radialScale_pos hbar coupling Fact.out Fact.out).ne']
  rw [hcancel]
  exact image_smul hbar coupling E hE q p ‖p.value‖ hp hq

end FoliationQM.ConeIsometryRigidity
