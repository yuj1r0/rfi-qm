module

public import FoliationQM.ConeIsometryRigidity
public import FoliationQM.ConeRotations
public import FoliationQM.EuclideanRotationAction
public import FoliationQM.CircleAutomorphism

/-!
# Coordinate rigidity of arbitrary Euclidean cone-completion isometries

Source: v13 `lem:uniqueness`. No formula for the unknown isometry is
prescribed. Genuine cone rotations, Euclidean isometry classification,
continuous circle-character classification, and exact radial distances
force a fixed complex rotation or reflection times the intrinsic radial
scale. The separate local-distance argument must still select that scale.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeEuclideanRigidity

open ConeCompletion ConeRotations ConeIsometryRigidity ConeRadial
open EuclideanRotationAction UniformSpace
open scoped ComplexConjugate

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]
variable (E : Completed hbar coupling ≃ᵢ ℂ) (hE : E (tip hbar coupling) = 0)

/-- Transport the genuine physical rotation action through an arbitrary
completed Euclidean isometry. -/
def conjugatedRotation (q : Circle) : ℂ ≃ᵢ ℂ :=
  (E.symm.trans (completedRotation hbar coupling q)).trans E

/-- Its value is the actual composition of the original isometries. -/
theorem conjugatedRotation_apply (q : Circle) (z : ℂ) :
    conjugatedRotation hbar coupling E q z =
      E (completedRotation hbar coupling q (E.symm z)) := rfl

include hE in
/-- The conjugated action fixes the Euclidean origin. -/
theorem conjugatedRotation_zero (q : Circle) :
    conjugatedRotation hbar coupling E q 0 = 0 := by
  have h0 : E.symm 0 = tip hbar coupling := by
    apply E.injective
    rw [E.apply_symm_apply, hE]
  rw [conjugatedRotation_apply, h0, completedRotation_tip, hE]

/-- The genuine identity rotation remains the identity after conjugation. -/
theorem conjugatedRotation_one (z : ℂ) :
    conjugatedRotation hbar coupling E 1 z = z := by
  rw [conjugatedRotation_apply, completedRotation_one, E.apply_symm_apply]

/-- Conjugation preserves the physical-circle composition law. -/
theorem conjugatedRotation_mul (q r : Circle) (z : ℂ) :
    conjugatedRotation hbar coupling E (q * r) z =
      conjugatedRotation hbar coupling E q (conjugatedRotation hbar coupling E r z) := by
  simp only [conjugatedRotation_apply, E.symm_apply_apply, completedRotation_mul]

/-- The transported action is faithful, since its original action on a
point of physical coordinate one distinguishes every phase. -/
theorem conjugatedRotation_faithful (q r : Circle)
    (h : ∀ z, conjugatedRotation hbar coupling E q z =
      conjugatedRotation hbar coupling E r z) : q = r := by
  let p : ConeManifold.Point hbar coupling := ⟨1, one_ne_zero⟩
  have he := E.injective (h (E (p : Completed hbar coupling)))
  change completedRotation hbar coupling q (E.symm (E (p : Completed hbar coupling))) =
    completedRotation hbar coupling r (E.symm (E (p : Completed hbar coupling))) at he
  rw [E.symm_apply_apply] at he
  have hc := congrArg (coordinate hbar coupling) he
  simp only [coordinate_completedRotation, coordinate_coe, p, mul_one] at hc
  exact Subtype.ext hc

/-- The physical coordinate formula makes each conjugated orbit continuous
in its circle parameter, including for an arbitrary unknown isometry. -/
theorem continuous_conjugatedRotation (z : ℂ) :
    Continuous (fun q => conjugatedRotation hbar coupling E q z) := by
  have he (q : Circle) : completedRotation hbar coupling q (E.symm z) =
      (complexHomeomorph hbar coupling).symm
        ((q : ℂ) * coordinate hbar coupling (E.symm z)) := by
    apply (complexHomeomorph hbar coupling).injective
    exact (coordinate_completedRotation hbar coupling q (E.symm z)).trans
      ((complexHomeomorph hbar coupling).apply_symm_apply _).symm
  simp only [conjugatedRotation_apply, he]
  exact E.continuous.comp ((complexHomeomorph hbar coupling).symm.continuous.comp
    (continuous_subtype_val.mul continuous_const))

/-- The actual multiplier character of the conjugated physical rotation action. -/
def rotationCharacter : Circle →* Circle :=
  actionCharacter (conjugatedRotation hbar coupling E)
    (conjugatedRotation_zero hbar coupling E hE)
    (conjugatedRotation_one hbar coupling E)
    (conjugatedRotation_mul hbar coupling E)

/-- The character is continuous by the actual continuity of the rotation action. -/
theorem continuous_rotationCharacter : Continuous (rotationCharacter hbar coupling E hE) :=
  continuous_actionCharacter _ _ _ _ (continuous_conjugatedRotation hbar coupling E 1)

/-- The character is injective by the proved faithfulness of physical rotations. -/
theorem injective_rotationCharacter : Function.Injective (rotationCharacter hbar coupling E hE) :=
  injective_actionCharacter _ _ _ _ (conjugatedRotation_faithful hbar coupling E)

include hE in
/-- Every arbitrary completed Euclidean isometry intertwines physical rotations
either with the same rotations or with the reversed rotations, globally. -/
theorem rotation_intertwining :
    (∀ q : Circle, ∀ x : Completed hbar coupling,
      E (completedRotation hbar coupling q x) = (q : ℂ) * E x) ∨
    (∀ q : Circle, ∀ x : Completed hbar coupling,
      E (completedRotation hbar coupling q x) = conj (q : ℂ) * E x) := by
  have hact (q : Circle) (z : ℂ) : conjugatedRotation hbar coupling E q z =
      (rotationCharacter hbar coupling E hE q : ℂ) * z :=
    action_apply _ (conjugatedRotation_zero hbar coupling E hE)
      (conjugatedRotation_mul hbar coupling E) q z
  obtain h | h := CircleAutomorphism.continuous_injective_hom_coe_eq_id_or_conj
    (rotationCharacter hbar coupling E hE) (continuous_rotationCharacter hbar coupling E hE)
    (injective_rotationCharacter hbar coupling E hE)
  · left
    intro q x
    simpa only [conjugatedRotation_apply, E.symm_apply_apply, h] using hact q (E x)
  · right
    intro q x
    simpa only [conjugatedRotation_apply, E.symm_apply_apply, h, Complex.star_def]
      using hact q (E x)

include hE in
/-- Exact radial homogeneity and the rotation action force a fixed multiplier
or its reflected counterpart on every original point, with no coordinate ansatz. -/
theorem original_coordinate_formula :
    ∃ b : ℂ, ‖b‖ = radialScale hbar coupling ∧
      ((∀ p : ConeManifold.Point hbar coupling,
        E (p : Completed hbar coupling) = b * p.value) ∨
       (∀ p : ConeManifold.Point hbar coupling,
        E (p : Completed hbar coupling) = b * conj p.value)) := by
  let u : ConeManifold.Point hbar coupling := ⟨1, one_ne_zero⟩
  refine ⟨E (u : Completed hbar coupling), ?_, ?_⟩
  · simpa only [coordinate_coe, u, norm_one, mul_one] using
      norm_image hbar coupling E hE (u : Completed hbar coupling)
  have hrad (p : ConeManifold.Point hbar coupling) :
      E (p : Completed hbar coupling) = ‖p.value‖ •
        E (rotate (ConeIntrinsicMetric.canonicalEquiv hbar coupling p).phase u :
          Completed hbar coupling) := by
    apply image_smul hbar coupling E hE _ p ‖p.value‖ (norm_pos_iff.mpr p.value_ne_zero)
    change p.value = (‖p.value‖ : ℂ) * (p.value / (‖p.value‖ : ℂ) * 1)
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr p.value_ne_zero)]
  obtain h | h := rotation_intertwining hbar coupling E hE
  · left
    intro p
    rw [hrad, ← completedRotation_coe, h]
    change (‖p.value‖ : ℂ) * (p.value / (‖p.value‖ : ℂ) * E (u : Completed hbar coupling)) = _
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr p.value_ne_zero)]
  · right
    intro p
    rw [hrad, ← completedRotation_coe, h]
    change (‖p.value‖ : ℂ) *
      (conj (p.value / (‖p.value‖ : ℂ)) * E (u : Completed hbar coupling)) = _
    rw [map_div₀, Complex.conj_ofReal]
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr p.value_ne_zero)]

include hE in
/-- Density and continuity extend the forced rotation/reflection formula
to every point of the genuine completion, including its tip. -/
theorem completed_coordinate_formula :
    ∃ b : ℂ, ‖b‖ = radialScale hbar coupling ∧
      ((∀ x : Completed hbar coupling, E x = b * coordinate hbar coupling x) ∨
       (∀ x : Completed hbar coupling, E x = b * conj (coordinate hbar coupling x))) := by
  obtain ⟨b, hb, h | h⟩ := original_coordinate_formula hbar coupling E hE
  · refine ⟨b, hb, Or.inl ?_⟩
    intro x
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq E.continuous
        (continuous_const.mul (complexHomeomorph hbar coupling).continuous)
    · intro p
      rw [coordinate_coe]
      exact h p
  · refine ⟨b, hb, Or.inr ?_⟩
    intro x
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq E.continuous
        (continuous_const.mul (Complex.continuous_conj.comp
          (complexHomeomorph hbar coupling).continuous))
    · intro p
      rw [coordinate_coe]
      exact h p

include hE in
/-- Existence of any tip-preserving Euclidean completed isometry would force
every intrinsic distance to be the same radial-scale multiple of chord distance. -/
theorem dist_eq_scaled_chord (x y : Completed hbar coupling) :
    dist x y = radialScale hbar coupling *
      dist (coordinate hbar coupling x) (coordinate hbar coupling y) := by
  obtain ⟨b, hb, h | h⟩ := completed_coordinate_formula hbar coupling E hE
  · rw [← E.dist_eq, h, h, dist_eq_norm, ← mul_sub, norm_mul, hb, dist_eq_norm]
  · rw [← E.dist_eq, h, h, dist_eq_norm, ← mul_sub, norm_mul, hb,
      ← map_sub, Complex.norm_conj, dist_eq_norm]

/-- Any Euclidean isometry can be centered at the image of the cone tip
using an actual Euclidean translation isometry. -/
def centeredIsometry : Completed hbar coupling ≃ᵢ ℂ :=
  E.trans (IsometryEquiv.addRight (-E (tip hbar coupling)))

/-- Centering subtracts the actual image of the unique tip. -/
theorem centeredIsometry_apply (x : Completed hbar coupling) :
    centeredIsometry hbar coupling E x = E x - E (tip hbar coupling) := by
  simp only [centeredIsometry, IsometryEquiv.trans_apply, IsometryEquiv.addRight_apply,
    sub_eq_add_neg]

/-- The centered isometry satisfies the origin condition used in the rigidity proof. -/
theorem centeredIsometry_tip : centeredIsometry hbar coupling E (tip hbar coupling) = 0 := by
  rw [centeredIsometry_apply, sub_self]

include E in
/-- Without any condition on the image of the tip, existence of an arbitrary
Euclidean completed isometry forces the scaled-chord formula intrinsically. -/
theorem dist_eq_scaled_chord_of_isometry (x y : Completed hbar coupling) :
    dist x y = radialScale hbar coupling *
      dist (coordinate hbar coupling x) (coordinate hbar coupling y) :=
  dist_eq_scaled_chord hbar coupling (centeredIsometry hbar coupling E)
    (centeredIsometry_tip hbar coupling E) x y

end FoliationQM.ConeEuclideanRigidity
