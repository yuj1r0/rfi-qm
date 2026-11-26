module

public import FoliationQM.ConeCompletion

/-!
# Physical rotations of the genuine intrinsic cone and its completion

Source: v13 `lem:uniqueness`, symmetry of the actual positive-coupling cone.
Unit complex multiplication preserves the source tensor, its square-root
speed, and actual differentiated curve lengths. Transporting C1 paths in both
directions proves invariance of the intrinsic path infimum. The resulting
isometries extend to the genuine metric completion, retain their physical
coordinate formula, and fix its unique tip. No path-length preservation or
Euclidean isometry of a noncanonical cone is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeRotations

open Set MeasureTheory Topology UniformSpace ConeManifold ConeIntrinsicMetric ConeCompletion
open scoped ComplexConjugate ENNReal Manifold

variable {hbar coupling : ℝ}

/-- Physical rotation of a nonzero cone coordinate. -/
def rotate (q : Circle) (p : Point hbar coupling) : Point hbar coupling :=
  ⟨(q : ℂ) * p.value, mul_ne_zero q.coe_ne_zero p.value_ne_zero⟩

/-- Rotation has its ordinary physical complex-coordinate formula. -/
theorem rotate_value (q : Circle) (p : Point hbar coupling) :
    (rotate q p).value = (q : ℂ) * p.value := rfl

/-- The unit phase acts identically. -/
theorem rotate_one (p : Point hbar coupling) : rotate 1 p = p := by
  apply value_injective
  simp [rotate]

/-- Composition agrees with multiplication of physical phases. -/
theorem rotate_mul (q r : Circle) (p : Point hbar coupling) :
    rotate (q * r) p = rotate q (rotate r p) := by
  apply value_injective
  simp [rotate, mul_assoc]

/-- The inverse physical phase reverses rotation. -/
theorem rotate_inv_rotate (q : Circle) (p : Point hbar coupling) :
    rotate q⁻¹ (rotate q p) = p := by
  rw [← rotate_mul, inv_mul_cancel, rotate_one]

/-- Rotation followed by its inverse is also the identity. -/
theorem rotate_rotate_inv (q : Circle) (p : Point hbar coupling) :
    rotate q (rotate q⁻¹ p) = p := by
  rw [← rotate_mul, mul_inv_cancel, rotate_one]

/-- Multiplication by a physical phase preserves the complex Hermitian product. -/
theorem conj_mul_rotate (q : Circle) (v w : ℂ) :
    conj ((q : ℂ) * v) * ((q : ℂ) * w) = conj v * w := by
  rw [map_mul]
  calc
    conj (q : ℂ) * conj v * ((q : ℂ) * w) =
        (conj (q : ℂ) * (q : ℂ)) * (conj v * w) := by ring
    _ = conj v * w := by
      rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_mul_cancel₀ q.coe_ne_zero, one_mul]

/-- The Euclidean part of the source tensor is rotation invariant. -/
theorem euclidean_rotate (q : Circle) (v w : ℂ) :
    ConeMetricExtension.euclidean ((q : ℂ) * v) ((q : ℂ) * w) =
      ConeMetricExtension.euclidean v w := by
  unfold ConeMetricExtension.euclidean
  rw [conj_mul_rotate]

/-- The radial pairing is invariant when both base point and vector rotate. -/
theorem radial_rotate (q : Circle) (z v : ℂ) :
    ConeMetricExtension.radial ((q : ℂ) * z) ((q : ℂ) * v) =
      ConeMetricExtension.radial z v := by
  unfold ConeMetricExtension.radial
  rw [conj_mul_rotate]

/-- The full source tensor, including its noncanonical radial coefficient,
is invariant under actual physical rotations. -/
theorem tensor_rotate (hbar coupling : ℝ) (q : Circle) (z v w : ℂ) :
    ConeMetricExtension.tensor hbar coupling ((q : ℂ) * z)
      ((q : ℂ) * v) ((q : ℂ) * w) = ConeMetricExtension.tensor hbar coupling z v w := by
  simp only [ConeMetricExtension.tensor, euclidean_rotate, radial_rotate,
    Complex.normSq_mul, Circle.normSq_coe, one_mul]

/-- The actual source speed is invariant under rotation. -/
theorem speed_rotate (hbar coupling : ℝ) (q : Circle) (z v : ℂ) :
    ConeSpeed.speed hbar coupling ((q : ℂ) * z) ((q : ℂ) * v) =
      ConeSpeed.speed hbar coupling z v := by
  unfold ConeSpeed.speed
  rw [tensor_rotate]

/-- Constant complex rotation commutes with the actual real derivative,
including its totalized value at points of nondifferentiability. -/
theorem deriv_rotate (q : Circle) (γ : ℝ → ℂ) (t : ℝ) :
    deriv (fun u => (q : ℂ) * γ u) t = (q : ℂ) * deriv γ t :=
  deriv_const_mul_field (q : ℂ)

/-- Actual weighted curve lengths are rotation invariant, proved from their
derivatives and source speeds without a length-preservation premise. -/
theorem curveELength_rotate (hbar coupling : ℝ) (q : Circle) (γ : ℝ → ℂ) :
    ConeSpeed.curveELength hbar coupling (fun t => (q : ℂ) * γ t) =
      ConeSpeed.curveELength hbar coupling γ := by
  unfold ConeSpeed.curveELength
  apply lintegral_congr
  intro t
  dsimp only
  rw [deriv_rotate, speed_rotate]

/-- Rotation carries every actual C1 manifold path to another C1 path. -/
theorem contMDiffOn_rotate_curve (q : Circle) {γ : ℝ → Point hbar coupling} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (fun t => rotate q (γ t)) s := by
  apply contMDiffOn_curve_of_contDiffOn_value
  exact contDiffOn_const.mul (contDiffOn_value_curve hγ)

/-- The genuine manifold path integral agrees before and after rotation. -/
theorem pathELength_rotate (q : Circle) (γ : ℝ → Point hbar coupling) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (fun t => rotate q (γ t)) a b =
      Manifold.pathELength 𝓘(ℝ, ℂ) γ a b := by
  rw [pathELength_eq_integral, pathELength_eq_integral]
  apply lintegral_congr
  intro t
  change ENNReal.ofReal (ConeSpeed.speed hbar coupling ((q : ℂ) * (γ t).value)
    (deriv (fun u => (q : ℂ) * (γ u).value) t)) = _
  rw [deriv_rotate, speed_rotate]

/-- Rotating every competitor in the actual C1 path infimum gives one
distance inequality. -/
theorem intrinsicEDist_rotate_le (q : Circle) (p r : Point hbar coupling) :
    intrinsicEDist hbar coupling (rotate q p) (rotate q r) ≤
      intrinsicEDist hbar coupling p r := by
  apply le_of_forall_gt
  intro s hs
  obtain ⟨γ, hzero, hone, hsmooth, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hs
  have hle := Manifold.riemannianEDist_le_pathELength
    (contMDiffOn_rotate_curve q hsmooth) (congrArg (rotate q) hzero)
    (congrArg (rotate q) hone) zero_le_one
  rw [pathELength_rotate] at hle
  exact hle.trans_lt hlen

/-- Applying the genuine path transport in both directions proves exact
rotation invariance of the intrinsic infimum. -/
theorem intrinsicEDist_rotate (q : Circle) (p r : Point hbar coupling) :
    intrinsicEDist hbar coupling (rotate q p) (rotate q r) =
      intrinsicEDist hbar coupling p r := by
  apply le_antisymm (intrinsicEDist_rotate_le q p r)
  have h := intrinsicEDist_rotate_le q⁻¹ (rotate q p) (rotate q r)
  simpa only [rotate_inv_rotate] using h

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- Physical rotations are isometries of the actual positive-coupling
intrinsic metric. -/
theorem isometry_rotate (q : Circle) : Isometry (rotate (hbar := hbar) (coupling := coupling) q) := by
  intro p r
  rw [edist_eq_intrinsicEDist, edist_eq_intrinsicEDist, intrinsicEDist_rotate]

/-- The invertible physical rotation, bundled with its proved intrinsic isometry. -/
def rotation (q : Circle) : Point hbar coupling ≃ᵢ Point hbar coupling where
  toFun := rotate q
  invFun := rotate q⁻¹
  left_inv := rotate_inv_rotate q
  right_inv := rotate_rotate_inv q
  isometry_toFun := isometry_rotate hbar coupling q

/-- Physical rotation extends as an isometric equivalence of the genuine
uniform completion by the completion map of its proved uniform equivalence. -/
def completedRotation (q : Circle) : Completed hbar coupling ≃ᵢ Completed hbar coupling :=
  { (EquivalentMetricCompletion.completionEquiv (rotation hbar coupling q).toEquiv
      (rotation hbar coupling q).isometry.lipschitzWith
      (rotation hbar coupling q).isometry.antilipschitzWith).toEquiv with
    isometry_toFun := (rotation hbar coupling q).isometry.completion_map }

/-- The completed isometry agrees with the actual rotation on original points. -/
theorem completedRotation_coe (q : Circle) (p : Point hbar coupling) :
    completedRotation hbar coupling q (p : Completed hbar coupling) =
      (rotate q p : Completed hbar coupling) :=
  EquivalentMetricCompletion.completionEquiv_coe (rotation hbar coupling q).toEquiv
    (rotation hbar coupling q).isometry.lipschitzWith
    (rotation hbar coupling q).isometry.antilipschitzWith p

/-- The ordinary complex rotation formula survives completion by density and
continuity; it is a theorem about the genuine completed intrinsic metric. -/
theorem coordinate_completedRotation (q : Circle) (x : Completed hbar coupling) :
    coordinate hbar coupling (completedRotation hbar coupling q x) =
      (q : ℂ) * coordinate hbar coupling x := by
  have h : (fun x => coordinate hbar coupling (completedRotation hbar coupling q x)) =
      (fun x => (q : ℂ) * coordinate hbar coupling x) := by
    apply Completion.ext
      ((coordinate_lipschitz hbar coupling).continuous.comp
        (completedRotation hbar coupling q).continuous)
      (continuous_const.mul (coordinate_lipschitz hbar coupling).continuous)
    intro p
    change coordinate hbar coupling (completedRotation hbar coupling q (p : Completed hbar coupling)) =
      (q : ℂ) * coordinate hbar coupling (p : Completed hbar coupling)
    rw [completedRotation_coe, coordinate_coe, coordinate_coe, rotate_value]
  exact congrFun h x

/-- Every physical rotation fixes the unique completed cone tip. -/
theorem completedRotation_tip (q : Circle) :
    completedRotation hbar coupling q (tip hbar coupling) = tip hbar coupling := by
  apply (coordinate_eq_zero_iff hbar coupling _).mp
  rw [coordinate_completedRotation, coordinate_tip, mul_zero]

/-- Completed rotations preserve physical Born density everywhere, including
at the tip, where the phase coordinate itself is not extended. -/
theorem density_completedRotation (q : Circle) (x : Completed hbar coupling) :
    density hbar coupling (completedRotation hbar coupling q x) = density hbar coupling x := by
  rw [density_eq_norm_sq, density_eq_norm_sq, coordinate_completedRotation,
    norm_mul, Circle.norm_coe, one_mul]

/-- The unit physical rotation acts identically on the completed cone. -/
theorem completedRotation_one (x : Completed hbar coupling) :
    completedRotation hbar coupling 1 x = x := by
  apply (complexHomeomorph hbar coupling).injective
  change coordinate hbar coupling _ = coordinate hbar coupling x
  rw [coordinate_completedRotation, Circle.coe_one, one_mul]

/-- The completed intrinsic isometries retain the physical circle action. -/
theorem completedRotation_mul (q r : Circle) (x : Completed hbar coupling) :
    completedRotation hbar coupling (q * r) x =
      completedRotation hbar coupling q (completedRotation hbar coupling r x) := by
  apply (complexHomeomorph hbar coupling).injective
  change coordinate hbar coupling _ = coordinate hbar coupling _
  rw [coordinate_completedRotation, coordinate_completedRotation,
    coordinate_completedRotation, Circle.coe_mul, mul_assoc]

end FoliationQM.ConeRotations
