module
public import FoliationQM.LorentzMatrixGroup
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Geometric oriented future Lorentz frames

A frame is an actual ordered basis of a supplied real vector space, with
Minkowski Gram matrix for a supplied bilinear form, a specified genuine
orientation, and a specified future cone. These geometric data are independent
of the matrix Lorentz group and of Spin. Existence of such a frame is not
assumed for an arbitrary vector space or tangent bundle.

Change of frame is derived from basis coordinates. Its determinant one and
future preservation follow from the geometric frame conditions. The resulting
right Lorentz action is free and transitive whenever a frame is supplied.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator
namespace FoliationQM.GeometricLorentzFrame
open LorentzMatrixGroup RealLorentzFrame Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An actual oriented future Lorentz basis for the specified geometric bilinear form and cone. -/
structure Frame (g : LinearMap.BilinForm ℝ V)
    (orientation : Orientation ℝ V (Fin 4)) (future : Set V) where
  /-- The four actual vectors form a basis of the geometric vector space. -/
  basis : Module.Basis (Fin 4) ℝ V
  /-- Their Gram matrix is the source metric with signature (+---). -/
  metric : g.toMatrix basis = eta
  /-- The basis has the specified orientation in the exterior-form sense. -/
  oriented : basis.orientation = orientation
  /-- The basis identifies the specified geometric future cone with the model timelike future cone. -/
  future_iff : ∀ v : Covector, basis.equivFun.symm v ∈ future ↔ futureCone v

variable {g : LinearMap.BilinForm ℝ V} {orientation : Orientation ℝ V (Fin 4)}
  {future : Set V}

/-- Geometric frames are equal when their actual ordered bases are equal. -/
@[ext] theorem frame_ext {e f : Frame g orientation future} (h : e.basis = f.basis) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- A geometric frame evaluates the supplied bilinear form as the actual Minkowski form. -/
theorem metric_coordinates (e : Frame g orientation future) (v w : Covector) :
    g (e.basis.equivFun.symm v) (e.basis.equivFun.symm w) = minkowski v w := by
  rw [← g.dotProduct_toMatrix_mulVec e.basis, e.metric, minkowski_eq_dot_eta]

/-- The individual geometric basis vectors have precisely the prescribed Gram entries. -/
theorem metric_basis (e : Frame g orientation future) (a b : Fin 4) :
    g (e.basis a) (e.basis b) = eta a b := by
  simpa only [LinearMap.BilinForm.toMatrix_apply] using congrFun (congrFun e.metric a) b

/-- The metric pairing with a geometric basis vector gives its signed dual coordinate. -/
theorem metric_basis_left (e : Frame g orientation future) (v : V) (a : Fin 4) :
    g (e.basis a) v = sign a * e.basis.repr v a := by
  rw [g.apply_eq_dotProduct_toMatrix_mulVec e.basis, e.metric]
  simp [eta, dotProduct, Matrix.mulVec, Module.Basis.repr_self,
    Finsupp.single_apply, Matrix.diagonal_apply]

/-- Every basis coordinate is the metric pairing with the signed dual tetrad vector. -/
theorem repr_eq_signed_metric (e : Frame g orientation future) (v : V) (a : Fin 4) :
    e.basis.repr v a = sign a * g (e.basis a) v := by
  rw [metric_basis_left, ← mul_assoc, sign_sq, one_mul]

/-- The actual change-of-basis matrix satisfies the independent Lorentz metric equation. -/
theorem change_metric (e f : Frame g orientation future) :
    (f.basis.toMatrix e.basis).transpose * eta * f.basis.toMatrix e.basis = eta := by
  simpa only [e.metric, f.metric] using g.toMatrix_mul_basis_toMatrix f.basis e.basis

/-- Equality of actual orientations forces the geometric change-of-basis determinant to be positive. -/
theorem change_det_pos (e f : Frame g orientation future) :
    0 < (f.basis.toMatrix e.basis).det := by
  rw [← Module.Basis.det_apply]
  exact (Module.Basis.orientation_eq_iff_det_pos f.basis e.basis).mp
    (f.oriented.trans e.oriented.symm)

/-- The metric and orientation conditions together force determinant one, without a matrix-image assumption. -/
theorem change_det (e f : Frame g orientation future) :
    (f.basis.toMatrix e.basis).det = 1 := by
  have hs := det_sq_of_metric _ (change_metric e f)
  have hp := change_det_pos e f
  nlinarith

/-- The coordinate change sends the coordinates of a vector in the first frame to those in the second. -/
theorem change_coordinates (e f : Frame g orientation future) (v : Covector) :
    f.basis.toMatrix e.basis *ᵥ v = f.basis.equivFun (e.basis.equivFun.symm v) := by
  simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
    (e.basis.toMatrix_mulVec_repr f.basis (e.basis.equivFun.symm v))

/-- The specified geometric future cone forces actual model future-cone preservation by the coordinate change. -/
theorem change_preservesFutureCone (e f : Frame g orientation future) :
    preservesFutureCone (f.basis.toMatrix e.basis) := by
  intro v
  rw [change_coordinates]
  have hf := f.future_iff (f.basis.equivFun (e.basis.equivFun.symm v))
  rw [LinearEquiv.symm_apply_apply] at hf
  exact hf.symm.trans (e.future_iff v)

/-- The genuine proper future Lorentz element changing coordinates from geometric frame e to frame f. -/
def change (e f : Frame g orientation future) : ProperFutureLorentz :=
  ⟨⟨⟨f.basis.toMatrix e.basis, e.basis.toMatrix f.basis,
      f.basis.toMatrix_mul_toMatrix_flip e.basis,
      e.basis.toMatrix_mul_toMatrix_flip f.basis⟩, change_metric e f⟩,
    change_det e f, change_preservesFutureCone e f⟩

/-- Geometric coordinate changes have exactly the independently computed basis matrix. -/
theorem change_matrix (e f : Frame g orientation future) :
    matrix (change e f).val = f.basis.toMatrix e.basis := rfl

/-- Each geometric transition entry is a signed metric pairing of the two actual tetrads. -/
theorem change_matrix_entry (e f : Frame g orientation future) (a b : Fin 4) :
    matrix (change e f).val a b = sign a * g (f.basis a) (e.basis b) :=
  repr_eq_signed_metric f (e.basis b) a

/-- The geometric self-transition is the identity Lorentz element. -/
theorem change_self (e : Frame g orientation future) : change e e = 1 := by
  apply Subtype.ext
  apply matrix_injective
  exact e.basis.toMatrix_self

/-- Geometric coordinate changes compose in the actual chart i to j to k convention. -/
theorem change_comp (e f h : Frame g orientation future) :
    change f h * change e f = change e h := by
  apply Subtype.ext
  apply matrix_injective
  exact h.basis.toMatrix_mul_toMatrix f.basis e.basis

/-- Reversing a geometric change of frame takes its actual group inverse. -/
theorem change_reverse (e f : Frame g orientation future) : change f e = (change e f)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [change_comp, change_self]

/-- A proper future Lorentz element acts as an actual linear equivalence of model vectors. -/
def modelEquiv (L : ProperFutureLorentz) : Covector ≃ₗ[ℝ] Covector :=
  { Matrix.toLin' (matrix L.val) with
    invFun := fun v => matrix (L⁻¹).val *ᵥ v
    left_inv := by
      intro v
      change matrix (L⁻¹).val *ᵥ (matrix L.val *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, ← matrix_mul]
      simp [matrix_one]
    right_inv := by
      intro v
      change matrix L.val *ᵥ (matrix (L⁻¹).val *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, ← matrix_mul]
      simp [matrix_one] }

/-- The model linear action is literally multiplication by the physical real matrix. -/
theorem modelEquiv_apply (L : ProperFutureLorentz) (v : Covector) :
    modelEquiv L v = matrix L.val *ᵥ v := rfl

/-- Precomposing a geometric frame with a Lorentz element produces this actual ordered basis. -/
def rightBasis (e : Frame g orientation future) (L : ProperFutureLorentz) :
    Module.Basis (Fin 4) ℝ V :=
  Module.Basis.ofEquivFun (e.basis.equivFun.trans (modelEquiv L).symm)

/-- Coordinates reconstructed in the transformed basis are the original geometric frame applied after the Lorentz matrix. -/
theorem rightBasis_coordinates (e : Frame g orientation future) (L : ProperFutureLorentz)
    (v : Covector) :
    (rightBasis e L).equivFun.symm v = e.basis.equivFun.symm (matrix L.val *ᵥ v) := by
  rw [rightBasis, Module.Basis.equivFun_ofEquivFun]
  rfl

/-- The transformed geometric basis has precisely the prescribed Lorentz matrix in the original frame. -/
theorem rightBasis_matrix (e : Frame g orientation future) (L : ProperFutureLorentz) :
    e.basis.toMatrix (rightBasis e L) = matrix L.val := by
  ext a b
  rw [Module.Basis.toMatrix_apply]
  simp only [rightBasis, Module.Basis.coe_ofEquivFun]
  change e.basis.equivFun (e.basis.equivFun.symm (modelEquiv L (Pi.single b 1))) a = _
  rw [LinearEquiv.apply_symm_apply, modelEquiv_apply, Matrix.mulVec_single]
  simp

/-- Actual precomposition defines the principal right Lorentz action on geometric frames. -/
def rightAction (e : Frame g orientation future) (L : ProperFutureLorentz) :
    Frame g orientation future where
  basis := rightBasis e L
  metric := by
    have h := g.toMatrix_mul_basis_toMatrix e.basis (rightBasis e L)
    rw [e.metric, rightBasis_matrix, metric] at h
    exact h.symm
  oriented := by
    apply Eq.trans _ e.oriented
    apply Eq.symm
    apply (Module.Basis.orientation_eq_iff_det_pos e.basis (rightBasis e L)).mpr
    rw [Module.Basis.det_apply, rightBasis_matrix, L.property.1]
    norm_num
  future_iff v := by
    rw [rightBasis_coordinates]
    exact (e.future_iff _).trans (L.property.2 v)

/-- The actual vectors of a right-transformed frame are the Lorentz linear combinations of the original tetrad. -/
theorem rightAction_basis (e : Frame g orientation future) (L : ProperFutureLorentz) (a : Fin 4) :
    (rightAction e L).basis a = e.basis.equivFun.symm (fun b => matrix L.val b a) := by
  change (rightBasis e L) a = _
  simp only [rightBasis, Module.Basis.coe_ofEquivFun]
  change e.basis.equivFun.symm (modelEquiv L (Pi.single a 1)) = _
  rw [modelEquiv_apply, Matrix.mulVec_single]
  exact congrArg e.basis.equivFun.symm (one_smul ℝᵐᵒᵖ ((matrix L.val).col a))

/-- A right-transformed frame has the exact prescribed Lorentz change back to the original frame. -/
theorem change_rightAction (e : Frame g orientation future) (L : ProperFutureLorentz) :
    change (rightAction e L) e = L := by
  apply Subtype.ext
  apply matrix_injective
  exact rightBasis_matrix e L

/-- The unique change matrix reconstructs the first geometric frame from the second. -/
theorem rightAction_change (e f : Frame g orientation future) :
    rightAction f (change e f) = e := by
  apply frame_ext
  apply DFunLike.ext
  intro a
  rw [rightAction_basis, change_matrix]
  change f.basis.equivFun.symm (f.basis.equivFun (e.basis a)) = e.basis a
  exact f.basis.equivFun.symm_apply_apply _

/-- The identity Lorentz element acts trivially on every actual geometric frame. -/
theorem rightAction_one (e : Frame g orientation future) : rightAction e 1 = e := by
  simpa only [change_self] using rightAction_change e e

/-- Successive geometric right actions have the actual ordered Lorentz product. -/
theorem rightAction_mul (e : Frame g orientation future) (L K : ProperFutureLorentz) :
    rightAction (rightAction e L) K = rightAction e (L * K) := by
  apply frame_ext
  apply DFunLike.ext
  intro a
  rw [rightAction_basis, rightAction_basis]
  change (rightBasis e L).equivFun.symm _ = _
  rw [rightBasis_coordinates]
  change e.basis.equivFun.symm (matrix L.val *ᵥ (fun b => matrix K.val b a)) =
    e.basis.equivFun.symm (fun b => (matrix L.val * matrix K.val) b a)
  rfl

/-- The principal right Lorentz action is free at every supplied geometric frame. -/
theorem rightAction_injective (e : Frame g orientation future) :
    Function.Injective (rightAction e) := by
  intro L K h
  have hh := congrArg (fun f => change f e) h
  simpa only [change_rightAction] using hh

/-- Every pair of geometric frames is related by exactly one actual proper future Lorentz element. -/
theorem existsUnique_rightAction (e f : Frame g orientation future) :
    ∃! L : ProperFutureLorentz, rightAction e L = f := by
  refine ⟨change f e, rightAction_change f e, ?_⟩
  intro L hL
  exact rightAction_injective e (hL.trans (rightAction_change f e).symm)

/-- A supplied geometric frame identifies the entire frame fiber with the actual Lorentz group. -/
def frameEquiv (e : Frame g orientation future) : ProperFutureLorentz ≃ Frame g orientation future where
  toFun := rightAction e
  invFun := fun f => change f e
  left_inv := change_rightAction e
  right_inv := fun f => rightAction_change f e

/-- The standard Minkowski bilinear form is defined independently by its actual metric matrix. -/
def minkowskiForm : LinearMap.BilinForm ℝ Covector := eta.toBilin'

/-- The standard bilinear form agrees with the source's explicit Minkowski formula. -/
theorem minkowskiForm_apply (v w : Covector) : minkowskiForm v w = minkowski v w := by
  rw [minkowski_eq_dot_eta]
  exact Matrix.toBilin'_apply' _ _ _

/-- The actual standard coordinate basis gives an inhabited geometric Minkowski frame. -/
def standardFrame : Frame minkowskiForm (Pi.basisFun ℝ (Fin 4)).orientation {v | futureCone v} where
  basis := Pi.basisFun ℝ (Fin 4)
  metric := by simp [minkowskiForm, LinearMap.BilinForm.toMatrix_basisFun]
  oriented := rfl
  future_iff v := by simp

end FoliationQM.GeometricLorentzFrame
