module
public import FoliationQM.LorentzManifold
public import FoliationQM.LorentzCayleySmooth
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The independent proper future Lorentz Lie group

Source scope: the real Lorentz frame factor in v13 `prop:takabayasi`.
The independently constructed matrix Cayley atlas retains the original
proper future subgroup topology and operations. Its ambient-matrix
regularity criterion proves genuine smooth multiplication and inversion.
Inversion uses the actual metric-signed transpose, with no inverse-domain
assumption added to the group. Translations are actual diffeomorphisms.
No Spin covering or quotient atlas is used to define this Lie structure.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.LorentzGroupManifold
open LorentzMatrixGroup LorentzManifold

/-- Actual ordered Lorentz multiplication is jointly smooth for the independent matrix Cayley atlas. -/
theorem contMDiff_mul (n : WithTop ℕ∞) :
    ContMDiff (model.prod model) model n
      (fun p : ProperFutureLorentz × ProperFutureLorentz => p.1 * p.2) := by
  apply LorentzManifold.contMDiff_iff_value.mpr
  have hm : ContDiff ℝ n (fun p : Mat4 × Mat4 => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact hm.contMDiff.comp
    (((LorentzManifold.contMDiff_value n).comp contMDiff_fst).prodMk_space
      ((LorentzManifold.contMDiff_value n).comp contMDiff_snd))

/-- The actual group inverse is smooth because its independent ambient matrix is the metric-signed transpose. -/
theorem contMDiff_inv (n : WithTop ℕ∞) :
    ContMDiff model model n (fun L : ProperFutureLorentz => L⁻¹) := by
  apply LorentzManifold.contMDiff_iff_value.mpr
  have h := LorentzCayleySmooth.signedTransposeCLM.contMDiff.comp
    (LorentzManifold.contMDiff_value n)
  have he : (fun L : ProperFutureLorentz => value L⁻¹) =
      LorentzCayleySmooth.signedTransposeCLM ∘ value := by
    funext L
    exact (LorentzCayleySmooth.signedTransposeCLM_matrix L.val).symm
  rw [he]
  exact h

/-- The original proper future Lorentz matrix group is a genuine real Lie group for the independent Cayley atlas, to every order. -/
instance instLieGroupProperFutureLorentz (n : WithTop ℕ∞) :
    LieGroup model n ProperFutureLorentz where
  contMDiff_mul := contMDiff_mul n
  contMDiff_inv := contMDiff_inv n

/-- Left multiplication by a fixed actual Lorentz element is smooth. -/
theorem contMDiff_leftMul (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    ContMDiff model model n (fun K : ProperFutureLorentz => L * K) :=
  (contMDiff_mul n).comp (contMDiff_const.prodMk contMDiff_id)

/-- Right multiplication by a fixed actual Lorentz element is smooth. -/
theorem contMDiff_rightMul (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    ContMDiff model model n (fun K : ProperFutureLorentz => K * L) :=
  (contMDiff_mul n).comp (contMDiff_id.prodMk contMDiff_const)

/-- Actual left translation is a diffeomorphism with inverse left multiplication by the genuine group inverse. -/
def leftMulDiffeomorph (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    Diffeomorph model model ProperFutureLorentz ProperFutureLorentz n where
  toFun := fun K => L * K
  invFun := fun K => L⁻¹ * K
  left_inv := fun K => by simp [← mul_assoc]
  right_inv := fun K => by simp [← mul_assoc]
  contMDiff_toFun := contMDiff_leftMul n L
  contMDiff_invFun := contMDiff_leftMul n L⁻¹

/-- Actual right translation is a diffeomorphism with inverse right multiplication by the genuine group inverse. -/
def rightMulDiffeomorph (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    Diffeomorph model model ProperFutureLorentz ProperFutureLorentz n where
  toFun := fun K => K * L
  invFun := fun K => K * L⁻¹
  left_inv := fun K => by simp [mul_assoc]
  right_inv := fun K => by simp [mul_assoc]
  contMDiff_toFun := contMDiff_rightMul n L
  contMDiff_invFun := contMDiff_rightMul n L⁻¹

/-- Actual Lorentz group inversion is an involutive diffeomorphism for the independent atlas. -/
def inverseDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model model ProperFutureLorentz ProperFutureLorentz n where
  toFun := fun L => L⁻¹
  invFun := fun L => L⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  contMDiff_toFun := contMDiff_inv n
  contMDiff_invFun := contMDiff_inv n

/-- The left-translation diffeomorphism is exactly actual group multiplication. -/
@[simp]
theorem leftMulDiffeomorph_apply (n : WithTop ℕ∞) (L K : ProperFutureLorentz) :
    leftMulDiffeomorph n L K = L * K := rfl

/-- Its inverse is exactly left multiplication by the actual inverse Lorentz element. -/
@[simp]
theorem leftMulDiffeomorph_symm_apply (n : WithTop ℕ∞) (L K : ProperFutureLorentz) :
    (leftMulDiffeomorph n L).symm K = L⁻¹ * K := rfl

/-- The right-translation diffeomorphism is exactly actual right multiplication. -/
@[simp]
theorem rightMulDiffeomorph_apply (n : WithTop ℕ∞) (L K : ProperFutureLorentz) :
    rightMulDiffeomorph n L K = K * L := rfl

/-- Its inverse is exactly right multiplication by the actual inverse Lorentz element. -/
@[simp]
theorem rightMulDiffeomorph_symm_apply (n : WithTop ℕ∞) (L K : ProperFutureLorentz) :
    (rightMulDiffeomorph n L).symm K = K * L⁻¹ := rfl

/-- The inversion diffeomorphism is exactly the original group inverse. -/
@[simp]
theorem inverseDiffeomorph_apply (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    inverseDiffeomorph n L = L⁻¹ := rfl

end FoliationQM.LorentzGroupManifold
