module
public import FoliationQM.GeometricPrincipalAtlas
public import FoliationQM.LorentzMatrixGroup

/-!
# Two global Lorentz charts related by a prescribed gauge

For the frame-bundle component of v13 `prop:takabayasi`, take the product
principal bundle and change coordinates in its second global chart by a
continuous Lorentz matrix field. The transition of these two actual
trivializations is the given field on the whole base.
-/

@[expose] public section
noncomputable section
open Set Bundle
namespace FoliationQM.GlobalLorentzGaugeAtlas
open LorentzMatrixGroup

variable {B : Type*} [TopologicalSpace B]

/-- Change the fiber coordinate by left multiplication by the chosen base-dependent matrix. -/
def gaugeHomeomorph (k : C(B, ProperFutureLorentz)) :
    B × ProperFutureLorentz ≃ₜ B × ProperFutureLorentz where
  toFun p := (p.1, k p.1 * p.2)
  invFun p := (p.1, (k p.1)⁻¹ * p.2)
  left_inv p := Prod.ext rfl (inv_mul_cancel_left (k p.1) p.2)
  right_inv p := Prod.ext rfl (mul_inv_cancel_left (k p.1) p.2)
  continuous_toFun := continuous_fst.prodMk ((k.continuous.comp continuous_fst).mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk ((k.continuous.comp continuous_fst).inv.mul continuous_snd)

/-- The global trivialization associated to one continuous gauge. -/
def gaugeChart (k : C(B, ProperFutureLorentz)) :
    Trivialization ProperFutureLorentz (Prod.fst : B × ProperFutureLorentz → B) where
  toOpenPartialHomeomorph := (gaugeHomeomorph k).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl

/-- The first gauge is the unit and the second is the prescribed field. -/
def gauge (k : C(B, ProperFutureLorentz)) : Bool → C(B, ProperFutureLorentz)
  | false => .const B 1
  | true => k

/-- Both global charts describe the same product projection and the usual right multiplication. -/
def atlas (k : C(B, ProperFutureLorentz)) :
    GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (Prod.fst : B × ProperFutureLorentz → B) Bool where
  triv i := gaugeChart (gauge k i)
  covers x := ⟨false, mem_univ x⟩
  right p g := (p.1, p.2 * g)
  proj_right _ _ := rfl
  right_local i p g _ := (mul_assoc (gauge k i p.1) p.2 g).symm

variable (k : C(B, ProperFutureLorentz))

/-- Every chart is defined on the entire original base. -/
theorem baseSet (i : Bool) : ((atlas k).triv i).baseSet = univ := rfl

/-- The first chart is the ordinary product coordinate. -/
theorem triv_false (p : B × ProperFutureLorentz) : (atlas k).triv false p = p := by
  exact Prod.ext rfl (one_mul p.2)

/-- The second chart multiplies the fiber coordinate on the left by the gauge. -/
theorem triv_true (p : B × ProperFutureLorentz) : (atlas k).triv true p = (p.1, k p.1 * p.2) := rfl

/-- The inverse of the first chart is the ordinary product coordinate. -/
theorem symm_false (p : B × ProperFutureLorentz) :
    ((atlas k).triv false).toOpenPartialHomeomorph.symm p = p := by
  refine Prod.ext ?_ ?_
  · rfl
  · change (1 : ProperFutureLorentz)⁻¹ * p.2 = p.2
    rw [inv_one, one_mul]

/-- The inverse of the second chart multiplies on the left by the inverse gauge. -/
theorem symm_true (p : B × ProperFutureLorentz) :
    ((atlas k).triv true).toOpenPartialHomeomorph.symm p = (p.1, (k p.1)⁻¹ * p.2) := rfl

/-- The actual first-to-second chart transition is the prescribed gauge itself. -/
theorem transition_false_true (x : B) : (atlas k).transition false true x = k x := by
  change k x * ((1 : ProperFutureLorentz)⁻¹ * 1) = k x
  simp

/-- In the reverse order the transition is its pointwise inverse. -/
theorem transition_true_false (x : B) : (atlas k).transition true false x = (k x)⁻¹ := by
  change 1 * ((k x)⁻¹ * 1) = (k x)⁻¹
  simp

/-- The single global product chart gives another atlas of the same projection and right action. -/
def standard (B : Type*) [TopologicalSpace B] :
    GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (Prod.fst : B × ProperFutureLorentz → B) Unit where
  triv _ := gaugeChart (.const B 1)
  covers x := ⟨(), mem_univ x⟩
  right p g := (p.1, p.2 * g)
  proj_right _ _ := rfl
  right_local _ p g _ := (mul_assoc (1 : ProperFutureLorentz) p.2 g).symm

/-- The single product chart covers the entire base. -/
theorem standard_baseSet (B : Type*) [TopologicalSpace B] (i : Unit) :
    ((standard B).triv i).baseSet = univ := rfl

/-- The product chart has only the identity transition. -/
theorem standard_transition (B : Type*) [TopologicalSpace B] (i j : Unit) (x : B) :
    (standard B).transition i j x = 1 := by
  change (1 : ProperFutureLorentz) * (1⁻¹ * 1) = 1
  simp

/-- Changing the second chart leaves the geometric right action equal to that of the standard atlas. -/
theorem right_eq_standard : (atlas k).right = (standard B).right := rfl

end FoliationQM.GlobalLorentzGaugeAtlas
