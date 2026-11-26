module
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Product covering maps from genuine evenly covered neighborhoods

Source scope: support for the geometric Spin-frame component of v13
`prop:takabayasi`. A covering remains a covering after taking its product
with an arbitrary topological space. The proof constructs the actual local
product homeomorphism over each evenly covered neighborhood, retaining its
literal discrete sheet type. Continuous base-dependent multiplication is
also packaged as an actual product homeomorphism for subsequent independent
principal-bundle coordinate calculations.
-/

@[expose] public section
noncomputable section
open Set Topology
namespace FoliationQM.ProductCovering

variable {T E X : Type*} [TopologicalSpace T] [TopologicalSpace E]
  [TopologicalSpace X]

/-- The inverse image of a set under the second product projection has its original product/subtype topology. -/
def sndPreimageHomeomorph (T : Type*) [TopologicalSpace T] (U : Set X) :
    (Prod.snd ⁻¹' U : Set (T × X)) ≃ₜ T × U where
  toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  invFun z := ⟨(z.1, z.2.val), z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Products retain the actual discrete sheets of any evenly covered neighborhood. -/
theorem isEvenlyCovered_id_prodMap {f : E → X} {x : X}
    {I : Type*} [TopologicalSpace I] (h : IsEvenlyCovered f x I) (t : T) :
    IsEvenlyCovered (Prod.map (id : T → T) f) (t, x) I := by
  rcases h with ⟨hI, U, hx, hU, hfU, H, hH⟩
  let V : Set (T × X) := Prod.snd ⁻¹' U
  let K : (Prod.map (id : T → T) f) ⁻¹' V ≃ₜ V × I :=
    (sndPreimageHomeomorph T (f ⁻¹' U)).trans
      (((Homeomorph.refl T).prodCongr H).trans
        ((Homeomorph.prodAssoc T U I).symm.trans
          ((sndPreimageHomeomorph T U).symm.prodCongr (Homeomorph.refl I))))
  refine ⟨hI, V, hx, hU.preimage continuous_snd,
    hfU.preimage continuous_snd, K, ?_⟩
  intro z
  apply Prod.ext
  · rfl
  · exact hH ⟨z.val.2, z.property⟩

/-- Taking the product with an arbitrary space preserves covering maps through explicit evenly covered neighborhoods. -/
theorem isCoveringMap_id_prodMap {f : E → X} (h : IsCoveringMap f) :
    IsCoveringMap (Prod.map (id : T → T) f) := by
  intro z
  exact (isEvenlyCovered_id_prodMap (h z.2) z.1).to_isEvenlyCovered_preimage

/-- Continuous multiplication by a base-dependent group element is an actual product homeomorphism, with inverse multiplication by its inverse. -/
def skewMul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : T → G) (ha : Continuous a) : T × G ≃ₜ T × G where
  toFun z := (z.1, a z.1 * z.2)
  invFun z := (z.1, (a z.1)⁻¹ * z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk ((ha.comp continuous_fst).mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk ((ha.comp continuous_fst).inv.mul continuous_snd)

/-- The varying left-multiplication homeomorphism has the literal fiberwise group formula. -/
theorem skewMul_apply {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : T → G) (ha : Continuous a) (z : T × G) :
    skewMul a ha z = (z.1, a z.1 * z.2) := rfl

/-- The inverse varying multiplication homeomorphism has the literal inverse-group formula. -/
theorem skewMul_symm_apply {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : T → G) (ha : Continuous a) (z : T × G) :
    (skewMul a ha).symm z = (z.1, (a z.1)⁻¹ * z.2) := rfl

end FoliationQM.ProductCovering
