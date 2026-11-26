module
public import FoliationQM.GeometricPrincipalPullback

/-!
# Identity and composition for geometric fiber products

For the pullback of the v13 frame bundle in `prop:takabayasi`, the
identity base map gives back the original total space. For successive
base maps the intermediate base point is determined by the new one.
These identifications use the actual points of the fiber products and
commute with the lifted right operation.
-/

@[expose] public section
namespace FoliationQM.GeometricPullbackComparisons
open GeometricPrincipalPullback

variable {B X Y T G : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

/-- Discard the redundant base point in the identity pullback. -/
def identityEquiv (proj : T → B) : Total (ContinuousMap.id B) proj ≃ T where
  toFun := toOriginal (.id B) proj
  invFun p := ⟨(proj p, p), rfl⟩
  left_inv p := Subtype.ext (Prod.ext p.property.symm rfl)
  right_inv _ := rfl

/-- The inverse of the identity comparison inserts the actual original base point. -/
theorem identityEquiv_symm_val (proj : T → B) (p : T) :
    ((identityEquiv proj).symm p).val = (proj p, p) := rfl

/-- The identity comparison maps over the original base. -/
theorem identityEquiv_proj (proj : T → B) (p : Total (.id B) proj) :
    proj (identityEquiv proj p) = projection (.id B) proj p := p.property.symm

/-- The identity comparison preserves right translation in the original fiber. -/
theorem identityEquiv_right {proj : T → B} (act : T → G → T)
    (h : ∀ p g, proj (act p g) = proj p) (p : Total (.id B) proj) (a : G) :
    identityEquiv proj (right (.id B) act h p a) = act (identityEquiv proj p) a := rfl

/-- For a continuous projection the identity comparison is a homeomorphism. -/
def identityHomeomorph [TopologicalSpace T] (proj : T → B) (h : Continuous proj) :
    Total (.id B) proj ≃ₜ T where
  toEquiv := identityEquiv proj
  continuous_toFun := continuous_toOriginal (.id B)
  continuous_invFun := (h.prodMk continuous_id).subtype_mk _

variable (f : C(X, B)) (g : C(Y, X))

/-- Flatten a nested pullback by retaining its new base point and original total point. -/
def composeEquiv (proj : T → B) : Total g (projection f proj) ≃ Total (f.comp g) proj where
  toFun p := ⟨(p.val.1, p.val.2.val.2), (congrArg f p.property).trans p.val.2.property⟩
  invFun p := ⟨(p.val.1, ⟨(g p.val.1, p.val.2), p.property⟩), rfl⟩
  left_inv p := Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext p.property rfl)))
  right_inv _ := rfl

/-- Flattening keeps both the new base point and the point of the original total space. -/
theorem composeEquiv_val (proj : T → B) (p : Total g (projection f proj)) :
    (composeEquiv f g proj p).val = (p.val.1, p.val.2.val.2) := rfl

/-- The inverse of flattening reinstates the intermediate base point at its required value. -/
theorem composeEquiv_symm_val (proj : T → B) (p : Total (f.comp g) proj) :
    ((composeEquiv f g proj).symm p).val = (p.val.1, ⟨(g p.val.1, p.val.2), p.property⟩) := rfl

/-- The two lifted right operations correspond under the flattening of actual points. -/
theorem composeEquiv_right {proj : T → B} (act : T → G → T)
    (h : ∀ p a, proj (act p a) = proj p) (p : Total g (projection f proj)) (a : G) :
    composeEquiv f g proj (right g (right f act h) (fun _ _ => rfl) p a) =
      right (f.comp g) act h (composeEquiv f g proj p) a := rfl

/-- Successive and composite pullbacks are homeomorphic for their actual subspace topologies. -/
def composeHomeomorph [TopologicalSpace T] (proj : T → B) :
    Total g (projection f proj) ≃ₜ Total (f.comp g) proj where
  toEquiv := composeEquiv f g proj
  continuous_toFun := ((continuous_projection g).prodMk
    ((continuous_toOriginal f).comp (continuous_toOriginal g))).subtype_mk _
  continuous_invFun := by
    have hb : Continuous (projection (f.comp g) proj) := continuous_projection _
    have ht : Continuous (toOriginal (f.comp g) proj) := continuous_toOriginal _
    have hi : Continuous (fun p : Total (f.comp g) proj =>
        (⟨(g p.val.1, p.val.2), p.property⟩ : Total f proj)) :=
      ((g.continuous.comp hb).prodMk ht).subtype_mk _
    exact (hb.prodMk hi).subtype_mk _

end FoliationQM.GeometricPullbackComparisons
