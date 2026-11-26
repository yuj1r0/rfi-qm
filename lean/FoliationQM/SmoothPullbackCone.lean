module
public import FoliationQM.SmoothPullbackMapping
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# The smooth mapping property on bundled maps

For the frame component of v13 `prop:takabayasi`, smooth maps from a test
manifold to the principal fiber product correspond to pairs of smooth maps
whose images in the base agree. The correspondence is natural under
precomposition of the test maps.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SmoothPullbackCone
open GeometricPrincipalPullback SmoothPullbackMapping

variable {X B T G Z W ι EX EB ET EG EL EZ EW HX HB HT HG HL HZ HW : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  [NormedAddCommGroup EW] [NormedSpace ℝ EW] [TopologicalSpace HW]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace Z] [ChartedSpace HZ Z] [TopologicalSpace W] [ChartedSpace HW W]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {J : ModelWithCorners ℝ EG HG} {L : ModelWithCorners ℝ EL HL} {IZ : ModelWithCorners ℝ EZ HZ}
  {IW : ModelWithCorners ℝ EW HW} {n : WithTop ℕ∞} {proj : T → B}
  {A : GeometricPrincipalAtlas.Data (G := G) proj ι} (f : C(X, B))
  (hf : ContMDiff IX IB n f) (S : GeometricPrincipalSmoothAtlas.Data IB J K A n)
  [ChartedSpace HL (Total f proj)] (M : GeometricPrincipalSmoothAtlas.Data IX J L (atlas f A) n)

/-- Compatible smooth maps to the new base and the original total space. -/
abbrev Cone (f : C(X, B)) (proj : T → B) (IZ : ModelWithCorners ℝ EZ HZ)
    (IX : ModelWithCorners ℝ EX HX) (K : ModelWithCorners ℝ ET HT) (Z : Type*)
    [TopologicalSpace Z] [ChartedSpace HZ Z] (n : WithTop ℕ∞) :=
  {p : C^n⟮IZ, Z; IX, X⟯ × C^n⟮IZ, Z; K, T⟯ // ∀ z, f (p.1 z) = proj (p.2 z)}

/-- Smooth maps into the geometric fiber product are represented by their two compatible components. -/
def equiv : C^n⟮IZ, Z; L, Total f proj⟯ ≃ Cone f proj IZ IX K Z n where
  toFun F := ⟨(⟨_, (SmoothPullbackProjections.contMDiff_projection f M).comp F.contMDiff⟩,
    ⟨_, (SmoothPullbackProjections.contMDiff_toOriginal f hf S M).comp F.contMDiff⟩), fun z => (F z).property⟩
  invFun p := ⟨lift f p.val.1 p.val.2 p.property,
    contMDiff_lift f S M _ _ p.property p.val.1.contMDiff p.val.2.contMDiff⟩
  left_inv _ := ContMDiffMap.ext (fun _ => rfl)
  right_inv _ := Subtype.ext (Prod.ext (ContMDiffMap.ext (fun _ => rfl)) (ContMDiffMap.ext (fun _ => rfl)))

/-- The inverse correspondence realizes the pair with its exact original coordinates. -/
theorem symm_apply (p : Cone f proj IZ IX K Z n) (z : Z) :
    ((equiv f hf S M).symm p z).val = (p.val.1 z, p.val.2 z) := rfl

/-- Precompose both legs of a smooth cone with the same smooth test map. -/
def precomp (p : Cone f proj IZ IX K Z n) (g : C^n⟮IW, W; IZ, Z⟯) : Cone f proj IW IX K W n :=
  ⟨(p.val.1.comp g, p.val.2.comp g), fun w => p.property (g w)⟩

/-- The mapping equivalence commutes with precomposition on the test space. -/
theorem equiv_precomp (F : C^n⟮IZ, Z; L, Total f proj⟯) (g : C^n⟮IW, W; IZ, Z⟯) :
    equiv f hf S M (F.comp g) = precomp f (equiv f hf S M F) g := rfl

end FoliationQM.SmoothPullbackCone
