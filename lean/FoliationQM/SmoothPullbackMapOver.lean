module
public import FoliationQM.SmoothPullbackMapping

/-!
# Pullback of a map of principal spaces over one base

For the geometric frame component of v13 `prop:takabayasi`, a map over
the base acts on the original total-space coordinate of the pullback.
This construction preserves identities, compositions and equivariance.
Original smoothness gives smoothness between the actual fiber products.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SmoothPullbackMapOver
open GeometricPrincipalPullback

variable {X B T U V G H : Type*} [TopologicalSpace X] [TopologicalSpace B]
  (f : C(X, B)) {p : T → B} {q : U → B} {r : V → B}

/-- Apply a base-preserving map to the original total-space coordinate. -/
def map (m : T → U) (hm : ∀ t, q (m t) = p t) (z : Total f p) : Total f q :=
  ⟨(z.val.1, m z.val.2), z.property.trans (hm z.val.2).symm⟩

/-- Pullback retains the new base coordinate. -/
theorem projection_map (m : T → U) (hm : ∀ t, q (m t) = p t) (z : Total f p) :
    projection f q (map f m hm z) = projection f p z := rfl

/-- The underlying original point is the image of the original coordinate. -/
theorem original_map (m : T → U) (hm : ∀ t, q (m t) = p t) (z : Total f p) :
    toOriginal f q (map f m hm z) = m (toOriginal f p z) := rfl

/-- Pulling back the identity map fixes the point of the fiber product. -/
theorem map_id (z : Total f p) : map f id (fun _ => rfl) z = z := rfl

/-- Pullback respects the actual composition of maps over the base. -/
theorem map_comp (m : T → U) (k : U → V) (hm : ∀ t, q (m t) = p t) (hk : ∀ u, r (k u) = q u)
    (z : Total f p) : map f k hk (map f m hm z) = map f (k ∘ m) (fun t => (hk (m t)).trans (hm t)) z := rfl

/-- Equivariance with a specified map of structure groups passes to the fiber products. -/
theorem map_right (m : T → U) (hm : ∀ t, q (m t) = p t) (a : T → G → T) (b : U → H → U)
    (ha : ∀ t s, p (a t s) = p t) (hb : ∀ u s, q (b u s) = q u)
    (φ : G → H) (he : ∀ t s, m (a t s) = b (m t) (φ s)) (z : Total f p) (s : G) :
    map f m hm (right f a ha z s) = right f b hb (map f m hm z) (φ s) :=
  Subtype.ext (Prod.ext rfl (he z.val.2 s))

variable {ι κ EX EB EG EH ET EU HX HB HG HH HT HU : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup EH] [NormedSpace ℝ EH] [TopologicalSpace HH]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EU] [NormedSpace ℝ EU] [TopologicalSpace HU]
  [ChartedSpace HX X] [ChartedSpace HB B] [TopologicalSpace T] [ChartedSpace HT T]
  [TopologicalSpace U] [ChartedSpace HU U] [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace H] [ChartedSpace HH H] [Group H]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {J : ModelWithCorners ℝ EG HG} {J' : ModelWithCorners ℝ EH HH}
  {K : ModelWithCorners ℝ ET HT} {K' : ModelWithCorners ℝ EU HU} {n : WithTop ℕ∞}
  {A : GeometricPrincipalAtlas.Data (G := G) p ι} {D : GeometricPrincipalAtlas.Data (G := H) q κ}
  [ChartedSpace (ModelProd HX HG) (Total f p)] [ChartedSpace (ModelProd HX HH) (Total f q)]
  (hf : ContMDiff IX IB n f) (S : GeometricPrincipalSmoothAtlas.Data IB J K A n)
  (R : GeometricPrincipalSmoothAtlas.Data IB J' K' D n)
  (M : GeometricPrincipalSmoothAtlas.Data IX J (IX.prod J) (atlas f A) n)
  (N : GeometricPrincipalSmoothAtlas.Data IX J' (IX.prod J') (atlas f D) n)

include hf S R M N in
/-- A smooth map over the base induces a smooth map between the product-model fiber products. -/
theorem contMDiff_map (m : T → U) (hm : ∀ t, q (m t) = p t) (hs : ContMDiff K K' n m) :
    ContMDiff (IX.prod J) (IX.prod J') n (map f m hm) :=
  (SmoothPullbackMapping.contMDiff_iff f hf R N _).mpr
    ⟨SmoothPullbackProjections.contMDiff_projection f M,
      hs.comp (SmoothPullbackProjections.contMDiff_toOriginal f hf S M)⟩

end FoliationQM.SmoothPullbackMapOver
