module
public import FoliationQM.GeometricPullbackComparisons
public import FoliationQM.SmoothPullbackMapping
public import FoliationQM.SmoothPrincipalPullback

/-!
# Smooth identity and successive pullback comparisons

For the geometric frame component of v13 `prop:takabayasi`, the identity
pullback is diffeomorphic to the original total space. The iterated
pullback is diffeomorphic over its base to the pullback of the composite.
Their maps are the coordinate identifications of the geometric fiber
products, with regularity at the common order of the original smooth
atlas and the base maps.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SmoothPullbackComparisons
open GeometricPrincipalPullback GeometricPullbackComparisons SmoothPullbackChartedSpace
open SmoothPrincipalPullback SmoothPullbackMapping SmoothPullbackProjections

variable {EB EG ET HB HG HT B G T ι : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IB : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := G) proj ι}
  [IsManifold J n G]

section Identity
variable [IsManifold IB n B] (S : GeometricPrincipalSmoothAtlas.Data IB J K A n)

/-- The identity pullback recovers the original total space by an order-`n` diffeomorphism. -/
def identity :
    letI := chartedSpace HB HG (.id B) A
    Diffeomorph (IB.prod J) K (Total (.id B) proj) T n := by
  let := chartedSpace HB HG (.id B) A
  have hid : ContMDiff IB IB n (ContinuousMap.id B) := contMDiff_id
  let M := smoothAtlas (.id B) hid S
  exact
    { toEquiv := identityEquiv proj
      contMDiff_toFun := contMDiff_toOriginal (.id B) hid S M
      contMDiff_invFun := (contMDiff_iff (.id B) hid S M _).mpr
        ⟨S.contMDiff_proj, contMDiff_id⟩ }

/-- The smooth identity comparison uses precisely the pointwise geometric equivalence. -/
theorem identity_toEquiv :
    letI := chartedSpace HB HG (.id B) A
    (identity S).toEquiv = identityEquiv proj := rfl

/-- The smooth identity comparison sends a pulled right translate to its original right translate. -/
theorem identity_right (p : Total (.id B) proj) (a : G) :
    identity S ((atlas (.id B) A).right p a) = A.right (identity S p) a := rfl

end Identity

variable {EX EY HX HY X Y : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace Y] [ChartedSpace HY Y]
  {IX : ModelWithCorners ℝ EX HX} {IY : ModelWithCorners ℝ EY HY}
  [IsManifold IX n X] [IsManifold IY n Y]
  (f : C(X, B)) (g : C(Y, X)) (hf : ContMDiff IX IB n f) (hg : ContMDiff IY IX n g)
  (S : GeometricPrincipalSmoothAtlas.Data IB J K A n)

/-- The nested and composite fiber products are diffeomorphic with the constructed charts on both. -/
def compose :
    letI := chartedSpace HX HG f A
    letI := chartedSpace HY HG g (atlas f A)
    letI := chartedSpace HY HG (f.comp g) A
    Diffeomorph (IY.prod J) (IY.prod J) (Total g (projection f proj)) (Total (f.comp g) proj) n := by
  let := chartedSpace HX HG f A
  let := chartedSpace HY HG g (atlas f A)
  let := chartedSpace HY HG (f.comp g) A
  have hfg : ContMDiff IY IB n (f.comp g) := hf.comp hg
  let M := smoothAtlas f hf S
  let N := smoothAtlas g hg M
  let D := smoothAtlas (f.comp g) hfg S
  have hfirst := contMDiff_toOriginal f hf S M
  have hsecond := contMDiff_toOriginal g hg M N
  have hflat := contMDiff_toOriginal (f.comp g) hfg S D
  refine { toEquiv := composeEquiv f g proj, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (contMDiff_iff (f.comp g) hfg S D _).mpr
    exact ⟨N.contMDiff_proj, hfirst.comp hsecond⟩
  · apply (contMDiff_iff g hg M N _).mpr
    refine ⟨D.contMDiff_proj, ?_⟩
    apply (contMDiff_iff f hf S M _).mpr
    exact ⟨hg.comp D.contMDiff_proj, hflat⟩

/-- The smooth composition comparison retains the actual geometric flattening in both directions. -/
theorem compose_toEquiv :
    letI := chartedSpace HX HG f A
    letI := chartedSpace HY HG g (atlas f A)
    letI := chartedSpace HY HG (f.comp g) A
    (compose f g hf hg S).toEquiv = composeEquiv f g proj := rfl

/-- Flattening the nested right action agrees with translation in the composite pullback. -/
theorem compose_right (p : Total g (projection f proj)) (a : G) :
    compose f g hf hg S ((atlas g (atlas f A)).right p a) =
      (atlas (f.comp g) A).right (compose f g hf hg S p) a := rfl

end FoliationQM.SmoothPullbackComparisons
