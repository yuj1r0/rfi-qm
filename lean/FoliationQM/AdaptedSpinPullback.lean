module
public import FoliationQM.GeometricSpinPullback
public import FoliationQM.SpinHOnePullback

/-!
# Actual pullback of an adapted Spin lift

For the frame component of v13 `prop:takabayasi`, pulling both geometric
principal spaces back preserves adaptation of their unit sections.
Smooth source charts give an adapted lift on the actual Spin fiber
product, whose transition ratios are the pulled degree-one signs.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.AdaptedSpinPullback
open GeometricPrincipalPullback CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup
open AdaptedGeometricSpinLift SpinLiftIsomorphism SpinLiftSignDifference SpinSignHOne

section Geometry
variable {B X Q T ι : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace Q] [TopologicalSpace T] {q : Q → B} {p : T → B}
  {C : GeometricPrincipalAtlas.Data (G := Spin) q ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  {F : GeometricSpinLift.Map C L} (f : C(X, B))

/-- Unit-section adaptation survives continuous pullback of the two actual principal spaces. -/
theorem adapted (h : Adapted F) : Adapted (GeometricSpinPullback.map f F) where
  domain_eq i := congrArg (fun V : Set B => f ⁻¹' V) (h.domain_eq i)
  unit i x hx := by
    have hs : x ∈ ((atlas f C).triv i).baseSet := by
      change f x ∈ (C.triv i).baseSet
      rw [h.domain_eq i]
      exact hx
    apply Subtype.ext
    apply Prod.ext
    · exact ((atlas f C).proj_localSection i x hs).trans
        ((atlas f L).proj_localSection i x hx).symm
    · change F (toOriginal f q ((atlas f C).localSection i x)) =
        toOriginal f p ((atlas f L).localSection i x)
      rw [toOriginal_localSection f C i x hs, toOriginal_localSection f L i x hx]
      exact h.unit i (f x) hx

end Geometry

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)

/-- Construct an adapted smooth Spin lift on the actual fiber product over the new base. -/
def lift (S : GeometricSpinStructure.Lift IB L n) : GeometricSpinStructure.Lift IX (atlas f L) n := by
  let := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas
  exact
    { Carrier := Total f S.proj
      manifold := SmoothPrincipalPullback.isManifold_total f hf S.smoothAtlas
      proj := projection f S.proj
      atlas := atlas f S.atlas
      smoothAtlas := SmoothPrincipalPullback.smoothAtlas f hf S.smoothAtlas
      map := GeometricSpinPullback.map f S.map
      adapted := adapted f S.adapted }

/-- The source carrier is the actual pullback of the original Spin projection. -/
theorem lift_carrier (S : GeometricSpinStructure.Lift IB L n) :
    (lift f hf S).Carrier = Total f S.proj := rfl

/-- The adapted source charts are the constructed pullbacks of the supplied Spin charts. -/
theorem lift_atlas (S : GeometricSpinStructure.Lift IB L n) :
    (lift f hf S).atlas = atlas f S.atlas := rfl

/-- The physical map retains the new base point and the actual original Lorentz image. -/
theorem lift_map_val (S : GeometricSpinStructure.Lift IB L n) (z : Total f S.proj) :
    ((lift f hf S).map z).val = (z.val.1, S.map z.val.2) := rfl

/-- Source transitions on each true pulled overlap are the original Spin transitions at the image. -/
theorem atlas_transition (S : GeometricSpinStructure.Lift IB L n) (i j : ι) (x : X)
    (hi : x ∈ ((atlas f L).triv i).baseSet) (hj : x ∈ ((atlas f L).triv j).baseSet) :
    (lift f hf S).atlas.transition i j x = S.atlas.transition i j (f x) := by
  apply GeometricPrincipalPullback.transition_eq
  · change f x ∈ (S.atlas.triv i).baseSet
    rwa [S.adapted.domain_eq i]
  · change f x ∈ (S.atlas.triv j).baseSet
    rwa [S.adapted.domain_eq j]

variable (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- Extracting the adapted pulled transition computes the actual original transition at the image point. -/
theorem transition_eq (S : GeometricSpinStructure.Lift IB L n) (i j : ι) (x : X)
    (hi : x ∈ ((atlas f L).triv i).baseSet) (hj : x ∈ ((atlas f L).triv j).baseSet) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    (transitions (SmoothPrincipalPullback.smoothAtlas f hf LM) (lift f hf S)).transition i j x =
      (transitions LM S).transition i j (f x) :=
  atlas_transition f hf S i j x hi hj

/-- The genuine transition-ratio cocycle of two adapted pulled lifts agrees on each
actual overlap with the pullback of their original ratio. -/
theorem difference_overlap (S T : GeometricSpinStructure.Lift IB L n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    SpinSignOneCocycle.OverlapEq
      (difference (transitions (SmoothPrincipalPullback.smoothAtlas f hf LM) (lift f hf S))
        (transitions (SmoothPrincipalPullback.smoothAtlas f hf LM) (lift f hf T)))
      (SpinHOnePullback.cocycle f hf (difference (transitions LM S) (transitions LM T))) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  intro i j x hi hj
  apply Subtype.ext
  change ((difference (transitions _ (lift f hf S)) (transitions _ (lift f hf T))).val.value i j x).val =
    ((difference (transitions LM S) (transitions LM T)).val.value i j (f x)).val
  rw [difference_val _ _ i j x hi hj, difference_val _ _ i j (f x) hi hj,
    transition_eq f hf LM S i j x hi hj, transition_eq f hf LM T i j x hi hj]

/-- The fixed-cover relative class of actual adapted pullbacks is the smooth H¹ pullback
of their original physical transition difference. -/
theorem difference_class (S T : GeometricSpinStructure.Lift IB L n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    classOf (difference (transitions (SmoothPrincipalPullback.smoothAtlas f hf LM) (lift f hf S))
        (transitions (SmoothPrincipalPullback.smoothAtlas f hf LM) (lift f hf T))) =
      SpinHOnePullback.hom f hf (RefinedGeometricPrincipalAtlas.domains L)
        (classOf (difference (transitions LM S) (transitions LM T))) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  exact classOf_eq_of_overlap (difference_overlap f hf LM S T)

end FoliationQM.AdaptedSpinPullback
