module
public import FoliationQM.AdaptedSpinPullback
public import FoliationQM.AdaptedSpinCoverRestriction
public import FoliationQM.RestrictedPrincipalPullback

/-!
# Anchored pullback of a refined adapted Spin presentation

For v13 `prop:takabayasi`, pull back a supplied adapted Spin lift on
a refined Lorentz cover, then index its charts by points of the new base.
The physical map and smooth source structure come from the first pullback.
Actual unit-section equality identifies the target with the anchored
restriction of the original Lorentz pullback. Its relative signs compute
the global degree-one pullback.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.AnchoredAdaptedSpinPullback
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricPrincipalPullback
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas
open AdaptedGeometricSpinLift SpinLiftIsomorphism SpinLiftSignDifference SpinSignHOne

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {p : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (R : Refinement (domains L) B) (hm : ∀ b, b ∈ R.domain b)

/-- Reindex the pulled adapted source, then use the matching true target unit sections. -/
def lift (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    GeometricSpinStructure.Lift IX (restrictedAtlas (atlas f L) (AnchoredPullbackRefinement.refinement f R hm)) n := by
  let V := AdaptedSpinCoverRestriction.restrict (AdaptedSpinPullback.lift f hf S)
    (AnchoredPullbackRefinement.reindex f R hm)
  exact
    { Carrier := V.Carrier
      proj := V.proj
      atlas := V.atlas
      smoothAtlas := V.smoothAtlas
      map := { toFun := V.map
               continuous_toFun := V.map.continuous_toFun
               proj := V.map.proj
               equivariant := V.map.equivariant }
      adapted :=
        { domain_eq := V.adapted.domain_eq
          unit := fun i x hx => (V.adapted.unit i x hx).trans
            (RestrictedPrincipalPullback.anchored_localSection_eq f L R hm i x hx) } }

/-- The reindexed adapted source is the actual original Spin pullback. -/
theorem lift_carrier (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    (lift f hf R hm S).Carrier = Total f S.proj := rfl

/-- Its source charts use the first pullback structure before the principal atlas was restricted. -/
theorem lift_charted (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    (lift f hf R hm S).charted =
      SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas := rfl

/-- Its projection is still the new base point of the actual Spin pullback. -/
theorem lift_proj (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) (z : Total f S.proj) :
    (lift f hf R hm S).proj z = z.val.1 := rfl

/-- Its physical map keeps that base point and sends the original Spin frame to its image. -/
theorem lift_map_val (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) (z : Total f S.proj) :
    ((lift f hf R hm S).map z).val = (z.val.1, S.map z.val.2) := rfl

/-- The restricted source action is the lifted original Spin action. -/
theorem lift_right (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    (lift f hf R hm S).atlas.right = (atlas f S.atlas).right := rfl

variable (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- The reindexed extracted transition is the original Spin transition at the corresponding image indices. -/
theorem transition_eq (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) (i j x : X)
    (hi : f x ∈ R.domain (f i)) (hj : f x ∈ R.domain (f j)) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    (transitions (restrictedSmoothAtlas (SmoothPrincipalPullback.smoothAtlas f hf LM)
      (AnchoredPullbackRefinement.refinement f R hm)) (lift f hf R hm S)).transition i j x =
      (transitions (restrictedSmoothAtlas LM R) S).transition (f i) (f j) (f x) :=
  AdaptedSpinPullback.atlas_transition f hf S (f i) (f j) x hi hj

/-- The relative class of the two reindexed presentations is restriction of the pulled original class. -/
theorem difference_class (S T : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    classOf (difference
      (transitions (restrictedSmoothAtlas (SmoothPrincipalPullback.smoothAtlas f hf LM)
        (AnchoredPullbackRefinement.refinement f R hm)) (lift f hf R hm S))
      (transitions (restrictedSmoothAtlas (SmoothPrincipalPullback.smoothAtlas f hf LM)
        (AnchoredPullbackRefinement.refinement f R hm)) (lift f hf R hm T))) =
      SpinHOneRestriction.restrictHom (AnchoredPullbackRefinement.reindex f R hm)
        (SpinHOnePullback.hom f hf R.domain (classOf (difference
          (transitions (restrictedSmoothAtlas LM R) S) (transitions (restrictedSmoothAtlas LM R) T)))) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  apply classOf_eq_of_overlap
  intro i j x hi hj
  apply Subtype.ext
  change ((difference (transitions _ (lift f hf R hm S)) (transitions _ (lift f hf R hm T))).val.value i j x).val =
    ((difference (transitions (restrictedSmoothAtlas LM R) S)
      (transitions (restrictedSmoothAtlas LM R) T)).val.value (f i) (f j) (f x)).val
  rw [difference_val _ _ i j x hi hj, difference_val _ _ (f i) (f j) (f x) hi hj,
    transition_eq f hf R hm LM S i j x hi hj, transition_eq f hf R hm LM T i j x hi hj]

/-- Inclusion of the reindexed relative class is the global pullback of the original relative class. -/
theorem difference_global (S T : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    SpinAllCoverHOne.ofCover (AnchoredPullbackRefinement.refinement f R hm).domain
      (AnchoredPullbackRefinement.refinement f R hm).covers
      (classOf (difference
        (transitions (restrictedSmoothAtlas (SmoothPrincipalPullback.smoothAtlas f hf LM)
          (AnchoredPullbackRefinement.refinement f R hm)) (lift f hf R hm S))
        (transitions (restrictedSmoothAtlas (SmoothPrincipalPullback.smoothAtlas f hf LM)
          (AnchoredPullbackRefinement.refinement f R hm)) (lift f hf R hm T)))) =
      SpinHOneGlobalPullback.pull f hf (SpinAllCoverHOne.ofCover R.domain R.covers
        (classOf (difference (transitions (restrictedSmoothAtlas LM R) S)
          (transitions (restrictedSmoothAtlas LM R) T)))) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  exact (congrArg (SpinAllCoverHOne.ofCover (AnchoredPullbackRefinement.refinement f R hm).domain
    (AnchoredPullbackRefinement.refinement f R hm).covers) (difference_class f hf R hm LM S T)).trans
      (AnchoredPullbackRefinement.ofCover_reindex f R hm hf _)

end FoliationQM.AnchoredAdaptedSpinPullback
