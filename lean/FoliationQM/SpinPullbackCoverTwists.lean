module
public import FoliationQM.SpinPullbackTorsor
public import FoliationQM.GlobalSpinCoverTwists

/-!
# Smooth pullback of geometric Spin twists presented by cocycles

For the Spin-frame component of v13 `prop:takabayasi`, pull a geometric
twist back along a smooth map. It is physically isomorphic to the twist
of the pulled reference lift by the original sign cocycle evaluated on
the preimage cover. Two presentations on unrelated covers can thus be
compared on any common refinement over the new base.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackCoverTwists
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass
open SpinSignHOne SpinSignOneCocycle SpinAllCoverHOne GlobalSpinRealization
open GeometricPrincipalPullback SpinHOneRestriction CliffordSpinCoverRefinement

universe u
variable {X B : Type u} {T ι κ τ σ EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} {proj : T → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] [IsManifold IB n B] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n) (S : SmoothLift IB K L n)
  {U : κ → TopologicalSpace.Opens B} (hU : ∀ b, ∃ i, b ∈ U i)

/-- Pullback of the realized geometric twist represents the twist of the pulled reference by the pulled cocycle. -/
theorem class_twist (z : Cocycle IB U n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    physicalClass (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S U hU z)) =
      physicalClass (twistedFromCover (SmoothPrincipalPullback.smoothAtlas f hf LM)
        (GeometricSpinPullback.lift f hf LM S) (ModTwoPullback.domain f U)
        (ModTwoPullback.covers f hU) (SpinHOnePullback.cocycle f hf z)) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  change SpinPullbackClasses.classMap f hf LM (physicalClass (twistedFromCover LM S U hU z)) = _
  rw [← GlobalSpinCoverTwists.act_presented LM S hU z, SpinPullbackTorsor.classMap_act,
    SpinHOneGlobalPullback.pull_ofCover, SpinHOnePullback.hom_classOf]
  exact GlobalSpinCoverTwists.act_presented _ (GeometricSpinPullback.lift f hf LM S) _ _

/-- A smooth, equivariant diffeomorphism over the actual pulled Lorentz space relates the two constructions. -/
theorem twist_isomorphic (z : Cocycle IB U n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S U hU z))
      (twistedFromCover (SmoothPrincipalPullback.smoothAtlas f hf LM) (GeometricSpinPullback.lift f hf LM S)
        (ModTwoPullback.domain f U) (ModTwoPullback.covers f hU) (SpinHOnePullback.cocycle f hf z))) :=
  Quotient.exact (class_twist f hf LM S hU z)

variable {V : τ → TopologicalSpace.Opens B} (hV : ∀ b, ∃ i, b ∈ V i)

/-- Isomorphism of pulled twists from arbitrary input covers is detected by equality of the pulled global signs. -/
theorem twists_isomorphic_iff (z : Cocycle IB U n) (w : Cocycle IB V n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S U hU z))
      (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S V hV w))) ↔
        SpinHOneGlobalPullback.pull f hf (ofCover U hU (classOf z)) =
          SpinHOneGlobalPullback.pull f hf (ofCover V hV (classOf w)) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  let a := GeometricSpinPullback.lift f hf LM (twistedFromCover LM S U hU z)
  let b := GeometricSpinPullback.lift f hf LM (twistedFromCover LM S V hV w)
  have h : physicalClass a = physicalClass b ↔ Nonempty (SmoothBetween a b) := Quotient.eq
  refine h.symm.trans ?_
  dsimp only [a, b]
  rw [class_twist f hf LM S hU z, class_twist f hf LM S hV w, SpinHOneGlobalPullback.pull_ofCover,
    SpinHOneGlobalPullback.pull_ofCover, SpinHOnePullback.hom_classOf, SpinHOnePullback.hom_classOf]
  exact Quotient.eq.trans (GlobalSpinCoverTwists.twists_isomorphic_iff _ _ _ _ _ _)

/-- Equality of the signs on any specified common refinement of the preimage covers detects a physical isomorphism. -/
theorem twists_isomorphic_iff_common (W : σ → TopologicalSpace.Opens X) (hW : ∀ x, ∃ i, x ∈ W i)
    (p : σ → κ) (q : σ → τ) (hp : ∀ i, W i ≤ ModTwoPullback.domain f U (p i))
    (hq : ∀ i, W i ≤ ModTwoPullback.domain f V (q i)) (z : Cocycle IB U n) (w : Cocycle IB V n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S U hU z))
      (GeometricSpinPullback.lift f hf LM (twistedFromCover LM S V hV w))) ↔
        restrictHom (⟨p, W, hW, hp⟩ : Refinement (ModTwoPullback.domain f U) σ)
            (SpinHOnePullback.hom f hf U (classOf z)) =
          restrictHom (⟨q, W, hW, hq⟩ : Refinement (ModTwoPullback.domain f V) σ)
            (SpinHOnePullback.hom f hf V (classOf w)) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  rw [twists_isomorphic_iff, SpinHOneGlobalPullback.pull_ofCover, SpinHOneGlobalPullback.pull_ofCover]
  exact ofCover_eq_iff_common _ _ W hW p q hp hq _ _

end FoliationQM.SpinPullbackCoverTwists
