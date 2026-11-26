module
public import FoliationQM.ParacompactLorentzPresentation
public import FoliationQM.LorentzIntrinsicObstruction

/-!
# Normalized paths for a refined smooth Lorentz atlas

For the frame component of v13 `prop:takabayasi`, restrict the actual
smooth principal trivializations to the paracompact refinement. Their
parent maps retain the original regularity on the smaller domains.
The normalized continuous paths on these domains end at the transitions
extracted from those same smooth charts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.ParacompactSmoothAtlasPaths
open LorentzMatrixGroup CliffordSpinLorentzSmooth RefinedGeometricPrincipalAtlas

variable {E H ET HT B T ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace H B] [ParacompactSpace B] [NormalSpace B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K A n)

include LM

/-- The restricted principal charts and inverses are smooth at the order of the original atlas. -/
theorem smoothAtlas : GeometricPrincipalSmoothAtlas.Data I lorentzModel K
    (ParacompactLorentzPresentation.atlas A) n :=
  restrictedSmoothAtlas LM (ParacompactLorentzPresentation.refinement A)

/-- On its refined source the forward map of the original parent chart is still Cⁿ. -/
theorem smooth_triv (a : B) : ContMDiffOn K (I.prod lorentzModel) n
    (A.triv ((ParacompactLorentzPresentation.refinement A).parent a))
    ((ParacompactLorentzPresentation.atlas A).triv a).source :=
  (smoothAtlas LM).smooth_triv a

/-- On its refined target the inverse map of the original parent chart is still Cⁿ. -/
theorem smooth_symm (a : B) : ContMDiffOn (I.prod lorentzModel) K n
    (A.triv ((ParacompactLorentzPresentation.refinement A).parent a)).toOpenPartialHomeomorph.symm
    ((ParacompactLorentzPresentation.atlas A).triv a).target :=
  (smoothAtlas LM).smooth_symm a

/-- Extract the genuine Lorentz transitions from the restricted smooth principal charts. -/
def transitions : CliffordSpinLorentzTransitions.Data I B B n :=
  AdaptedGeometricSpinLift.lorentzData (smoothAtlas LM)

/-- Extraction from the refined smooth atlas is restriction of the original smooth transition data. -/
theorem transitions_eq : transitions LM =
    CliffordSpinCoverRefinement.lorentzData (AdaptedGeometricSpinLift.lorentzData LM)
      (ParacompactLorentzPresentation.refinement A) := rfl

/-- The extracted open family consists of the paracompact refinement's actual chart domains. -/
theorem transitions_domain : (transitions LM).domain = (ParacompactLorentzPresentation.refinement A).domain := rfl

/-- Each refined transition is its original parent transition. -/
theorem transitions_value (a b x : B) : (transitions LM).transition a b x =
    A.transition ((ParacompactLorentzPresentation.refinement A).parent a)
      ((ParacompactLorentzPresentation.refinement A).parent b) x := rfl

/-- The parent transition is Cⁿ on the true overlap of the refined domains. -/
theorem smooth_transition (a b : B) : ContMDiffOn I lorentzModel n
    (A.transition ((ParacompactLorentzPresentation.refinement A).parent a)
      ((ParacompactLorentzPresentation.refinement A).parent b))
    (((transitions LM).domain a : Set B) ∩ (transitions LM).domain b) :=
  (transitions LM).smooth_transition a b

/-- Forgetting the differentiability proof yields the exact topological transition
data of the restricted geometric atlas. -/
theorem topologicalData_eq : LorentzIntrinsicObstruction.data (transitions LM) =
    PrincipalAtlasCrossGauge.data (ParacompactLorentzPresentation.atlas A) := rfl

/-- Joint paths to the transitions extracted from the order-n smooth atlas. -/
def paths : LorentzTransitionPaths.Family (transitions LM) :=
  LorentzIntrinsicObstruction.lorentzFamily (ParacompactLorentzPresentation.family A)

/-- Converting the smooth transition family back to the topological interface preserves every joint map. -/
theorem family_paths : LorentzIntrinsicObstruction.family (paths LM) =
    ParacompactLorentzPresentation.family A := rfl

/-- The constructed path starts at the physical Lorentz identity on every true pair. -/
theorem paths_zero (a b : B) (x : LorentzTransitionPaths.pairOverlap (transitions LM) a b) :
    (paths LM).homotopy a b (0, x) = 1 := (paths LM).source a b x

/-- The constructed path ends at the original parent transition evaluated at that point. -/
theorem paths_one (a b : B) (x : LorentzTransitionPaths.pairOverlap (transitions LM) a b) :
    (paths LM).homotopy a b (1, x) =
      A.transition ((ParacompactLorentzPresentation.refinement A).parent a)
        ((ParacompactLorentzPresentation.refinement A).parent b) x :=
  (paths LM).target a b x

/-- At every time the actual diagonal path is the constant identity. -/
theorem paths_diagonal (a : B) (t : unitInterval) (x : LorentzTransitionPaths.pairOverlap (transitions LM) a a) :
    (paths LM).homotopy a a (t, x) = 1 := (paths LM).diagonal a t x

end FoliationQM.ParacompactSmoothAtlasPaths
