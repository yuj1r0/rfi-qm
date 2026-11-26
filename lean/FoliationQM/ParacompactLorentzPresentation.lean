module
public import FoliationQM.LocallyFiniteAtlasPresentation
public import FoliationQM.ParacompactChartShrinking

/-!
# General existence of Lorentz path presentations

For the frame-bundle component of v13 `prop:takabayasi`, an actual principal
Lorentz atlas on a paracompact normal base determines an anchored presentation
of its projection and right action. Paracompact Hausdorff bases satisfy these
hypotheses. The construction chooses a shrinking of the given open cover,
then constructs paths on a refinement of the original trivializations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ParacompactLorentzPresentation
open LorentzMatrixGroup PrincipalAtlasCrossGauge RefinedGeometricPrincipalAtlas
open PathTransitionData CliffordSpinCoverRefinement PresentedLorentzBundle

variable {B T ι : Type*} [TopologicalSpace B] [TopologicalSpace T] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)

section Normal
variable [hpc : ParacompactSpace B] [hn : NormalSpace B]

/-- Local finiteness and closure subordination follow from the topology of the base. -/
def shrinking : LocallyFiniteChartShrinking.Data (domains A) :=
  ParacompactChartShrinking.shrinking (domains A) A.covers

/-- The point-indexed refinement of the chart domains of the given atlas. -/
abbrev refinement : Refinement (domains A) B :=
  LocallyFiniteAtlasPresentation.refinement A (shrinking A)

/-- Actual restrictions of the parent trivializations on the same total space. -/
abbrev atlas := LocallyFiniteAtlasPresentation.atlas A (shrinking A)

/-- Every point belongs to the refined chart it indexes. -/
theorem mem_refinement (x : B) : x ∈ (refinement A).domain x :=
  ControlledTransitionRefinement.mem_refinement (data A) (shrinking A) x

/-- Every refined off-diagonal pair has a single Cayley neighborhood for its transition image. -/
theorem pairBounded : LorentzLocalPathFamily.PairBounded (data (atlas A)) :=
  LocallyFiniteAtlasPresentation.pairBounded A (shrinking A)

/-- Normalized paths on the constructed geometric atlas. -/
abbrev family : Family (data (atlas A)) :=
  LocallyFiniteAtlasPresentation.family A (shrinking A)

/-- A refined path reaches the original chart transition at each overlap point. -/
theorem family_target (a b : B) (x : pairOverlap (data (atlas A)) a b) :
    (family A).homotopy a b (1, x) = A.transition ((refinement A).parent a) ((refinement A).parent b) x :=
  LocallyFiniteAtlasPresentation.family_target A (shrinking A) a b x

/-- The presentation of the actual projected right action, chosen from its original atlas. -/
def presentation : Presentation proj A.right :=
  LocallyFiniteAtlasPresentation.presentation A (shrinking A)

/-- The presentation restricts the actual chart with the designated original parent. -/
theorem presentation_triv (a : B) :
    (presentation A).atlas.triv a = restrictedTriv A (refinement A) a := rfl

include hpc hn in
/-- Every geometric Lorentz principal atlas over a paracompact normal base admits a presentation. -/
theorem hasPresentation : HasPresentation proj A.right := ⟨presentation A⟩

include hpc hn in
/-- For a prescribed projection and action, presenting them is equivalent to exhibiting
ordinary principal charts indexed by the base points. -/
theorem hasPresentation_iff_atlas (right : T → ProperFutureLorentz → T) :
    HasPresentation proj right ↔
      ∃ C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj B, C.right = right := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.atlas, P.right_eq⟩
  · rintro ⟨C, rfl⟩
    exact hasPresentation C

end Normal

/-- In particular every geometric Lorentz atlas on a paracompact Hausdorff base
admits normalized paths after restricting its charts. -/
theorem hasPresentation_of_t2 [ParacompactSpace B] [T2Space B] :
    HasPresentation proj A.right := hasPresentation A

end FoliationQM.ParacompactLorentzPresentation
