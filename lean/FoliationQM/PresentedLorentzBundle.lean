module
public import FoliationQM.GeometricAtlasObstruction
public import FoliationQM.RefinedGeometricPrincipalAtlas
public import FoliationQM.SignCommonRefinement

/-!
# The intrinsic class of a presented Lorentz principal bundle

For the geometric frame component of v13 `prop:takabayasi`, fix a
topological total space, its projection and its right Lorentz action.
A presentation gives an actual principal atlas and normalized joint
paths to its transitions. Taking one chart containing each base point
puts presentations on a common index type. The class of the resulting
bundle depends only on its projection and right action once a presentation
exists, by comparison of the actual charts of every pair of presentations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PresentedLorentzBundle
open LorentzMatrixGroup PrincipalAtlasCrossGauge PathTransitionData
open RefinedGeometricPrincipalAtlas SignCommonRefinement

variable {B T ι : Type*} [TopologicalSpace B] [TopologicalSpace T]

/-- A base-indexed geometric principal atlas and its actual joint transition
paths, for the prescribed projection and right action. -/
structure Presentation (proj : T → B) (right : T → ProperFutureLorentz → T) where
  /-- Actual trivializations of the fixed projection, indexed by points of the base. -/
  atlas : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj B
  /-- The chart indexed by each point contains that point. -/
  anchor : ∀ x : B, x ∈ (atlas.triv x).baseSet
  /-- The geometric operation in the atlas is the prescribed operation. -/
  right_eq : atlas.right = right
  /-- Normalized jointly continuous paths to the actual geometric transitions. -/
  family : Family (data atlas)

/-- Existence of a topological presentation on the original total space. -/
abbrev HasPresentation (proj : T → B) (right : T → ProperFutureLorentz → T) : Prop :=
  Nonempty (Presentation proj right)

variable {proj : T → B} {right : T → ProperFutureLorentz → T}

/-- Choose one containing chart per base point and restrict both the original
trivializations and the entire joint transition family to that cover. -/
def ofAtlas (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (P : Family (data A)) : Presentation proj right where
  atlas := restrictedAtlas A (pointCover (domains A) A.covers)
  anchor x := pointCover_mem (domains A) A.covers x
  right_eq := hr
  family := IntrinsicPathRestriction.family P (pointCover (domains A) A.covers)

/-- The base-indexed atlas of the presentation consists of the selected original charts. -/
theorem ofAtlas_atlas (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (P : Family (data A)) :
    (ofAtlas A hr P).atlas = restrictedAtlas A (pointCover (domains A) A.covers) := rfl

/-- The entire base-indexed path family is the restriction of the original joint maps. -/
theorem ofAtlas_family (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (P : Family (data A)) :
    (ofAtlas A hr P).family = IntrinsicPathRestriction.family P (pointCover (domains A) A.covers) := rfl

/-- An atlas and path family supply the presentation-existence witness for any index universe. -/
theorem has_of_atlas (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (P : Family (data A)) : HasPresentation proj right :=
  ⟨ofAtlas A hr P⟩

/-- Standard contractibility of the nonempty chart pairs constructs a bundle presentation. -/
def ofContractible (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (hA : ContractibleTransitionPaths.PairContractible (data A)) :
    Presentation proj right := ofAtlas A hr (ContractibleTransitionPaths.family (data A) hA)

/-- A geometric atlas with contractible nonempty pairs supplies a presentation-existence witness. -/
theorem has_of_contractible (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (hA : ContractibleTransitionPaths.PairContractible (data A)) :
    HasPresentation proj right := ⟨ofContractible A hr hA⟩

variable [LocallyPathConnectedSpace B]

/-- The intrinsic global class computed in a given geometric presentation. -/
def value (p : Presentation proj right) : ModTwoAllCover.GlobalH2 B :=
  GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character p.family

/-- The all-cover obstruction of this projection and geometric right action, defined
whenever they have a presentation. -/
def obstruction (h : HasPresentation proj right) : ModTwoAllCover.GlobalH2 B :=
  value (Classical.choice h)

/-- Every presentation of the given projection and action, with arbitrary original
cover index, computes the same bundle class. -/
theorem obstruction_eq (h : HasPresentation proj right)
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (P : Family (data A)) :
    obstruction h = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character P :=
  GeometricAtlasObstruction.obstruction_eq (Classical.choice h).atlas A
    ((Classical.choice h).right_eq.trans hr.symm) (Classical.choice h).family P

/-- The class can be evaluated on any actual base-indexed presentation. -/
theorem obstruction_eq_value (h : HasPresentation proj right) (p : Presentation proj right) :
    obstruction h = value p := obstruction_eq h p.atlas p.right_eq p.family

/-- Contractible nonempty pairs give the computed bundle class directly from the
original geometric transitions and the generic contraction construction. -/
theorem obstruction_eq_constructed (h : HasPresentation proj right)
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (hr : A.right = right) (hA : ContractibleTransitionPaths.PairContractible (data A)) :
    obstruction h = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character
      (ContractibleTransitionPaths.family (data A) hA) := obstruction_eq h A hr _

/-- The intrinsic bundle class is the unique all-cover class taking the value
computed by every actual presentation of this projection and action. -/
theorem existsUnique_value (h : HasPresentation proj right) :
    ∃! c : ModTwoAllCover.GlobalH2 B, ∀ p : Presentation proj right, c = value p := by
  refine ⟨obstruction h, obstruction_eq_value h, ?_⟩
  intro c hc
  exact hc (Classical.choice h)

end FoliationQM.PresentedLorentzBundle
