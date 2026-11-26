module
public import FoliationQM.AtlasPathTransfer
public import FoliationQM.PresentedLorentzBundle

/-!
# Nullhomotopies on a fixed cover and after refinement

For the frame-bundle component of v13 `prop:takabayasi`, a transition family
on a specified cover exists precisely when the off-diagonal transition maps
are nullhomotopic on their entire true overlaps. For an actual Lorentz atlas,
the corresponding criterion on an anchored refinement characterizes existence
of a presentation of its projection and right action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TransitionNullhomotopyCriterion
open PathTransitionData ContractibleTransitionPaths

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [TopologicalSpace B]
  (D : Data G B ι)

/-- The homotopy carried by a normalized family on an entire ordered chart overlap. -/
def toHomotopy (P : Family D) (i j : ι) :
    (ContinuousMap.const ↥(pairOverlap D i j) 1).Homotopy (transitionMap D i j) where
  toContinuousMap := P.homotopy i j
  map_zero_left := P.source i j
  map_one_left := P.target i j

/-- A normalized family contracts each transition to the constant identity map. -/
theorem nullhomotopic (P : Family D) (i j : ι) : (transitionMap D i j).Nullhomotopic :=
  ⟨1, ⟨(toHomotopy D P i j).symm⟩⟩

/-- Nullhomotopy on the full overlap is only required for distinct chart indices. -/
def OffDiagonalNull : Prop :=
  ∀ i j, i ≠ j → (transitionMap D i j).Nullhomotopic

variable [PathConnectedSpace G]

/-- Join the unit to the given contracting value, then reverse the contraction. -/
def fromNull {X : Type*} [TopologicalSpace X] (f : C(X, G)) (h : f.Nullhomotopic) :
    (ContinuousMap.const X 1).Homotopy f :=
  (PathConnectedSpace.somePath 1 h.choose).toHomotopyConst.trans h.choose_spec.some.symm

/-- Use the constant path on the diagonal, independent of any nullhomotopy choices. -/
def joint (h : OffDiagonalNull D) (i j : ι) :
    (ContinuousMap.const ↥(pairOverlap D i j) 1).Homotopy (transitionMap D i j) := by
  classical
  by_cases e : i = j
  · subst j
    exact (ContinuousMap.Homotopy.refl (ContinuousMap.const _ (1 : G))).cast rfl
      (ContinuousMap.ext (fun x => (D.identity i x x.property.1).symm))
  · exact fromNull _ (h i j e)

/-- Diagonal paths are constantly one at every time. -/
theorem joint_diagonal (h : OffDiagonalNull D) (i : ι) (t : unitInterval)
    (x : pairOverlap D i i) : joint D h i i (t, x) = 1 := by
  classical
  simp only [joint]
  rfl

/-- Assemble the independently contracted pairs into the required normalized family. -/
def ofNull (h : OffDiagonalNull D) : Family D where
  homotopy i j := (joint D h i j).toContinuousMap
  source i j := (joint D h i j).apply_zero
  target i j := (joint D h i j).apply_one
  diagonal := joint_diagonal D h

/-- Exact fixed-cover criterion, including empty overlaps. -/
theorem nonempty_iff : Nonempty (Family D) ↔ OffDiagonalNull D :=
  ⟨fun ⟨P⟩ i j _ => nullhomotopic D P i j, fun h => ⟨ofNull D h⟩⟩

open LorentzMatrixGroup RefinedGeometricPrincipalAtlas PresentedLorentzBundle
open PrincipalAtlasCrossGauge CliffordSpinCoverRefinement

variable {T : Type*} [TopologicalSpace T] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)

/-- A presentation exists precisely when the original atlas has an anchored
refinement with nullhomotopic off-diagonal transitions. -/
theorem hasPresentation_iff :
    HasPresentation proj A.right ↔ ∃ R : Refinement (domains A) B,
      (∀ x, x ∈ R.domain x) ∧ OffDiagonalNull (data (restrictedAtlas A R)) := by
  constructor
  · rintro ⟨P⟩
    refine ⟨AtlasPathTransfer.refinement P.atlas A, AtlasPathTransfer.mem_refinement _ _, ?_⟩
    exact (nonempty_iff _).mp ⟨AtlasPathTransfer.family _ _ P.right_eq P.family⟩
  · rintro ⟨R, hR, h⟩
    exact ⟨{ atlas := restrictedAtlas A R, anchor := hR, right_eq := rfl, family := ofNull _ h }⟩

end FoliationQM.TransitionNullhomotopyCriterion
