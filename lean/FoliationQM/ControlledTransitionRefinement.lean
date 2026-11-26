module
public import FoliationQM.LocallyFiniteChartShrinking
public import FoliationQM.LorentzLocalPathFamily

/-!
# Simultaneous control of Lorentz transitions on a refinement

For the geometric frame component of v13 `prop:takabayasi`, shrink each
anchored chart inside the patches for all nearby parent charts. Local
finiteness controls the number of such conditions. Every transition on
a refined overlap stays in the Cayley neighborhood of its value at the
first anchor.
-/

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace FoliationQM.ControlledTransitionRefinement
open CliffordSpinCoverRefinement LorentzMatrixGroup PathTransitionData LorentzLocalPathFamily
open LocallyFiniteChartShrinking (parent mem_parent exists_control)

variable {B ι : Type*} [TopologicalSpace B] (D : PathTransitionData.Data ProperFutureLorentz B ι)
  (S : LocallyFiniteChartShrinking.Data D.domain)

/-- For each parent whose shrunken closure contains the anchor, use the true transition
patch centered there. Other parents impose no condition on the neighborhood. -/
def rowOpen (a : B) (j : ι) : Opens B := by
  classical
  exact if hj : a ∈ closure (S.carrier j : Set B) then
    patch D (parent S a) j ⟨a, S.closure_subset _ (subset_closure (mem_parent S a)), S.closure_subset j hj⟩
  else ⊤

/-- One anchored neighborhood lies in every incident transition patch while avoiding all nonincident carriers. -/
theorem exists_row (a : B) :
    ∃ W : Opens B, a ∈ W ∧ W ≤ S.carrier (parent S a) ∧
      (∀ y ∈ W, ∀ j, y ∈ S.carrier j → a ∈ closure (S.carrier j : Set B)) ∧
      (∀ j, a ∈ closure (S.carrier j : Set B) → W ≤ rowOpen D S a j) := by
  apply exists_control S a (rowOpen D S a)
  intro j hj
  simpa only [rowOpen, dite_eq_left hj] using mem_patch D (parent S a) j
    ⟨a, S.closure_subset _ (subset_closure (mem_parent S a)), S.closure_subset j hj⟩

/-- Refine the Lorentz chart domains by anchored opens controlling all incident transitions at once. -/
def refinement : Refinement D.domain B where
  parent := parent S
  domain a := (exists_row D S a).choose
  covers x := ⟨x, (exists_row D S x).choose_spec.1⟩
  subset a _ hx := S.closure_subset _ (subset_closure ((exists_row D S a).choose_spec.2.1 hx))

/-- Every point belongs to the domain indexed by that point. -/
theorem mem_refinement (a : B) : a ∈ (refinement D S).domain a :=
  (exists_row D S a).choose_spec.1

/-- The chosen original index is the parent of the anchor in the shrunken cover. -/
theorem refinement_parent (a : B) : (refinement D S).parent a = parent S a := rfl

/-- Each refined domain stays in the shrunken carrier of its own parent. -/
theorem domain_subset_carrier (a : B) : (refinement D S).domain a ≤ S.carrier (parent S a) :=
  (exists_row D S a).choose_spec.2.1

/-- A point of both refined domains forces the first anchor into the closure of the second carrier. -/
theorem anchor_mem_closure_of_overlap (a b : B)
    (x : pairOverlap (IntrinsicPathRestriction.data D (refinement D S)) a b) :
    a ∈ closure (S.carrier (parent S b) : Set B) :=
  (exists_row D S a).choose_spec.2.2.1 x x.property.1 (parent S b)
    (domain_subset_carrier D S b x.property.2)

/-- On the whole refined pair the transition stays in the neighborhood of its original value
at the first anchor. This also holds when the two parent indices agree. -/
theorem transition_mem (a b : B)
    (x : pairOverlap (IntrinsicPathRestriction.data D (refinement D S)) a b) :
    (IntrinsicPathRestriction.data D (refinement D S)).transition a b x ∈
      LorentzLocalPaths.neighborhood (D.transition (parent S a) (parent S b) a) := by
  have hj := anchor_mem_closure_of_overlap D S a b x
  have hrow := (exists_row D S a).choose_spec.2.2.2 (parent S b) hj x.property.1
  rw [rowOpen, dite_eq_left hj] at hrow
  exact patch_image D (parent S a) (parent S b) _ hrow

/-- One Cayley neighborhood contains each entire off-diagonal refined transition image. -/
theorem pairBounded : PairBounded (IntrinsicPathRestriction.data D (refinement D S)) :=
  fun a b _ => ⟨D.transition (parent S a) (parent S b) a, transition_mem D S a b⟩

end FoliationQM.ControlledTransitionRefinement
