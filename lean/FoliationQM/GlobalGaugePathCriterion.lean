module
public import FoliationQM.GlobalLorentzGaugeAtlas
public import FoliationQM.TransitionNullhomotopyCriterion

/-!
# When two whole-base Lorentz gauges have paths on the given cover

For the frame-bundle component of v13 `prop:takabayasi`, both charts of
the product atlas cover the entire base. The transition in one direction
is the gauge map itself, and in the other it is its inverse. The normalized
joint family on these specified charts exists precisely when the gauge
map is nullhomotopic.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalGaugePathCriterion
open LorentzMatrixGroup PathTransitionData PrincipalAtlasCrossGauge ContractibleTransitionPaths
open GlobalLorentzGaugeAtlas

variable {B : Type*} [TopologicalSpace B] (k : C(B, ProperFutureLorentz))

/-- Both global coordinates contain every point of the base. -/
theorem mem_pair (i j : Bool) (x : B) : x ∈ pairOverlap (data (atlas k)) i j := by
  change x ∈ ((atlas k).triv i).baseSet ∧ x ∈ ((atlas k).triv j).baseSet
  simp only [baseSet, Set.mem_univ, and_self]

/-- Regard any point of the original base as a point of any pair of the two global charts. -/
def toOverlap (i j : Bool) : C(B, ↥(pairOverlap (data (atlas k)) i j)) :=
  ⟨fun x => ⟨x, mem_pair k i j x⟩, continuous_id.subtype_mk _⟩

/-- Taking the false-to-true transition on the whole base recovers the actual gauge map. -/
theorem forward_comp : (transitionMap (data (atlas k)) false true).comp (toOverlap k false true) = k :=
  ContinuousMap.ext (fun x => transition_false_true k x)

/-- Inversion in the Lorentz group carries a contracting homotopy of the gauge to one for its inverse. -/
theorem nullhomotopic_inv (h : k.Nullhomotopic) : (k⁻¹).Nullhomotopic :=
  h.comp_right ⟨Inv.inv, continuous_inv⟩

/-- A contracting gauge makes both ordered off-diagonal transitions nullhomotopic. -/
theorem offDiagonalNull (h : k.Nullhomotopic) :
    TransitionNullhomotopyCriterion.OffDiagonalNull (data (atlas k)) := by
  intro i j hij
  let incl : C(↥(pairOverlap (data (atlas k)) i j), B) := ⟨Subtype.val, continuous_subtype_val⟩
  cases i <;> cases j
  · exact (hij rfl).elim
  · have e : transitionMap (data (atlas k)) false true = k.comp incl :=
      ContinuousMap.ext (fun x => transition_false_true k x)
    exact e.symm ▸ h.comp_left incl
  · have e : transitionMap (data (atlas k)) true false = (k⁻¹).comp incl :=
      ContinuousMap.ext (fun x => transition_true_false k x)
    exact e.symm ▸ (nullhomotopic_inv k h).comp_left incl
  · exact (hij rfl).elim

/-- The fixed unrefined atlas has normalized transition paths exactly when its gauge contracts. -/
theorem family_iff_nullhomotopic : Nonempty (Family (data (atlas k))) ↔ k.Nullhomotopic := by
  constructor
  · rintro ⟨P⟩
    have h := (TransitionNullhomotopyCriterion.nullhomotopic _ P false true).comp_left
      (toOverlap k false true)
    rwa [forward_comp] at h
  · intro h
    exact ⟨TransitionNullhomotopyCriterion.ofNull _ (offDiagonalNull k h)⟩

end FoliationQM.GlobalGaugePathCriterion
