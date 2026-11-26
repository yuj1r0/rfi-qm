module
public import FoliationQM.SpinSignHTwo
public import FoliationQM.SpinHOneDirected

/-!
# The directed system for degree-two Clifford sign cohomology

For the Spin-frame component of v13 `prop:takabayasi`, restriction on
point-indexed open neighborhoods gives a directed system of the original
obstruction groups. The same covering families used in degree one supply
common refinements and representatives of arbitrary open covers.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinHTwoDirected
open SpinSignCohomology SpinHOneDirected

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]

/-- Shrinking the neighborhood of each point restricts the degree-two obstruction group. -/
def transition (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (P Q : Cover B) (h : P ≤ Q) :
    ObstructionClass I P.domain n →* ObstructionClass I Q.domain n :=
  SpinSignHTwo.restrictHom (refine h)

variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

instance : DirectedSystem (fun P : Cover B => ObstructionClass I P.domain n)
    (fun _ _ h => (transition I n _ _ h : _ → _)) where
  map_self P x := SignClassRestriction.restrictClass_identity P.covers x
  map_map _ _ _ h k x := SignClassRestriction.restrictClass_compose (refine h) (refine k) x

end FoliationQM.SpinHTwoDirected
