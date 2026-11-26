module
public import FoliationQM.CliffordSpinLorentzTransitions
public import Mathlib.Topology.Path

/-!
# Jointly continuous normalized paths to Lorentz transitions

For the Spin-frame component of v13 `prop:takabayasi`, the supplied
data here are paths in the physical Lorentz group. Their joint
continuity on time times the actual pair overlap is explicit.
No Spin endpoint, Spin lift, or connectivity of the overlap is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped Topology
namespace FoliationQM.LorentzTransitionPaths
open LorentzMatrixGroup

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}

/-- The original open intersection on which a Lorentz transition is specified. -/
abbrev pairOverlap (D : CliffordSpinLorentzTransitions.Data I B ι n) (i j : ι) :
    TopologicalSpace.Opens B := D.domain i ⊓ D.domain j

/-- Normalized paths from the identity to the given Lorentz transitions,
jointly continuous in time and the point of their actual pair overlap. -/
structure Family (D : CliffordSpinLorentzTransitions.Data I B ι n) where
  /-- Joint continuity, rather than separate pointwise choices of paths. -/
  homotopy : ∀ i j, C(unitInterval × ↥(pairOverlap D i j), ProperFutureLorentz)
  /-- Each transition path starts at the Lorentz identity. -/
  source : ∀ i j (x : pairOverlap D i j), homotopy i j (0, x) = 1
  /-- Each transition path ends at the specified physical Lorentz transition. -/
  target : ∀ i j (x : pairOverlap D i j), homotopy i j (1, x) = D.transition i j x
  /-- Every diagonal transition is represented by the constant identity path. -/
  diagonal : ∀ i (t : unitInterval) (x : pairOverlap D i i), homotopy i i (t, x) = 1

variable {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The actual Lorentz transition path at a point of a genuine pair overlap. -/
def path (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : Path 1 (D.transition i j x) where
  toContinuousMap := (P.homotopy i j).comp
    ((ContinuousMap.id unitInterval).prodMk (.const unitInterval ⟨x, hi, hj⟩))
  source' := P.source i j ⟨x, hi, hj⟩
  target' := P.target i j ⟨x, hi, hj⟩

/-- The pointwise path is exactly the time slice of the given joint family. -/
theorem path_apply (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (t : unitInterval) :
    path P i j x hi hj t = P.homotopy i j (t, ⟨x, hi, hj⟩) := rfl

/-- The actual time slice starts at the physical identity. -/
theorem path_zero (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : path P i j x hi hj 0 = 1 :=
  (path P i j x hi hj).source

/-- The actual time slice ends at the specified Lorentz transition. -/
theorem path_one (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    path P i j x hi hj 1 = D.transition i j x := (path P i j x hi hj).target

/-- Every pointwise diagonal path is identically the Lorentz identity. -/
theorem path_diagonal (P : Family D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) (t : unitInterval) : path P i i x hi hi t = 1 :=
  P.diagonal i t ⟨x, hi, hi⟩

end FoliationQM.LorentzTransitionPaths
