module
public import FoliationQM.CliffordSpinCocycleCorrection

/-!
# Spin cocycle existence depends only on genuine overlap values

Source scope: the geometric Spin-structure bridge underlying v13
`prop:takabayasi`. Two actual Lorentz cocycles with identical open domains
and identical values on true pair overlaps have exactly the same existence
condition for a genuine same-cover Clifford Spin cocycle lift. The proof
retains the actual Spin cocycle witness; no equality of arbitrary off-overlap
fillers and no existence of a lift are assumed.
-/

@[expose] public section
open scoped Manifold
namespace FoliationQM.GeometricSpinStructure
open CliffordSpinCocycleCorrection

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞}
  {D D' : CliffordSpinLorentzTransitions.Data I B ι n}

/-- Genuine same-cover Clifford Spin cocycle existence is unchanged by replacing Lorentz transition values only outside their meaningful pair overlaps. -/
theorem hasSpinCocycleLift_congr (hdom : D.domain = D'.domain)
    (htrans : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      D.transition i j x = D'.transition i j x) :
    HasSpinCocycleLift D ↔ HasSpinCocycleLift D' := by
  constructor
  · rintro ⟨S, hs, hp⟩
    refine ⟨S, hs.trans hdom, ?_⟩
    intro i j x hi hj
    have hiD : x ∈ D.domain i := by rwa [hdom]
    have hjD : x ∈ D.domain j := by rwa [hdom]
    exact (hp i j x hiD hjD).trans (htrans i j x hiD hjD)
  · rintro ⟨S, hs, hp⟩
    refine ⟨S, hs.trans hdom.symm, ?_⟩
    intro i j x hi hj
    have hiD' : x ∈ D'.domain i := by rwa [← hdom]
    have hjD' : x ∈ D'.domain j := by rwa [← hdom]
    exact (hp i j x hiD' hjD').trans (htrans i j x hi hj).symm

end FoliationQM.GeometricSpinStructure
