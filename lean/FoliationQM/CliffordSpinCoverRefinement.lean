module
public import FoliationQM.CliffordSpinCocycleCorrection

/-!
# Restriction of the Clifford sign obstruction to an open refinement

Source scope: the local-to-global Spin lifting component of v13
`prop:takabayasi` (A/C/D, component only). An open refinement specifies
which old chart contains each new chart. Restricting the smooth Lorentz
transitions, pair lifts and correcting signs along this map restricts the
actual kernel-valued triple defect. A solution of the original correction
equations thus gives a solution on the refined cover.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold
namespace FoliationQM.CliffordSpinCoverRefinement
open CliffordSpinTransitionLifts CliffordSpinCocycleCorrection

/-- An open refinement consists of a new cover and one containing old chart for each of its domains. -/
structure Refinement {B : Type*} [TopologicalSpace B] {ι : Type*}
    (U : ι → TopologicalSpace.Opens B) (κ : Type*) where
  /-- The original chart used to express each refined chart's transitions. -/
  parent : κ → ι
  /-- The open domains of the refined cover. -/
  domain : κ → TopologicalSpace.Opens B
  /-- Every base point belongs to some refined domain. -/
  covers : ∀ x : B, ∃ a, x ∈ domain a
  /-- Every refined domain lies in its designated original chart. -/
  subset : ∀ a, (domain a : Set B) ⊆ U (parent a)

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι κ : Type*} {n : WithTop ℕ∞}

/-- Pair overlaps of the refinement lie in the corresponding original pair overlaps. -/
theorem pair_subset {U : ι → TopologicalSpace.Opens B} (R : Refinement U κ) (a b : κ) :
    (R.domain a : Set B) ∩ R.domain b ⊆
      (U (R.parent a) : Set B) ∩ U (R.parent b) :=
  fun _ h => ⟨R.subset a h.1, R.subset b h.2⟩

/-- Restrict a smooth Lorentz cocycle by reindexing its transitions and restricting their smoothness and composition to the refined domains. -/
def lorentzData (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (R : Refinement D.domain κ) : CliffordSpinLorentzTransitions.Data I B κ n where
  domain := R.domain
  covers := R.covers
  transition a b := D.transition (R.parent a) (R.parent b)
  smooth_transition a b :=
    (D.smooth_transition (R.parent a) (R.parent b)).mono (pair_subset R a b)
  identity a x ha := D.identity (R.parent a) x (R.subset a ha)
  comp a b c x ha hb hc :=
    D.comp (R.parent a) (R.parent b) (R.parent c) x
      (R.subset a ha) (R.subset b hb) (R.subset c hc)

variable {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The refined Lorentz cocycle uses precisely the specified new open domains. -/
theorem lorentzData_domain (R : Refinement D.domain κ) :
    (lorentzData D R).domain = R.domain := rfl

/-- Each refined Lorentz transition uses its original parent transition as its representative. -/
theorem lorentzData_transition (R : Refinement D.domain κ) (a b : κ) :
    (lorentzData D R).transition a b = D.transition (R.parent a) (R.parent b) := rfl

/-- Restrict normalized physical Spin pair lifts to the refined pair overlaps. -/
def pairLifts (P : PairLifts D) (R : Refinement D.domain κ) : PairLifts (lorentzData D R) where
  transition a b := P.transition (R.parent a) (R.parent b)
  smooth_transition a b :=
    (P.smooth_transition (R.parent a) (R.parent b)).mono (pair_subset R a b)
  identity a x ha := P.identity (R.parent a) x (R.subset a ha)
  projection a b x ha hb :=
    P.projection (R.parent a) (R.parent b) x (R.subset a ha) (R.subset b hb)

/-- The normalized refined lift uses the original parent Spin transition as its representative. -/
theorem pairLifts_transition (P : PairLifts D) (R : Refinement D.domain κ) (a b : κ) :
    (pairLifts P R).transition a b = P.transition (R.parent a) (R.parent b) := rfl

/-- On a refined triple the ambient ordered Spin defect is the original ordered parent defect. -/
theorem pairLifts_defectValue (P : PairLifts D) (R : Refinement D.domain κ) (a b c : κ) :
    defectValue (pairLifts P R) a b c =
      defectValue P (R.parent a) (R.parent b) (R.parent c) := rfl

/-- A point of the true refined triple overlap lies in the original triple overlap of its parent charts. -/
theorem triple_subset (R : Refinement D.domain κ) (a b c : κ) :
    (tripleOverlap (lorentzData D R) a b c : Set B) ⊆
      tripleOverlap D (R.parent a) (R.parent b) (R.parent c) :=
  fun _ h => ⟨⟨R.subset a h.1.1, R.subset b h.1.2⟩, R.subset c h.2⟩

/-- The actual locally constant kernel sign on a refined triple overlap equals the parent sign pulled back by the overlap inclusion. -/
theorem pairLifts_kernelDefect (P : PairLifts D) (R : Refinement D.domain κ) (a b c : κ)
    (x : tripleOverlap (lorentzData D R) a b c) :
    kernelDefect (pairLifts P R) a b c x =
      kernelDefect P (R.parent a) (R.parent b) (R.parent c)
        ⟨x.val, triple_subset R a b c x.property⟩ := rfl

/-- Restrict the smooth, normalized correcting sign coefficients to genuine refined pair overlaps. -/
def correction (s : Correction D) (R : Refinement D.domain κ) : Correction (lorentzData D R) where
  value a b := s.value (R.parent a) (R.parent b)
  smooth_value a b := (s.smooth_value (R.parent a) (R.parent b)).mono (pair_subset R a b)
  projection a b x ha hb :=
    s.projection (R.parent a) (R.parent b) x (R.subset a ha) (R.subset b hb)
  identity a x ha := s.identity (R.parent a) x (R.subset a ha)

/-- Refined correcting signs use the original parent coefficients as their representatives. -/
theorem correction_value (s : Correction D) (R : Refinement D.domain κ) (a b : κ) :
    (correction s R).value a b = s.value (R.parent a) (R.parent b) := rfl

/-- Multiplying in the correcting coefficients commutes with restriction of the actual Spin pair lifts. -/
theorem corrected_pairLifts (P : PairLifts D) (s : Correction D) (R : Refinement D.domain κ) :
    corrected (pairLifts P R) (correction s R) = pairLifts (corrected P s) R := rfl

/-- A sign correction that removes the original defect also removes the restricted defect on every true refined triple overlap. -/
theorem removesDefect (R : Refinement D.domain κ) {P : PairLifts D} {s : Correction D}
    (hs : RemovesDefect P s) : RemovesDefect (pairLifts P R) (correction s R) :=
  fun a b c x ha hb hc =>
    hs (R.parent a) (R.parent b) (R.parent c) x (R.subset a ha) (R.subset b hb) (R.subset c hc)

end FoliationQM.CliffordSpinCoverRefinement
