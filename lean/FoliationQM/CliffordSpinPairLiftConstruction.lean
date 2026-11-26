module
public import FoliationQM.CliffordSpinGlobalLift
public import FoliationQM.CliffordSpinTransitionLifts

/-!
# Constructing actual pairwise Spin lifts on simply connected overlaps

Source scope: the local lifting step for independent Lorentz transition
cocycles in v13 Section 7 and `prop:takabayasi`. Each nonempty pair
intersection is explicitly assumed simply connected and locally path
connected in its original open-subset topology. The proved universal
cover lifting theorem then constructs actual smooth Clifford Spin lifts
of the given transitions on those intersections.

Empty intersections impose no anchor or connectivity premise. Diagonal
transitions are identically the genuine Clifford unit. Off their pair
intersection the constructed functions are assigned the unit, with
smoothness asserted only on the actual intersection. The output is the
independently defined pair-lift structure, whose triple defect need not
vanish. No arbitrary Lorentz cocycle lift or automatic spacetime Spin
structure is inferred from the pairwise construction.
-/

@[expose] public section
noncomputable section
open scoped Topology Manifold
open Set Topology TopologicalSpace
namespace FoliationQM.CliffordSpinPairLiftConstruction
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup
open CliffordSpinGlobalLift

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}

/-- The original open pair intersection on which a supplied Lorentz transition must be lifted. -/
abbrev pairOverlap (D : CliffordSpinLorentzTransitions.Data I B ι n) (i j : ι) :
    Opens B := D.domain i ⊓ D.domain j

private def extendOne {U : Opens B} (f : U → Spin) (x : B) : Spin := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 1

private theorem extendOne_eq {U : Opens B} (f : U → Spin) (x : B) (hx : x ∈ U) :
    extendOne f x = f ⟨x, hx⟩ := by
  classical
  exact dite_eq_left hx

private theorem contMDiffOn_extendOne {U : Opens B} (f : U → Spin)
    (hf : ContMDiff I spinModel n f) :
    ContMDiffOn I spinModel n (extendOne f) (U : Set B) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (I := I) (I' := spinModel)
    (f := extendOne f) (x := ⟨x, hx⟩)).mp
  have he : (fun y : U => extendOne f y) = f := by
    funext y
    exact extendOne_eq f y y.property
  rw [he]
  exact hf ⟨x, hx⟩

private def overlapLorentzField (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (i j : ι) : C^n⟮I, ↥(pairOverlap D i j); lorentzModel, ProperFutureLorentz⟯ :=
  ⟨fun x => D.transition i j x,
    (D.smooth_transition i j).comp_contMDiff contMDiff_subtype_val (fun x => x.property)⟩

/-- On each actual pair intersection, explicit simple connectivity and local path connectivity when it is nonempty give a smooth actual Spin lift, extended by the unit off the intersection. -/
theorem exists_pairLift (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (i j : ι)
    (hsc : Nonempty ↥(pairOverlap D i j) → SimplyConnectedSpace ↥(pairOverlap D i j))
    (hlpc : Nonempty ↥(pairOverlap D i j) → LocallyPathConnectedSpace ↥(pairOverlap D i j)) :
    ∃ f : B → Spin,
      ContMDiffOn I spinModel n f (pairOverlap D i j : Set B) ∧
      (∀ x, x ∈ pairOverlap D i j → lorentzHom (f x) = D.transition i j x) ∧
      (∀ x, x ∉ pairOverlap D i j → f x = 1) := by
  classical
  by_cases hU : Nonempty ↥(pairOverlap D i j)
  · let : SimplyConnectedSpace ↥(pairOverlap D i j) := hsc hU
    let : LocallyPathConnectedSpace ↥(pairOverlap D i j) := hlpc hU
    let x0 : pairOverlap D i j := Classical.choice hU
    obtain ⟨s0, hs⟩ := lorentzHom_surjective (D.transition i j x0)
    let g := smoothLift (overlapLorentzField D i j) x0 s0 hs
    refine ⟨extendOne g, contMDiffOn_extendOne g g.contMDiff, ?_, ?_⟩
    · intro x hx
      rw [extendOne_eq]
      exact congrFun (projection_smoothLift (overlapLorentzField D i j) x0 s0 hs) ⟨x, hx⟩
    · intro x hx
      exact dite_eq_right hx
  · refine ⟨fun _ => 1, contMDiffOn_const, ?_, ?_⟩
    · intro x hx
      exact False.elim (hU ⟨⟨x, hx⟩⟩)
    · intro x hx
      rfl

/-- Explicit simple connectivity and local path connectivity on each nonempty actual pair intersection suffice to construct normalized smooth genuine Clifford Spin pair lifts of the supplied Lorentz data. -/
def pairLifts (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (hsc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      SimplyConnectedSpace ↥(pairOverlap D i j))
    (hlpc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      LocallyPathConnectedSpace ↥(pairOverlap D i j)) :
    CliffordSpinTransitionLifts.PairLifts D := by
  classical
  let f : ι → ι → B → Spin := fun i j =>
    if i = j then fun _ => 1 else (exists_pairLift D i j (hsc i j) (hlpc i j)).choose
  refine { transition := f, smooth_transition := ?_, identity := ?_, projection := ?_ }
  · intro i j
    dsimp [f]
    split
    · exact contMDiffOn_const
    · exact (exists_pairLift D i j (hsc i j) (hlpc i j)).choose_spec.1
  · intro i x hx
    simp only [f, ite_true]
  · intro i j x hi hj
    dsimp [f]
    split_ifs with hij
    · subst j
      rw [map_one, D.identity i x hi]
    · exact (exists_pairLift D i j (hsc i j) (hlpc i j)).choose_spec.2.1 x ⟨hi, hj⟩

/-- The constructed diagonal Spin transitions are literally the Clifford unit on the entire base, including outside the chart domain. -/
theorem pairLifts_diagonal (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (hsc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      SimplyConnectedSpace ↥(pairOverlap D i j))
    (hlpc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      LocallyPathConnectedSpace ↥(pairOverlap D i j)) (i : ι) (x : B) :
    (pairLifts D hsc hlpc).transition i i x = 1 := by
  classical
  simp only [pairLifts, ite_true]

/-- Outside the relevant pair intersection the chosen actual Spin extension is the Clifford unit; no off-intersection regularity or projection statement is asserted. -/
theorem pairLifts_outside (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (hsc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      SimplyConnectedSpace ↥(pairOverlap D i j))
    (hlpc : ∀ i j, Nonempty ↥(pairOverlap D i j) →
      LocallyPathConnectedSpace ↥(pairOverlap D i j)) (i j : ι) (x : B)
    (hx : x ∉ pairOverlap D i j) : (pairLifts D hsc hlpc).transition i j x = 1 := by
  classical
  by_cases hij : i = j
  · subst j
    exact pairLifts_diagonal D hsc hlpc i x
  · change (if i = j then fun _ => 1 else
      (exists_pairLift D i j (hsc i j) (hlpc i j)).choose) x = 1
    rw [ite_eq_right hij]
    exact (exists_pairLift D i j (hsc i j) (hlpc i j)).choose_spec.2.2 x hx

end FoliationQM.CliffordSpinPairLiftConstruction
