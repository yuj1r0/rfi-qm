module
public import FoliationQM.CliffordSpinCoverRefinement

/-!
# Iterated refinement and restriction of genuine Spin lifts

Source scope: the global Spin-frame component of v13 `prop:takabayasi`.
The open inclusions compose on the original base. Restricting a genuine
cocycle therefore preserves its projection on the new pair overlaps.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.SpinRefinementComposition
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection

variable {B ι κ τ : Type*} [TopologicalSpace B] {U : ι → TopologicalSpace.Opens B}

/-- The original index family and open domains give the identity refinement of a cover. -/
def identity (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i) :
    Refinement U ι where
  parent := id
  domain := U
  covers := hU
  subset _ := Subset.rfl

/-- A refinement of a refinement uses the final opens and the composite parent index. -/
def compose (R : Refinement U κ) (T : Refinement R.domain τ) : Refinement U τ where
  parent a := R.parent (T.parent a)
  domain := T.domain
  covers := T.covers
  subset a := (T.subset a).trans (R.subset (T.parent a))

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The identity refinement recovers the entire original Lorentz cocycle. -/
theorem lorentzData_identity (D : CliffordSpinLorentzTransitions.Data I B ι n) :
    lorentzData D (identity D.domain D.covers) = D := rfl

/-- Two successive restrictions and the composite refinement give equal Lorentz data. -/
theorem lorentzData_compose (R : Refinement D.domain κ) (T : Refinement R.domain τ) :
    lorentzData (lorentzData D R) T = lorentzData D (compose R T) := rfl

/-- The actual pair lifts agree as records after iterated and composite restriction. -/
theorem pairLifts_compose (P : CliffordSpinTransitionLifts.PairLifts D)
    (R : Refinement D.domain κ) (T : Refinement R.domain τ) :
    pairLifts (pairLifts P R) T = pairLifts P (compose R T) := rfl

/-- The actual sign correction agrees after iterated and composite restriction. -/
theorem correction_compose (b : Correction D)
    (R : Refinement D.domain κ) (T : Refinement R.domain τ) :
    correction (correction b R) T = correction b (compose R T) := rfl

/-- Restrict a genuine Spin cocycle along open inclusions using its actual transition functions. -/
def spinData (S : CliffordSpinPolarCocycle.Data I B ι n) (R : Refinement S.domain κ) :
    CliffordSpinPolarCocycle.Data I B κ n where
  domain := R.domain
  covers := R.covers
  transition a b := S.transition (R.parent a) (R.parent b)
  smooth_transition a b := (S.smooth_transition _ _).mono
    (fun _ hx => ⟨R.subset a hx.1, R.subset b hx.2⟩)
  identity a x hx := S.identity _ x (R.subset a hx)
  comp a b c x ha hb hc := S.comp _ _ _ x (R.subset a ha) (R.subset b hb) (R.subset c hc)

/-- Physical projection commutes with restriction as equality of full Lorentz cocycle data. -/
theorem project_spinData (S : CliffordSpinPolarCocycle.Data I B ι n)
    (R : Refinement S.domain κ) :
    CliffordSpinLorentzTransitions.ofSpinData (spinData S R) =
      lorentzData (CliffordSpinLorentzTransitions.ofSpinData S) R := rfl

/-- The composite restriction of a genuine Spin cocycle equals its two successive restrictions. -/
theorem spinData_compose (S : CliffordSpinPolarCocycle.Data I B ι n)
    (R : Refinement S.domain κ) (T : Refinement R.domain τ) :
    spinData (spinData S R) T = spinData S (compose R T) := rfl

/-- A geometric transition cocycle with a genuine Spin lift retains a genuine lift on every refinement. -/
theorem hasSpinCocycleLift (R : Refinement D.domain κ) (h : HasSpinCocycleLift D) :
    HasSpinCocycleLift (lorentzData D R) := by
  obtain ⟨S, hdomain, hproj⟩ := h
  let RS : Refinement S.domain κ :=
    { R with subset := fun a => by simpa only [hdomain] using R.subset a }
  refine ⟨spinData S RS, rfl, ?_⟩
  intro a b x ha hb
  exact hproj (R.parent a) (R.parent b) x (R.subset a ha) (R.subset b hb)

end FoliationQM.SpinRefinementComposition
