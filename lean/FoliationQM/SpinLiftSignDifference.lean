module
public import FoliationQM.SpinSignOneCocycle
public import FoliationQM.SpinPairLiftDifference
public import FoliationQM.SpinSignDefectRepresentative

/-!
# Sign differences and twists of genuine Clifford Spin lifts

Source scope: the global Spin-frame component of v13 `prop:takabayasi`.
Two smooth Spin cocycles projecting to the same Lorentz data differ on
their pair overlaps by a normalized sign one-cocycle. Conversely, a sign
one-cocycle twists a given lift while preserving its physical projection
and its ordered composition law.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinLiftSignDifference
open CliffordSpinLorentz CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinSignCohomology SpinSignDefectRepresentative

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- A genuine lift of the given Lorentz cocycle has its normalized pair lifts and the ordered triple-overlap composition law. -/
structure Lift (D : CliffordSpinLorentzTransitions.Data I B ι n) extends PairLifts D where
  /-- On three intersecting charts the lifted transition from the first to the last is their ordered product. -/
  comp : ∀ i j k x, x ∈ D.domain i → x ∈ D.domain j → x ∈ D.domain k →
    transition j k x * transition i j x = transition i k x

/-- The genuine Clifford cocycle underlying a lift uses exactly the original Lorentz chart domains. -/
def spinData (P : Lift D) : CliffordSpinPolarCocycle.Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition := P.transition
  smooth_transition := P.smooth_transition
  identity := P.identity
  comp := P.comp

/-- A genuine Spin cocycle with the same open domains and the specified physical projection defines a lift. -/
def ofSpinData (S : CliffordSpinPolarCocycle.Data I B ι n) (hd : S.domain = D.domain)
    (hp : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      lorentzHom (S.transition i j x) = D.transition i j x) : Lift D where
  transition := S.transition
  smooth_transition i j := by simpa only [hd] using S.smooth_transition i j
  identity i x hi := S.identity i x (hd ▸ hi)
  projection := hp
  comp i j k x hi hj hk := S.comp i j k x (hd ▸ hi) (hd ▸ hj) (hd ▸ hk)

/-- The type of genuine lifts is inhabited exactly when the established same-cover Spin lifting criterion holds. -/
theorem nonempty_lift_iff : Nonempty (Lift D) ↔ HasSpinCocycleLift D := by
  constructor
  · rintro ⟨P⟩
    exact ⟨spinData P, rfl, P.projection⟩
  · rintro ⟨S, hd, hp⟩
    exact ⟨ofSpinData S hd hp⟩

/-- A genuine lift has unit physical defect on each triple overlap. -/
theorem defectValue_one (P : Lift D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    defectValue P.toPairLifts i j k x = 1 :=
  (defectValue_eq_one_iff _ i j k x).mpr (P.comp i j k x hi hj hk)

/-- The physical ratio from one genuine lift to another satisfies the sign one-cocycle law on every triple overlap. -/
theorem difference_isCocycle (P Q : Lift D) :
    SpinSignOneCocycle.IsCocycle (ofCorrection
      (SpinPairLiftDifference.difference P.toPairLifts Q.toPairLifts)) := by
  let s := SpinPairLiftDifference.difference P.toPairLifts Q.toPairLifts
  intro i j k x hi hj hk
  apply Subtype.ext
  change ((ofCorrection s).value j k x).val * ((ofCorrection s).value i j x).val =
    ((ofCorrection s).value i k x).val
  rw [ofCorrection_val s j k x hj hk, ofCorrection_val s i j x hi hj, ofCorrection_val s i k x hi hk]
  have h : (corrected P.toPairLifts s).transition j k x * (corrected P.toPairLifts s).transition i j x =
      (corrected P.toPairLifts s).transition i k x := by
    rw [show corrected P.toPairLifts s = Q.toPairLifts from SpinPairLiftDifference.corrected_difference _ _]
    exact Q.comp i j k x hi hj hk
  have he := (corrected_comp_iff P.toPairLifts s i j k x hi hj).mp h
  rwa [defectValue_one P i j k x hi hj hk, mul_one] at he

/-- The normalized smooth one-cocycle comparing two genuine lifts of the same Lorentz data. -/
def difference (P Q : Lift D) : SpinSignOneCocycle.Cocycle I D.domain n :=
  ⟨ofCorrection (SpinPairLiftDifference.difference P.toPairLifts Q.toPairLifts),
    difference_isCocycle P Q⟩

/-- On a genuine pair overlap the difference sign is the ordered ratio of the second and first lifted transitions. -/
theorem difference_val (P Q : Lift D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    ((difference P Q).val.value i j x).val = Q.transition i j x * (P.transition i j x)⁻¹ :=
  ofCorrection_val _ i j x hi hj

/-- Multiplying the physical transitions by a smooth sign one-cocycle yields a genuine lift of the same Lorentz transitions. -/
def twist (P : Lift D) (z : SpinSignOneCocycle.Cocycle I D.domain n) : Lift D where
  toPairLifts := corrected P.toPairLifts (toCorrection z.val)
  comp i j k x hi hj hk := by
    apply (corrected_comp_iff P.toPairLifts (toCorrection z.val) i j k x hi hj).mpr
    rw [defectValue_one P i j k x hi hj hk, mul_one]
    exact congrArg Subtype.val (z.property i j k x hi hj hk)

/-- Each twisted transition is the left product of the sign coefficient with the original Spin transition. -/
theorem twist_transition (P : Lift D) (z : SpinSignOneCocycle.Cocycle I D.domain n)
    (i j : ι) (x : B) :
    (twist P z).transition i j x = (z.val.value i j x).val * P.transition i j x := rfl

end FoliationQM.SpinLiftSignDifference
