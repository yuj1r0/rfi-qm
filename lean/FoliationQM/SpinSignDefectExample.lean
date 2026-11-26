module
public import FoliationQM.CliffordSpinCocycleCorrection

/-!
# A removable negative Clifford sign on an actual triple overlap

Source scope: the sign-correction component of v13 `prop:takabayasi`.
The opens `(-∞, 1)` and `(-1, ∞)` cover the real line. Starting from the
identity cocycle, change just the ordered transition from chart zero to
chart one by the negative Clifford unit. Its defect on the triple
`(0,1,0)` is negative. Applying the same sign again gives the identity
transitions on every ordered pair.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinSignDefectExample
open CliffordSpinMap CliffordSpinEquivalence CliffordSpinLorentz
open CliffordSpinTransitionLifts CliffordSpinCocycleCorrection

/-- The first chart is the open ray below one and the second is the open ray above minus one. -/
def domains (i : Fin 2) : TopologicalSpace.Opens ℝ :=
  if i = 0 then ⟨Set.Iio 1, isOpen_Iio⟩ else ⟨Set.Ioi (-1), isOpen_Ioi⟩

/-- Every real point belongs to at least one of the two open rays. -/
theorem covers (x : ℝ) : ∃ i, x ∈ domains i := by
  by_cases h : x < 1
  · exact ⟨0, by simpa [domains] using h⟩
  · refine ⟨1, ?_⟩
    have hx : -1 < x := lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 1) (le_of_not_gt h)
    simpa [domains] using hx

/-- The Lorentz transitions are the physical projection of the genuine identity cocycle on these rays. -/
def lorentzData (n : WithTop ℕ∞) : CliffordSpinLorentzTransitions.Data 𝓘(ℝ, ℝ) ℝ (Fin 2) n :=
  CliffordSpinLorentzTransitions.ofSpinData
    (CliffordSpinPolarCocycle.identityData domains covers)

/-- The pair coefficient is the genuine negative Clifford unit precisely on the arrow from zero to one. -/
def pairSign (i j : Fin 2) : Spin := if i = 0 ∧ j = 1 then negativeOne else 1

/-- Every chosen pair coefficient squares to the Clifford identity, using the actual kernel generator's order. -/
theorem pairSign_mul_self (i j : Fin 2) : pairSign i j * pairSign i j = 1 := by
  unfold pairSign
  split
  · have h := pow_orderOf_eq_one CliffordSpinSignKernel.generator
    rw [CliffordSpinSignKernel.generator_orderOf, pow_two] at h
    exact congrArg Subtype.val h
  · exact one_mul 1

/-- The smooth central sign correction is constant on each ordered pair overlap and normalized on the diagonal. -/
def signCorrection (n : WithTop ℕ∞) : Correction (lorentzData n) where
  value i j _ := pairSign i j
  smooth_value _ _ := contMDiff_const.contMDiffOn
  projection i j _ _ _ := by
    unfold pairSign
    split
    · exact CliffordSpinPolarAction.lorentz_negativeOne
    · exact map_one _
  identity i _ _ := by fin_cases i <;> simp [pairSign]

/-- Twisting the identity pair lifts by the selected single negative arrow gives normalized smooth lifts of the same Lorentz data. -/
def pairLifts (n : WithTop ℕ∞) : PairLifts (lorentzData n) :=
  corrected (identityPairLifts domains covers) (signCorrection n)

/-- The literal Spin transition on each ordered pair equals its single selected coefficient. -/
theorem pairLifts_transition (n : WithTop ℕ∞) (i j : Fin 2) (x : ℝ) :
    (pairLifts n).transition i j x = pairSign i j := mul_one _

/-- Zero belongs to the genuine triple overlap of the first, second and first open charts. -/
theorem zero_mem_tripleOverlap (n : WithTop ℕ∞) : (0 : ℝ) ∈ tripleOverlap (lorentzData n) 0 1 0 := by
  change (0 : ℝ) ∈ ((domains 0 : Set ℝ) ∩ domains 1) ∩ domains 0
  norm_num [domains]

/-- The ordered raw defect from chart zero via chart one back to chart zero is the negative Clifford unit. -/
theorem defectValue_negativeOne (n : WithTop ℕ∞) (x : ℝ) :
    defectValue (pairLifts n) 0 1 0 x = negativeOne := by
  simp [defectValue, pairLifts_transition, pairSign]

/-- The displayed raw triple defect differs from the Clifford identity. -/
theorem defectValue_ne_one (n : WithTop ℕ∞) (x : ℝ) :
    defectValue (pairLifts n) 0 1 0 x ≠ 1 := by
  rw [defectValue_negativeOne]
  exact negativeOne_ne_one

/-- At zero on the genuine overlap, the kernel-valued defect is the distinguished negative generator. -/
theorem kernelDefect_zero (n : WithTop ℕ∞) :
    kernelDefect (pairLifts n) 0 1 0 ⟨0, zero_mem_tripleOverlap n⟩ =
      CliffordSpinSignKernel.generator :=
  Subtype.ext (defectValue_negativeOne n 0)

/-- Applying the explicit correcting sign on each ordered pair recovers the identity transition everywhere. -/
theorem corrected_transition_one (n : WithTop ℕ∞) (i j : Fin 2) (x : ℝ) :
    (corrected (pairLifts n) (signCorrection n)).transition i j x = 1 := by
  rw [corrected_transition, pairLifts_transition]
  exact pairSign_mul_self i j

/-- The same concrete pair sign solves every genuine triple-overlap defect equation on the two-chart cover. -/
theorem removesDefect (n : WithTop ℕ∞) : RemovesDefect (pairLifts n) (signCorrection n) := by
  intro i j k x hi hj hk
  apply (corrected_comp_iff (pairLifts n) (signCorrection n) i j k x hi hj).mp
  simp only [corrected_transition_one, one_mul]

end FoliationQM.SpinSignDefectExample
