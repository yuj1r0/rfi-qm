module
public import FoliationQM.PolarSignCovering
public import FoliationQM.SourcePolarRealization
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
/-!
# An actual polar loop obstructs global continuous representatives

Source boundary for v13 `prop:takabayasi`: a global quotient-valued
inverse is distinct from a global continuous choice of one representative.
The explicit density-one regular-spinor loop has matrix coordinates
`diag(exp(2*pi*i*t),1)`. Its continuous polar lift starts at one datum and
ends at its simultaneous negative. Connected uniqueness for the actual
proved covering forces every continuous lift to have the same sign change.

Consequently no global continuous section of actual realization exists,
nor of the natural sign projection or literal source realization. In
particular the explicitly reconstructed principal datum is not globally
continuous. These statements preserve the globally continuous quotient
inverse proved earlier and do not negate the source quotient formulation.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology Set
namespace FoliationQM.PolarNoGlobalSection
open PolarSignQuotient PolarDatumTopology SpinorMatrix

/-- The actual complex half-turn exponential used in the representative loop. -/
def halfTurn (t : ℝ) : ℂ := Complex.exp ((Real.pi * t : ℝ) * Complex.I)
/-- The explicit half-turn amplitude never vanishes. -/
theorem halfTurn_ne_zero (t : ℝ) : halfTurn t ≠ 0 := Complex.exp_ne_zero _
/-- The half-turn amplitude starts at one. -/
theorem halfTurn_zero : halfTurn 0 = 1 := by simp [halfTurn]
/-- The half-turn amplitude ends at negative one. -/
theorem halfTurn_one : halfTurn 1 = -1 := by simp [halfTurn,Complex.exp_pi_mul_I]
/-- The opposite half-turn also ends at negative one. -/
theorem halfTurn_neg_one : halfTurn (-1) = -1 := by
  simp [halfTurn,Complex.exp_neg,Complex.exp_pi_mul_I]
/-- Opposite half-turn factors multiply to one, giving actual determinant-one matrices. -/
theorem halfTurn_mul_neg (t : ℝ) : halfTurn t * halfTurn (-t) = 1 := by
  rw [halfTurn,halfTurn,← Complex.exp_add]
  have he : ((Real.pi * t : ℝ) : ℂ) * Complex.I +
      ((Real.pi * -t : ℝ) : ℂ) * Complex.I = 0 := by push_cast; ring
  rw [he,Complex.exp_zero]
/-- The explicit half-turn amplitude has unit norm at every real parameter. -/
theorem norm_halfTurn (t : ℝ) : ‖halfTurn t‖ = 1 := by
  simp [halfTurn,Complex.norm_exp]
/-- Squaring the half-turn amplitude is the actual full-turn complex exponential. -/
theorem halfTurn_sq (t : ℝ) : (halfTurn t)^2 =
    Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  simp only [halfTurn,pow_two,← Complex.exp_add]
  congr 1
  push_cast
  ring
/-- The explicit half-turn amplitude is continuous on the real parameter line. -/
theorem continuous_halfTurn : Continuous halfTurn := by unfold halfTurn; fun_prop

/-- The actual diagonal determinant-one matrix paired with the half-turn amplitude. -/
def liftMatrix (t : ℝ) : Mat2 := !![halfTurn t,0;0,halfTurn (-t)]
/-- The matrix along the explicit polar lift has determinant one at every parameter. -/
theorem det_liftMatrix (t : ℝ) : (liftMatrix t).det = 1 := by
  simpa [liftMatrix,Matrix.det_fin_two] using halfTurn_mul_neg t
/-- The actual determinant-one matrix path is continuous in the natural matrix topology. -/
theorem continuous_liftMatrix : Continuous liftMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_halfTurn | exact continuous_const |
    exact continuous_halfTurn.comp continuous_neg

/-- The explicit nonzero-amplitude and determinant-one datum path. -/
def liftedLoop (t : ℝ) : Datum :=
  ⟨halfTurn t,liftMatrix t,halfTurn_ne_zero t,det_liftMatrix t⟩
/-- The explicit datum path is continuous in the independently defined natural topology. -/
theorem continuous_liftedLoop : Continuous liftedLoop :=
  PolarDatumTopology.continuous_iff.mpr ⟨continuous_halfTurn,continuous_liftMatrix⟩
/-- The actual datum path ends at the simultaneous negative of its initial representative. -/
theorem liftedLoop_one : liftedLoop 1 = negDatum (liftedLoop 0) := by
  apply datum_ext
  · simp [liftedLoop,negDatum,halfTurn_zero,halfTurn_one]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftedLoop,negDatum,liftMatrix,halfTurn_zero,halfTurn_one,halfTurn_neg_one]
/-- The actual regular-spinor realization of the explicit datum path. -/
def regularLoop (t : ℝ) : RegularSpinor := realize (liftedLoop t)
/-- The actual realized regular-spinor path is continuous. -/
theorem continuous_regularLoop : Continuous regularLoop :=
  PolarDatumTopology.continuous_realize.comp continuous_liftedLoop
/-- The realized spinor path is closed because its lifted endpoints differ by the simultaneous sign. -/
theorem regularLoop_one : regularLoop 1 = regularLoop 0 := by
  unfold regularLoop
  rw [liftedLoop_one]
  exact (realize_eq_iff_related _ _).mpr (Or.inr rfl)
/-- Every point of the explicit regular-spinor loop has actual invariant density one. -/
theorem density_regularLoop (t : ℝ) :
    SpinorRegularity.invariantDensity (regularLoop t).val = 1 := by
  change SpinorRegularity.invariantDensity
    (PolarMatrixFibers.parameterSpinor (halfTurn t) (liftMatrix t)) = 1
  rw [PolarMatrixFibers.density_parameterSpinor _ _ (det_liftMatrix t),norm_halfTurn]
  norm_num
/-- The actual encoded spinor loop is diagonal with squared half-turn phase and unit second entry. -/
theorem matrix_regularLoop (t : ℝ) :
    toMatrix (regularLoop t).val = !![(halfTurn t)^2,0;0,1] := by
  change toMatrix (PolarMatrixFibers.parameterSpinor (halfTurn t) (liftMatrix t)) = _
  rw [PolarMatrixFibers.toMatrix_parameterSpinor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,Matrix.smul_apply,smul_eq_mul,pow_two,halfTurn_mul_neg]
/-- The actual encoded spinor loop is exactly the full complex exponential in one diagonal entry. -/
theorem matrix_regularLoop_exponential (t : ℝ) :
    toMatrix (regularLoop t).val =
      !![Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I),0;0,1] := by
  rw [matrix_regularLoop,halfTurn_sq]
/-- The actual two-sheet polar realization admits no global continuous right inverse, as witnessed by the explicit closed loop and connected lift uniqueness. -/
theorem no_continuous_section :
    ¬ ∃ s : RegularSpinor → Datum, Continuous s ∧ Function.RightInverse s realize := by
  have hcover := PolarSignCovering.realize_isCoveringMap
  rintro ⟨s,hs,hsection⟩
  have hc : Continuous (fun t => s (regularLoop t)) := hs.comp continuous_regularLoop
  have hclose : s (regularLoop 1) = s (regularLoop 0) := congrArg s regularLoop_one
  have hstart : realize (s (regularLoop 0)) = realize (liftedLoop 0) := hsection _
  rcases (realize_eq_iff_related _ _).mp hstart with h | h
  · have heq := hcover.eq_of_comp_eq hc continuous_liftedLoop
      (funext fun t => hsection (regularLoop t)) (0:ℝ) h
    apply negDatum_ne_self (liftedLoop 0)
    calc negDatum (liftedLoop 0) = liftedLoop 1 := liftedLoop_one.symm
      _ = s (regularLoop 1) := (congrFun heq 1).symm
      _ = s (regularLoop 0) := hclose
      _ = liftedLoop 0 := congrFun heq 0
  · have heq := hcover.eq_of_comp_eq hc
      (continuous_negDatum.comp continuous_liftedLoop)
      (funext fun t => (hsection (regularLoop t)).trans
        ((realize_eq_iff_related _ _).mpr (Or.inr rfl)).symm) (0:ℝ) h
    have hend : negDatum (liftedLoop 1) = negDatum (liftedLoop 0) :=
      (congrFun heq 1).symm.trans (hclose.trans (congrFun heq 0))
    rw [liftedLoop_one,negDatum_involutive] at hend
    exact negDatum_ne_self (liftedLoop 0) hend.symm
/-- The explicit principal reconstructed datum is not globally continuous on the entire strict regular-spinor domain. -/
theorem not_continuous_inverseDatum : ¬ Continuous inverseDatum := by
  intro h
  exact no_continuous_section ⟨inverseDatum,h,realize_inverseDatum⟩
/-- The natural simultaneous-sign quotient projection has no global continuous representative section. -/
theorem no_continuous_quotient_section :
    ¬ ∃ s : PolarQuotient → Datum, Continuous s ∧
      Function.RightInverse s (Quotient.mk signSetoid) := by
  rintro ⟨s,hs,hsection⟩
  apply no_continuous_section
  refine ⟨fun q => s (ofRegular q), hs.comp RegularPolarHomeomorph.continuous_ofRegular, ?_⟩
  intro q
  have h := congrArg toRegular (hsection (ofRegular q))
  simpa only [toRegular_mk,toRegular_ofRegular] using h
/-- The literal positive-density, four-pi-angle and determinant-one source realization has no global continuous individual-representative section. -/
theorem no_continuous_source_section :
    ¬ ∃ s : RegularSpinor → SourcePolarDatum.SourceDatum, Continuous s ∧
      Function.RightInverse s SourcePolarRealization.realizeSource := by
  rintro ⟨s,hs,hsection⟩
  exact no_continuous_section ⟨fun q => SourcePolarDatum.toDatum (s q),
    SourcePolarDatum.continuous_toDatum.comp hs,hsection⟩
end FoliationQM.PolarNoGlobalSection
