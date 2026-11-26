module

public import FoliationQM.ClockScales
public import FoliationQM.PhaseCircle

/-!
# The adopted action-circle compactification and its proper period

Sources: v13 `thm:contact_period` (ii), `eq:phase_Phi`, and its proof paragraph
beginning with the periodic proper-clock postulate. The action quotient by
2πℏ is an explicitly adopted compactification, not a consequence of contact
geometry, a return of a spacetime trajectory, or a proved symplectic-capacity
statement. No capacity or non-squeezing premise is introduced here.

Starting from that actual quotient, continuous circle equivalences implement
S = -mc²τ and phase = S/ℏ. The quotient kernel determines every real period
of the pulled-back action readout and of the actual unit-circle phase; their
least positive period is the derived value 2πℏ/(mc²). The image of a positive
proper-time generator has actual fundamental-group winding number -1.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ActionClockCircle

/-- The action circle stipulated by the periodic proper-clock postulate: ℝ/(2πℏℤ). -/
abbrev ActionCircle (p : MassiveParameters) := AddCircle (2 * Real.pi * p.hbar)
/-- The actual proper-time quotient using the period derived from the action quantum and rest energy. -/
abbrev ProperClockCircle (p : MassiveParameters) := AddCircle p.period

/-- The supplied positive Planck scale makes the adopted action period positive. -/
instance actionPeriod_positive (p : MassiveParameters) : Fact (0 < 2 * Real.pi * p.hbar) :=
  ⟨mul_pos Real.two_pi_pos p.hbar_pos⟩
/-- The derived proper period is positive, enabling the actual circle winding-number API. -/
instance properPeriod_positive (p : MassiveParameters) : Fact (0 < p.period) :=
  ⟨ClockScales.period_pos p⟩

/-- The continuous circle equivalence descending S = -mc²τ, with negative orientation. -/
def properToAction (p : MassiveParameters) : ProperClockCircle p ≃ₜ ActionCircle p :=
  (AddCircle.homeomorphAddCircle p.period (2 * Real.pi * p.hbar)
    (ClockScales.period_pos p).ne' (mul_pos Real.two_pi_pos p.hbar_pos).ne').trans
      (Homeomorph.neg (ActionCircle p))

/-- The quotient equivalence agrees with the actual negative action/proper-time linear conversion. -/
theorem properToAction_coe (p : MassiveParameters) (τ : ℝ) :
    properToAction p (τ : ProperClockCircle p) = (-p.m * p.c ^ 2 * τ : ℝ) := by
  change (-(τ * (p.period⁻¹ * (2 * Real.pi * p.hbar))) : ℝ) =
    (-p.m * p.c ^ 2 * τ : ActionCircle p)
  congr 1
  unfold MassiveParameters.period
  field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne', Real.pi_ne_zero]

/-- The continuous equivalence from the adopted action circle to angles modulo 2π. -/
def actionToPhase (p : MassiveParameters) : ActionCircle p ≃ₜ AddCircle (2 * Real.pi) :=
  AddCircle.homeomorphAddCircle (2 * Real.pi * p.hbar) (2 * Real.pi)
    (mul_pos Real.two_pi_pos p.hbar_pos).ne' Real.two_pi_pos.ne'

/-- The quotient phase map is S/ℏ modulo 2π, as in v13 `eq:phase_Phi`. -/
theorem actionToPhase_coe (p : MassiveParameters) (S : ℝ) :
    actionToPhase p (S : ActionCircle p) = (S / p.hbar : ℝ) := by
  change (S * ((2 * Real.pi * p.hbar)⁻¹ * (2 * Real.pi)) : ℝ) =
    (S / p.hbar : AddCircle (2 * Real.pi))
  congr 1
  field_simp [p.hbar_pos.ne', Real.pi_ne_zero]

/-- The actual proper-clock-to-phase circle equivalence, obtained through the adopted action quotient. -/
def properToPhase (p : MassiveParameters) : ProperClockCircle p ≃ₜ AddCircle (2 * Real.pi) :=
  (properToAction p).trans (actionToPhase p)

/-- The proper-time phase is -ω₀τ modulo 2π, derived from S = -mc²τ and phase = S/ℏ. -/
theorem properToPhase_coe (p : MassiveParameters) (τ : ℝ) :
    properToPhase p (τ : ProperClockCircle p) = (-p.omega0 * τ : ℝ) := by
  change actionToPhase p (properToAction p (τ : ProperClockCircle p)) = _
  rw [properToAction_coe, actionToPhase_coe]
  congr 1
  unfold MassiveParameters.omega0
  ring

/-- The action/proper-time circle equivalence preserves the chosen origin. -/
theorem properToAction_zero (p : MassiveParameters) : properToAction p 0 = 0 := by
  simpa using properToAction_coe p 0

/-- The action-to-phase circle equivalence preserves the chosen origin. -/
theorem actionToPhase_zero (p : MassiveParameters) : actionToPhase p 0 = 0 := by
  simpa using actionToPhase_coe p 0

/-- The proper-clock-to-phase circle equivalence preserves the chosen origin. -/
theorem properToPhase_zero (p : MassiveParameters) : properToPhase p 0 = 0 := by
  simpa using properToPhase_coe p 0

/-- The action readout returns to the origin exactly at integer multiples of the derived proper period. -/
theorem properToAction_coe_eq_zero_iff (p : MassiveParameters) (τ : ℝ) :
    properToAction p (τ : ProperClockCircle p) = 0 ↔ ∃ n : ℤ, τ = n * p.period := by
  rw [← properToAction_zero p, (properToAction p).injective.eq_iff,
    AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, eq_comm]

/-- All real periods of the compactified action readout are integer multiples of the derived proper period. -/
theorem properToAction_periodic_iff (p : MassiveParameters) (T : ℝ) :
    Function.Periodic (fun τ : ℝ => properToAction p (τ : ProperClockCircle p)) T ↔
      ∃ n : ℤ, T = n * p.period := by
  rw [← properToAction_coe_eq_zero_iff]
  constructor
  · intro h
    simpa [properToAction_zero] using h.eq
  · intro h τ
    apply congrArg (properToAction p)
    have hT : (T : ProperClockCircle p) = 0 :=
      (properToAction p).injective (h.trans (properToAction_zero p).symm)
    simp only [AddCircle.coe_add, hT, add_zero]

/-- The derived proper period is an actual period of the compactified action readout. -/
theorem properToAction_periodic (p : MassiveParameters) :
    Function.Periodic (fun τ : ℝ => properToAction p (τ : ProperClockCircle p)) p.period := by
  exact (properToAction_periodic_iff p p.period).2 ⟨1, by simp⟩

/-- The derived proper period is the least positive period of the actual compactified action readout. -/
theorem properToAction_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0 < T ∧
      Function.Periodic (fun τ : ℝ => properToAction p (τ : ProperClockCircle p)) T} p.period := by
  refine ⟨⟨ClockScales.period_pos p, properToAction_periodic p⟩, ?_⟩
  rintro T ⟨hT, hperiodic⟩
  obtain ⟨n, rfl⟩ := (properToAction_periodic_iff p T).1 hperiodic
  have hnpos : (0 : ℝ) < n := by nlinarith [ClockScales.period_pos p]
  have hn : (1 : ℤ) ≤ n := Int.add_one_le_iff.mpr (Int.cast_pos.mp hnpos)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa using mul_le_mul_of_nonneg_right hnreal (ClockScales.period_pos p).le

/-- The phase quotient returns to zero exactly at integer multiples of the derived proper period. -/
theorem properToPhase_coe_eq_zero_iff (p : MassiveParameters) (τ : ℝ) :
    properToPhase p (τ : ProperClockCircle p) = 0 ↔ ∃ n : ℤ, τ = n * p.period := by
  rw [← properToPhase_zero p, (properToPhase p).injective.eq_iff,
    AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, eq_comm]

/-- All real periods of the actual quotient phase are integer multiples of the derived proper period. -/
theorem properToPhase_periodic_iff (p : MassiveParameters) (T : ℝ) :
    Function.Periodic (fun τ : ℝ => properToPhase p (τ : ProperClockCircle p)) T ↔
      ∃ n : ℤ, T = n * p.period := by
  rw [← properToAction_periodic_iff]
  constructor
  · intro h τ
    exact (actionToPhase p).injective (h τ)
  · intro h τ
    exact congrArg (actionToPhase p) (h τ)

/-- The derived proper period is the least positive period of the quotient phase. -/
theorem properToPhase_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0 < T ∧
      Function.Periodic (fun τ : ℝ => properToPhase p (τ : ProperClockCircle p)) T} p.period := by
  simpa only [properToPhase_periodic_iff, ← properToAction_periodic_iff] using
    properToAction_least_positive_period p

/-- The image in the action circle of one positive proper-time generator loop. -/
def imageProperGenerator (p : MassiveParameters) : Path (0 : ActionCircle p) 0 :=
  ((AddCircle.zsmulLoop p.period 0 1).map (properToAction p).continuous).cast
    (properToAction_zero p).symm (properToAction_zero p).symm

/-- The image generator is the actual negative generator loop in the action circle. -/
theorem imageProperGenerator_eq (p : MassiveParameters) :
    imageProperGenerator p = AddCircle.zsmulLoop (2 * Real.pi * p.hbar) 0 (-1) := by
  ext t
  change properToAction p (AddCircle.zsmulLoop p.period 0 1 t) = _
  simp only [AddCircle.zsmulLoop, Path.coe_mk_mk, AddCircle.coe_zero, one_zsmul, add_zero, properToAction_coe]
  change ((-p.m * p.c ^ 2 * (t.val * p.period) : ℝ) : ActionCircle p) =
    (-1 : ℤ) • (t.val * (2 * Real.pi * p.hbar) : ℝ)
  rw [neg_one_zsmul]
  congr 1
  unfold MassiveParameters.period
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- The induced image of the positive generator has actual fundamental-group winding number -1. -/
theorem windingNumber_imageProperGenerator (p : MassiveParameters) :
    AddCircle.windingNumber (.of (.mk (imageProperGenerator p))) = -1 := by
  rw [imageProperGenerator_eq]
  exact AddCircle.windingNumber_zsmulLoop 0 (-1)

/-- The inverse circle equivalence agrees with τ = -S/(mc²). -/
theorem properToAction_symm_coe (p : MassiveParameters) (S : ℝ) :
    (properToAction p).symm (S : ActionCircle p) = (-S / (p.m * p.c ^ 2) : ℝ) := by
  apply (properToAction p).injective
  rw [(properToAction p).apply_symm_apply, properToAction_coe]
  congr 1
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- For the real proper-time lift, the adopted action quotient has exactly the derived integer-period kernel. -/
theorem action_readout_kernel (p : MassiveParameters) (τ : ℝ) :
    ((-p.m * p.c ^ 2 * τ : ℝ) : ActionCircle p) = 0 ↔
      ∃ n : ℤ, τ = n * p.period := by
  simpa only [properToAction_coe] using properToAction_coe_eq_zero_iff p τ

/-- The real lift τ ↦ [-mc²τ] has precisely the integer multiples of 2πℏ/(mc²) as periods. -/
theorem action_readout_periodic_iff (p : MassiveParameters) (T : ℝ) :
    Function.Periodic (fun τ : ℝ => ((-p.m * p.c ^ 2 * τ : ℝ) : ActionCircle p)) T ↔
      ∃ n : ℤ, T = n * p.period := by
  simpa only [properToAction_coe] using properToAction_periodic_iff p T

/-- The real lifted action readout has least positive period 2πℏ/(mc²), derived from the quotient kernel. -/
theorem action_readout_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0 < T ∧
      Function.Periodic (fun τ : ℝ => ((-p.m * p.c ^ 2 * τ : ℝ) : ActionCircle p)) T} p.period := by
  simpa only [properToAction_coe] using properToAction_least_positive_period p

/-- The actual continuous identification of the adopted action quotient with U(1). -/
def actionToUnitCircle (p : MassiveParameters) : ActionCircle p ≃ₜ Circle :=
  (actionToPhase p).trans AddCircle.homeomorphCircle'

/-- The proper-clock circle mapped continuously and bijectively to the actual unit circle. -/
def properToUnitCircle (p : MassiveParameters) : ProperClockCircle p ≃ₜ Circle :=
  (properToPhase p).trans AddCircle.homeomorphCircle'

/-- On real action lifts, the actual unit-circle phase is exp(iS/ℏ). -/
theorem actionToUnitCircle_coe (p : MassiveParameters) (S : ℝ) :
    actionToUnitCircle p (S : ActionCircle p) = Circle.exp (S / p.hbar) := by
  change AddCircle.homeomorphCircle' (actionToPhase p (S : ActionCircle p)) = _
  rw [actionToPhase_coe, AddCircle.homeomorphCircle'_apply_mk]

/-- On real proper-time lifts, the actual unit-circle phase is exp(-iω₀τ). -/
theorem properToUnitCircle_coe (p : MassiveParameters) (τ : ℝ) :
    properToUnitCircle p (τ : ProperClockCircle p) = Circle.exp (-p.omega0 * τ) := by
  change AddCircle.homeomorphCircle' (properToPhase p (τ : ProperClockCircle p)) = _
  rw [properToPhase_coe, AddCircle.homeomorphCircle'_apply_mk]

/-- All real periods of the actual unit-circle phase exp(-iω₀τ) are integer multiples of the derived proper period. -/
theorem unit_phase_periodic_iff (p : MassiveParameters) (T : ℝ) :
    Function.Periodic (fun τ : ℝ => Circle.exp (-p.omega0 * τ)) T ↔
      ∃ n : ℤ, T = n * p.period := by
  have hiff : Function.Periodic
      (fun τ : ℝ => properToUnitCircle p (τ : ProperClockCircle p)) T ↔
      Function.Periodic (fun τ : ℝ => properToPhase p (τ : ProperClockCircle p)) T := by
    constructor
    · intro h τ
      exact AddCircle.homeomorphCircle'.injective (h τ)
    · intro h τ
      exact congrArg AddCircle.homeomorphCircle' (h τ)
  simpa only [properToUnitCircle_coe, properToPhase_periodic_iff] using hiff

/-- The actual unit-circle phase exp(-iω₀τ) has least positive period 2πℏ/(mc²). -/
theorem unit_phase_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0 < T ∧
      Function.Periodic (fun τ : ℝ => Circle.exp (-p.omega0 * τ)) T} p.period := by
  simpa only [unit_phase_periodic_iff, ← properToAction_periodic_iff] using
    properToAction_least_positive_period p

end FoliationQM.ActionClockCircle
