module
public import FoliationQM.ScalarSectorDensity
public import FoliationQM.RelativePolarStationaryAction
public import FoliationQM.DiracRestField

/-!
# Phase reversal and the two orders of field equation

For v13 `thm:dirac_lift` and `thm:kahler`, simultaneous reversal of the
action phase and its tests preserves the scalar massive action. Its
reversed rest wave gives a smooth, regular quadratic stationary field
whose first-order positive-mass Dirac residual is nonzero.
-/

@[expose] public section
noncomputable section
open scoped ContDiff Topology
namespace FoliationQM.ScalarPhaseReversal
open ActionDensity PolarChartAction RelativePolarStationaryAction DiracMatrices DiracEquation

/-- Reversing the phase preserves its full signed quadratic contribution. -/
theorem hydroIntegrand_neg (p : MassiveParameters) (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) :
    hydroIntegrand p ρ (-S) e x = hydroIntegrand p ρ S e x := by
  simp only [hydroIntegrand, hydroDensity, fderiv_neg, neg_apply, minkowski, neg_mul, mul_neg, neg_neg]

/-- The full relative action is invariant when both phases are reversed. -/
theorem relative_neg (p : MassiveParameters) (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    relativeHydroAction p ρ (-S) ρ' (-S') e U = relativeHydroAction p ρ S ρ' S' e U := by
  simp only [relativeHydroAction, relativeHydroDensity, hydroIntegrand_neg]

/-- Every reversed compact phase test corresponds to an original compact test. -/
theorem stationary_neg (p : MassiveParameters) {ρ S : Covector → ℝ} {e : Fin 4 → Covector} {U : Set Covector}
    (h : RelativePolarStationaryOn p ρ S e U) : RelativePolarStationaryOn p ρ (-S) e U := by
  intro a b ha hb hca hcb hsa hsb
  have ht := h a (-b) ha hb.neg hca hcb.neg hsa (by simpa only [tsupport_neg] using hsb)
  have he (t : ℝ) : (fun x => (-S) x + t * b x) = -(fun x => S x + t * (-b) x) := by
    funext x
    simp [add_comm]
  simpa only [he, relative_neg] using ht

/-- Negation is an involution of stationary scalar phases. -/
theorem stationary_neg_iff (p : MassiveParameters) (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    RelativePolarStationaryOn p ρ (-S) e U ↔ RelativePolarStationaryOn p ρ S e U :=
  ⟨fun h => by simpa only [neg_neg] using stationary_neg p h, stationary_neg p⟩

/-- The phase-reversed rest solution is stationary on every open flat domain. -/
theorem reversed_rest_stationary (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U) :
    RelativePolarStationaryOn p (fun _ => 1) (-RestPlaneWave.restAction p) Madelung.coordinateVector U :=
  stationary_neg p (rest_relativePolarStationaryOn p hU)

/-- The reversed plane-rotor field is the exact same wave as the rest solution for the signed mass −m. -/
theorem reversed_field_eq (p : MassiveParameters) :
    ScalarSectorDensity.field p (fun _ => 1) (-RestPlaneWave.restAction p) = DiracRestField.field p.hbar p.c (-p.m) := by
  rw [ScalarSectorDensity.field_eq_lift]
  funext x
  unfold ScalarRestKinetic.lift ScalarRestKinetic.embed actionField PolarDifferential.polarField
  simp only [Pi.neg_apply, RestPlaneWave.restAction, Real.sqrt_one, Complex.ofReal_one, one_mul,
    DiracRestField.field, DiracRestField.wave]
  congr 2
  ring

/-- No nonzero field solves both mass signs at the same point when mc ≠ 0. -/
theorem opposite_mass_incompatible (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (hn : ψ x ≠ 0) (he : diracField p.hbar (-p.m) p.c ψ x = 0) :
    diracField p.hbar p.m p.c ψ x ≠ 0 := by
  intro hp
  change _ - (((-p.m * p.c : ℝ) : ℂ) • ψ x) = 0 at he
  change _ - (((p.m * p.c : ℝ) : ℂ) • ψ x) = 0 at hp
  have h := (sub_eq_zero.mp hp).symm.trans (sub_eq_zero.mp he)
  have hz := sub_eq_zero.mpr h
  rw [← sub_smul] at hz
  have hmc : (((p.m * p.c : ℝ) : ℂ) - ((-p.m * p.c : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show p.m * p.c - -p.m * p.c ≠ 0 by nlinarith [mul_pos p.m_pos p.c_pos])
  exact smul_ne_zero hmc hn hz

/-- The positive-mass Dirac residual of the regular reversed rest wave is nonzero everywhere. -/
theorem reversed_rest_not_dirac (p : MassiveParameters) (x : Covector) :
    diracField p.hbar p.m p.c (ScalarSectorDensity.field p (fun _ => 1) (-RestPlaneWave.restAction p)) x ≠ 0 := by
  rw [reversed_field_eq]
  exact opposite_mass_incompatible p (SpinorRegularity.regular_ne_zero (DiracRestField.regular p.hbar p.c (-p.m) x))
    (DiracRestField.diracField_zero p.hbar p.c (-p.m) p.hbar_pos.ne' x)

end FoliationQM.ScalarPhaseReversal
