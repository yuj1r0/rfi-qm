module

public import FoliationQM.DressedMassField
public import FoliationQM.HamiltonJacobiPullback
public import FoliationQM.SpinConnectionForms
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The closed phase clock and the dressed proper-time form

For v13 `eq:clock_vs_proper_oneform`, a real phase gives the exact phase
clock. On the timelike domain the normalized velocity defines the dressed
proper-time form. Its exterior derivative involves the true gradient of
the positive mass computed from the phase, with the sign −d log M ∧ β.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DressedClockForms

open DressedMassDensityVariation SpinConnectionForms

/-- The actual effective mass of the phase covector in the physical coordinates. -/
def mass (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : ℝ :=
  effectiveMass p.c (phaseDifferential S x)

/-- The exact phase-clock form −dS/(mc²). -/
def clockForm (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  HamiltonJacobiPullback.clockForm S p.m p.c x

/-- Scalar coefficient of the phase differential in the proper-time form. -/
def weight (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : ℝ :=
  -(p.c ^ 2)⁻¹ * (mass p S x)⁻¹

/-- The proper-time covector −dS/(M c²), regarded as a real linear functional. -/
def properLinear (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : Covector →L[ℝ] ℝ :=
  weight p S x • fderiv ℝ S x

/-- The physical proper-time covector regarded as a genuine differential one-form. -/
def properForm (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  oneFormLift (properLinear p S x)

/-- The effective mass is C¹ at each timelike C² phase point. -/
theorem contDiffAt_mass (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    ContDiffAt ℝ 1 (mass p S) x := by
  have hg (μ : Fin 4) : ContDiffAt ℝ 1 (fun y => phaseDifferential S y μ) x :=
    (hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have sq (μ : Fin 4) := (hg μ).mul (hg μ)
  have h := (((sq 0).sub (sq 1)).sub (sq 2)).sub (sq 3)
  exact (h.sqrt ht.ne').div_const _

/-- The source phase clock is closed at every C² point, without a timelike assumption. -/
theorem extDeriv_clock_eq_zero (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : extDeriv (clockForm p S) x = 0 := by
  change extDeriv ((-(p.m * p.c^2)⁻¹) • HamiltonJacobiPullback.phaseDifferential S) x = 0
  rw [extDeriv_smul, HamiltonJacobiPullback.extDeriv_phaseDifferential_zero hS, smul_zero]

/-- The proper one-form evaluated on a vector is the corresponding actual phase derivative divided by −Mc². -/
theorem properForm_apply (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) (v : Fin 1 → Covector) :
    properForm p S x v = -(fderiv ℝ S x (v 0)) / (mass p S x * p.c^2) := by
  change (weight p S x) * (fderiv ℝ S x (v 0)) = _
  simp only [weight, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Each coordinate component of the proper form is the lower normalized velocity component divided by c². -/
theorem properForm_component (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) (μ : Fin 4) :
    properForm p S x ![Madelung.coordinateVector μ] =
      velocityCovector p.c (phaseDifferential S x) μ / p.c^2 := by
  rw [properForm_apply]
  change -fderiv ℝ S x (Madelung.coordinateVector μ) / (_ * _) =
    (-fderiv ℝ S x (Madelung.coordinateVector μ) / mass p S x) / _
  rw [div_div]

/-- The alternating form equals the Minkowski proper-time form of the raised physical velocity. -/
theorem proper_eq_properTimeForm (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    properForm p S x = HamiltonJacobiPullback.properTimeForm p.c
      (ContactReeb.sharp (velocityCovector p.c (phaseDifferential S x))) := by
  have hm : 0 < mass p S x := effectiveMass_pos p.c_pos ht
  calc
    properForm p S x = HamiltonJacobiPullback.clockForm S (mass p S x) p.c x := by
      ext v
      rw [properForm_apply, HamiltonJacobiPullback.clockForm_apply]
    _ = _ := by
      apply HamiltonJacobiPullback.clockForm_eq_properTimeForm hm
      rw [ContactReeb.sharp_sharp]
      funext μ
      change -(fderiv ℝ S x (Madelung.coordinateVector μ)) =
        mass p S x * (-(fderiv ℝ S x (Madelung.coordinateVector μ)) / mass p S x)
      field_simp [hm.ne']

/-- On the timelike domain the phase clock equals (M/m) times the physical proper-time form. -/
theorem clock_eq_mass_smul_proper (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    clockForm p S x = (mass p S x / p.m) • properForm p S x := by
  have hm : mass p S x ≠ 0 := (effectiveMass_pos p.c_pos ht).ne'
  ext v
  rw [clockForm, HamiltonJacobiPullback.clockForm_apply, ContinuousAlternatingMap.smul_apply, properForm_apply]
  simp only [smul_eq_mul]
  field_simp [hm, p.m_pos.ne', p.c_pos.ne']

private theorem linearForm_apply (L : Covector →L[ℝ] ℝ) (v : Fin 1 → Covector) :
    oneFormLift L v = L (v 0) := rfl

private theorem weighted_phase_exterior {S g : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (hg : DifferentiableAt ℝ g x) :
    extDeriv (fun y => oneFormLift (g y • fderiv ℝ S y)) x =
      scalarWedge (fderiv ℝ g x) (fderiv ℝ S x) := by
  have hD := (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hd : DifferentiableAt ℝ (fun y => oneFormLift (g y • fderiv ℝ S y)) x :=
    oneFormLift.differentiableAt.comp x (hg.smul hD)
  have ev (w a : Covector) : fderiv ℝ (fun y => g y * fderiv ℝ S y w) x a =
      fderiv ℝ g x a * fderiv ℝ S x w + g x * (fderiv ℝ (fderiv ℝ S) x a) w := by
    have he := hg.hasFDerivAt.fun_mul (hD.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
    rw [he.fderiv]
    simp [mul_comm, add_comm]
  ext v
  rw [extDeriv_apply hd, scalarWedge_apply]
  simp only [linearForm_apply, smul_apply, smul_eq_mul, ev]
  simp [Fin.sum_univ_succ, Fin.removeNth, sub_eq_add_neg]
  rw [hS.isSymmSndFDerivAt (by norm_num) (v 0) (v 1)]
  ring

/-- The physical proper-time form has exterior derivative −d log M ∧ β at each timelike C² point. -/
theorem extDeriv_proper_eq (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    extDeriv (properForm p S) x =
      -scalarWedge (fderiv ℝ (fun y => Real.log (mass p S y)) x) (properLinear p S x) := by
  have hm := (contDiffAt_mass p hS ht).differentiableAt_one
  have hp : mass p S x ≠ 0 := (effectiveMass_pos p.c_pos ht).ne'
  have hinv := (hasDerivAt_inv hp).comp_hasFDerivAt x hm.hasFDerivAt
  have hw := hinv.const_mul (-(p.c^2)⁻¹)
  change HasFDerivAt (weight p S) _ x at hw
  rw [show properForm p S = fun y => oneFormLift (weight p S y • fderiv ℝ S y) from rfl,
    weighted_phase_exterior hS hw.differentiableAt, hw.fderiv, (hm.hasFDerivAt.log hp).fderiv]
  ext v
  simp only [ContinuousAlternatingMap.neg_apply, scalarWedge_apply, properLinear, weight,
    smul_apply, smul_eq_mul]
  ring

end FoliationQM.DressedClockForms
