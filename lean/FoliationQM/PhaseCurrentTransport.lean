module

public import FoliationQM.LogDensityTransport
public import FoliationQM.ObserverFluxDensity

/-!
# Local transport balance of the physical phase current

In v13 lines 811–817 the replacement of the lower spatial momentum by the
laboratory drift is valid near every event with nonzero normal momentum.
The residual below uses actual Fréchet derivatives and the physical time
coordinate x⁰=ct.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace FoliationQM.PhaseCurrentTransport

open DressedMassDensityVariation ObserverFluxDensity Madelung PolarSecondDifferential PolarRegularity

/-- A C² phase supplies a differentiable normal momentum in laboratory coordinates. -/
theorem differentiableAt_normalMomentum {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : DifferentiableAt ℝ (normalMomentum S) x :=
  (differentiableAt_directionalDerivative_of_contDiffAt_two hS (coordinateVector 0)).neg

/-- The full three-component phase drift is differentiable where the normal momentum is nonzero. -/
theorem differentiableAt_phaseDrift (c : ℝ) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (ha : normalMomentum S x ≠ 0) :
    DifferentiableAt ℝ (phaseDrift c S) x := by
  have hd (i : Fin 4) : ContDiffAt ℝ 1 (fun y => phaseDifferential S y i) x :=
    (hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  apply differentiableAt_pi.mpr
  intro i
  exact ((contDiffAt_const.mul (hd i.succ)).div (hd 0).neg ha).differentiableAt_one

/-- The laboratory conservative residual for ρa and ρav equals −c times the (+---)
divergence of ρ dS. Nonzero normal momentum allows cancellation on a neighborhood. -/
theorem phase_balance (c : ℝ) {ρ S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (ha : normalMomentum S x ≠ 0) :
    LogDensityTransport.balance c ρ (normalMomentum S) (phaseDrift c S) x =
      -c * densityCurrentDivergence ρ S coordinateVector x := by
  let J := densityCurrent ρ S coordinateVector
  have time : (fun y => ρ y * normalMomentum S y) = fun y => -J 0 y := by
    funext y
    exact mul_neg _ _
  have spatial (i : Fin 3) :
      phaseDifferential (fun y => ρ y * normalMomentum S y * phaseDrift c S y i) x i.succ =
      c * directionalDerivative (J i.succ) (coordinateVector i.succ) x := by
    have he : (fun y => ρ y * normalMomentum S y * phaseDrift c S y i) =ᶠ[𝓝 x]
        (c • J i.succ) := by
      filter_upwards [(differentiableAt_normalMomentum hS).continuousAt.eventually_ne ha] with y hy
      change ρ y * normalMomentum S y * (c * phaseDifferential S y i.succ / normalMomentum S y) =
        c * (ρ y * phaseDifferential S y i.succ)
      field_simp [hy]
    change fderiv ℝ _ x _ = c * fderiv ℝ (J i.succ) x _
    rw [he.fderiv_eq, fderiv_const_smul_field]
    rfl
  unfold LogDensityTransport.balance
  rw [time]
  simp only [spatial, Fin.sum_univ_three]
  change c * fderiv ℝ (fun y => -J 0 y) x (coordinateVector 0) + _ =
    -c * (directionalDerivative (J 0) (coordinateVector 0) x - _ - _ - _)
  rw [fderiv_fun_neg]
  let d := fun i => directionalDerivative (J i) (coordinateVector i) x
  change c * -d 0 + (c * d 1 + c * d 2 + c * d 3) = -c * (d 0 - d 1 - d 2 - d 3)
  ring

/-- For positive light speed the physical density-current equation is equivalent
to laboratory mass balance. -/
theorem phase_balance_eq_zero_iff {c : ℝ} {ρ S : Covector → ℝ} {x : Covector}
    (hc : 0 < c) (hS : ContDiffAt ℝ 2 S x) (ha : normalMomentum S x ≠ 0) :
    LogDensityTransport.balance c ρ (normalMomentum S) (phaseDrift c S) x = 0 ↔
      densityCurrentDivergence ρ S coordinateVector x = 0 := by
  rw [phase_balance c hS ha, mul_eq_zero]
  simp [hc.ne']

end FoliationQM.PhaseCurrentTransport
