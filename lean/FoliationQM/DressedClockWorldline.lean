module

public import FoliationQM.DressedMassField
public import FoliationQM.HamiltonJacobiPullback
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Dressed phase rate along physical worldlines

In v13 `eq:clock_vs_proper_oneform`, x⁰ = ct, the physical trajectory is
tangent to the raised velocity, and its parameter is proper time. The
frequency calculation uses the local real phase and the actual chain rule.
A C² phase constructs such a trajectory near every future-timelike point.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace FoliationQM.DressedClockWorldline
open DressedMassDensityVariation ContactReeb

/-- The physical velocity vector obtained by raising the lowered normalized phase momentum. -/
def velocity (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : Covector :=
  sharp (velocityCovector p.c (phaseDifferential S x))

/-- Raising the index preserves the normalized Minkowski square of the physical velocity. -/
theorem velocity_sq (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    minkowski (velocity p S x) (velocity p S x) = p.c^2 :=
  (minkowski_sharp _ _).trans (velocity_normalized p.c_pos ht)

/-- On the future branch the raised velocity has positive time component. -/
theorem velocity_time_pos (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : 0 < velocity p S x 0 := by
  change 0 < velocityCovector p.c (phaseDifferential S x) 0
  exact velocity_future p.c_pos ht hf

/-- Evaluation of the physical proper-time one-form on the raised velocity gives one. -/
theorem properTime_velocity (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    HamiltonJacobiPullback.properTimeForm p.c (velocity p S x) (fun _ => velocity p S x) = 1 :=
  HamiltonJacobiPullback.properTimeForm_velocity p.c_pos (velocity_sq p ht)

/-- The true differential of the action phase along its normalized raised velocity equals −Mc². -/
theorem differential_velocity (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    fderiv ℝ S x (velocity p S x) = -effectiveMass p.c (phaseDifferential S x) * p.c^2 := by
  have hm := (effectiveMass_pos p.c_pos ht).ne'
  have hp : HamiltonJacobiPullback.momentum S x =
      effectiveMass p.c (phaseDifferential S x) • velocityCovector p.c (phaseDifferential S x) := by
    ext i
    change -phaseDifferential S x i = effectiveMass p.c (phaseDifferential S x) *
      (-phaseDifferential S x i / effectiveMass p.c (phaseDifferential S x))
    field_simp [hm]
  have h := HamiltonJacobiPullback.momentum_pairing S x (velocity p S x)
  rw [hp, pairing_smul_left, velocity, pairing_sharp_right, velocity_normalized p.c_pos ht] at h
  unfold velocity
  linarith

/-- The dimensionless physical phase along an actual proper-time worldline has instantaneous
derivative −M c²/ℏ, with the dressed mass evaluated at the point of the curve. -/
theorem phase_rate (p : MassiveParameters) {S : Covector → ℝ} {γ : ℝ → Covector} {τ : ℝ}
    (hS : DifferentiableAt ℝ S (γ τ))
    (ht : 0 < minkowski (phaseDifferential S (γ τ)) (phaseDifferential S (γ τ)))
    (hγ : HasDerivAt γ (velocity p S (γ τ)) τ) :
    HasDerivAt (fun t => S (γ t) / p.hbar)
      (-effectiveMass p.c (phaseDifferential S (γ τ)) * p.c^2 / p.hbar) τ := by
  have hd := (hS.hasFDerivAt.comp_hasDerivAt τ hγ).div_const p.hbar
  rwa [differential_velocity p ht] at hd

private theorem differentiable_gradient {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) : ContDiffAt ℝ 1 (phaseDifferential S) x :=
  contDiffAt_pi.mpr fun i => (hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

private theorem differentiable_phase_square {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) :
    ContDiffAt ℝ 1 (fun y => minkowski (phaseDifferential S y) (phaseDifferential S y)) x := by
  have hc (i : Fin 4) := (contDiffAt_pi.mp (differentiable_gradient hS) i)
  exact ((((hc 0).mul (hc 0)).sub ((hc 1).mul (hc 1))).sub ((hc 2).mul (hc 2))).sub ((hc 3).mul (hc 3))

/-- Local C² regularity of the action phase makes its normalized raised velocity C¹ on the
timelike domain, the regularity required for a local physical flow. -/
theorem contDiffAt_velocity (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    ContDiffAt ℝ 1 (velocity p S) x := by
  have hm : ContDiffAt ℝ 1 (fun y => effectiveMass p.c (phaseDifferential S y)) x :=
    ((differentiable_phase_square hS).sqrt ht.ne').div_const p.c
  have hU (i : Fin 4) : ContDiffAt ℝ 1 (fun y => velocityCovector p.c (phaseDifferential S y) i) x :=
    (contDiffAt_pi.mp (differentiable_gradient hS) i).neg.div hm (effectiveMass_pos p.c_pos ht).ne'
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · simpa [velocity, sharp, hi] using hU i
  · simpa [velocity, sharp, hi] using (hU i).neg

/-- A future-timelike point of a C² phase has an actual local proper-time trajectory. Along
a neighborhood of its initial time the trajectory stays future normalized and its phase
satisfies the dressed frequency law. -/
theorem exists_worldline (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    ∃ γ : ℝ → Covector, γ 0 = x ∧ ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt γ (velocity p S (γ τ)) τ ∧
      minkowski (velocity p S (γ τ)) (velocity p S (γ τ)) = p.c^2 ∧ 0 < velocity p S (γ τ) 0 ∧
      HasDerivAt (fun t => S (γ t) / p.hbar)
        (-effectiveMass p.c (phaseDifferential S (γ τ)) * p.c^2 / p.hbar) τ := by
  obtain ⟨γ, hzero, ε, hε, hcurve⟩ :=
    (contDiffAt_velocity p hS ht).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hnear : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt γ (velocity p S (γ τ)) τ := by
    filter_upwards [Ioo_mem_nhds (show 0 - ε < 0 by linarith) (show 0 < 0 + ε by linarith)] with τ hτ
    exact hcurve τ hτ
  have hγx : Tendsto γ (𝓝 0) (𝓝 x) := hzero ▸ hnear.self_of_nhds.continuousAt
  have htim := (differentiable_phase_square hS).continuousAt.eventually (Ioi_mem_nhds ht)
  have hfut := (contDiffAt_pi.mp (differentiable_gradient hS) 0).continuousAt.eventually (Iio_mem_nhds hf)
  refine ⟨γ, hzero, ?_⟩
  filter_upwards [hnear, hγx.eventually (hS.eventually (by norm_num)), hγx.eventually htim,
    hγx.eventually hfut] with τ hγ hSt ht' hf'
  exact ⟨hγ, velocity_sq p ht', velocity_time_pos p ht' hf',
    phase_rate p (hSt.differentiableAt (by norm_num)) ht' hγ⟩

end FoliationQM.DressedClockWorldline
