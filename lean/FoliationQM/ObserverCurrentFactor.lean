module

public import FoliationQM.ObserverFluxDensity

/-!
# The observer factor from the physical phase and current

V13 Remark 5.2 and equation `eq:jacobian_density` identify the multiplier
of the invariant modulus density on a spacelike slice. For a future unit
normal it is the Lorentz factor of the dressed four-velocity times the
dressed-to-bare mass ratio. The normal differentiates the physical phase
in the spacetime coordinates (ct,x¹,x²,x³).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverCurrentFactor

open DressedMassDensityVariation ObserverFluxDensity

/-- The physical observer multiplier from the actual normal phase derivative. -/
def factor (p : MassiveParameters) (S : Covector → ℝ) (n x : Covector) : ℝ :=
  -(fderiv ℝ S x n) / (p.m * p.c)

/-- Contracting the current of the original polar wave with the observer normal
gives the normal-phase multiplier times its invariant density. -/
theorem flux_eq_factor (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (n : Covector) (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hp : 0 < ρ x) :
    ContactReeb.pairing n (ScalarPhaseCurrent.current p (ActionDensity.actionField p ρ S) x) /
      p.c = factor p S n x * ρ x := by
  have hj : ScalarPhaseCurrent.current p (ActionDensity.actionField p ρ S) x =
      (ρ x / p.m) • HamiltonJacobiPullback.momentum S x := by
    funext i
    rw [ScalarDressedCurrent.current_actionField p hρ hS hp]
    change -(ρ x / p.m) * phaseDifferential S x i = (ρ x / p.m) * (-phaseDifferential S x i)
    ring
  rw [hj, ContactReeb.pairing_smul_right, ContactReeb.pairing_comm n,
    HamiltonJacobiPullback.momentum_pairing, factor]
  ring

/-- The normal phase derivative divided by −mc is exactly the dressed mass
ratio times the relative velocity contraction. The algebra holds for every normal. -/
theorem factor_eq_mass_gamma (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (n : Covector) (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    factor p S n x = (effectiveMass p.c (phaseDifferential S x) / p.m) *
      (minkowski n (DressedClockWorldline.velocity p S x) / p.c) := by
  have hm := (effectiveMass_pos p.c_pos ht).ne'
  have hp : HamiltonJacobiPullback.momentum S x =
      effectiveMass p.c (phaseDifferential S x) • velocityCovector p.c (phaseDifferential S x) := by
    funext i
    change -phaseDifferential S x i = effectiveMass p.c (phaseDifferential S x) *
      (-phaseDifferential S x i / effectiveMass p.c (phaseDifferential S x))
    field_simp [hm]
  have hnu : ContactReeb.pairing (velocityCovector p.c (phaseDifferential S x)) n =
      minkowski n (DressedClockWorldline.velocity p S x) := by
    rw [ContactReeb.pairing_comm, ← ContactReeb.pairing_sharp_right,
      DressedClockWorldline.velocity, ContactReeb.sharp_sharp]
  rw [factor, ← HamiltonJacobiPullback.momentum_pairing, hp, ContactReeb.pairing_smul_left, hnu]
  ring

/-- A future unit normal sees a strictly positive observer multiplier on the
future timelike phase branch. -/
theorem factor_pos (p : MassiveParameters) {S : Covector → ℝ} {x n : Covector}
    (hn : minkowski n n = 1) (hnf : 0 < n 0)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : 0 < factor p S n x := by
  have hg := ObserverBoostFactor.normal_gamma_ge_one p.c_pos hn hnf
    (DressedClockWorldline.velocity_sq p ht) (DressedClockWorldline.velocity_time_pos p ht hf)
  rw [factor_eq_mass_gamma p n ht]
  exact mul_pos (div_pos (effectiveMass_pos p.c_pos ht) p.m_pos) (one_pos.trans_le hg)

/-- For a future unit normal, the multiplier equals the bare relative boost
precisely when the dressed mass equals the bare mass at the observation point. -/
theorem factor_eq_gamma_iff (p : MassiveParameters) {S : Covector → ℝ} {x n : Covector}
    (hn : minkowski n n = 1) (hnf : 0 < n 0)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    factor p S n x = minkowski n (DressedClockWorldline.velocity p S x) / p.c ↔
      effectiveMass p.c (phaseDifferential S x) = p.m := by
  have hg := ObserverBoostFactor.normal_gamma_ge_one p.c_pos hn hnf
    (DressedClockWorldline.velocity_sq p ht) (DressedClockWorldline.velocity_time_pos p ht hf)
  rw [factor_eq_mass_gamma p n ht, mul_eq_right₀ (one_pos.trans_le hg).ne',
    div_eq_one_iff_eq p.m_pos.ne']

/-- In laboratory coordinates the observer normal selects the existing laboratory
normal momentum, with the same bare-mass and light-speed denominator. -/
theorem labFactor_eq_normalMomentum (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) :
    factor p S (Madelung.coordinateVector 0) x = normalMomentum S x / (p.m * p.c) := rfl

/-- For the laboratory observer the velocity contraction is the usual Lorentz
factor of the phase drift in the three spatial coordinates. -/
theorem labFactor_eq_mass_gamma (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    factor p S (Madelung.coordinateVector 0) x = (effectiveMass p.c (phaseDifferential S x) / p.m) *
      LorentzCoordinates.gamma p.c (phaseDrift p.c S x) := by
  have hg := ObserverBoostFactor.gamma_drift p.c_pos (DressedClockWorldline.velocity_sq p ht)
    (DressedClockWorldline.velocity_time_pos p ht hf)
  rw [drift_velocity p ht hf] at hg
  rw [factor_eq_mass_gamma p _ ht, hg]
  simp [minkowski, Madelung.coordinateVector]

/-- The laboratory density of the polar field is exactly the invariant
modulus density times its physical observer multiplier. -/
theorem labDensity_eq_factor (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    labDensity p (ActionDensity.actionField p ρ S) x =
      factor p S (Madelung.coordinateVector 0) x * ρ x := by
  rw [labFactor_eq_normalMomentum, labDensity_polar p hρ hS hp]
  ring

end FoliationQM.ObserverCurrentFactor
