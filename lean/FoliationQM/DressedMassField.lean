module

public import FoliationQM.DressedMassDensityVariation
public import FoliationQM.DressedMassShell

/-!
# Dressed mass and velocity of a scalar phase field

Both lines of the v13 dressed-mass equation use the same phase derivative.
The density equation follows from compact variations at fixed phase. There
is also a local C² formulation using the Klein–Gordon equation directly.
The future orientation uses x⁰ = ct and the inverse Minkowski metric.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DressedMassField

open DressedMassDensityVariation PolarSecondDifferential Madelung
open scoped ContDiff

/-- Both expressions for the positive mass, the sign of its radicand, the
components of the physical velocity and its future timelike normalization. -/
def MassVelocityAt (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) : Prop :=
  let v := phaseDifferential S x
  let M := effectiveMass p.c v
  let U := velocityCovector p.c v
  M = Real.sqrt (minkowski v v) / p.c ∧
    M = p.m * Real.sqrt (1 + p.ellC ^ 2 * quantumCorrection ρ x) ∧
    0 < 1 + p.ellC ^ 2 * quantumCorrection ρ x ∧ 0 < M ∧
    (∀ μ, U μ = -v μ / M) ∧ minkowski U U = p.c ^ 2 ∧ 0 < U 0

private theorem of_shell (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hshell : minkowski (phaseDifferential S x) (phaseDifferential S x) =
      p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * quantumCorrection ρ x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : MassVelocityAt p ρ S x :=
  ⟨rfl, DressedMassShell.mass_formula p ht hshell, DressedMassShell.radicand_pos p ht hshell,
    effectiveMass_pos p.c_pos ht, fun _ => rfl, velocity_normalized p.c_pos ht,
    velocity_future p.c_pos ht hf⟩

/-- Stationarity of the scalar action under density variations with fixed phase
already implies the entire dressed-mass and future-velocity identity. -/
theorem of_density_variations (p : MassiveParameters) {ρ S : Covector → ℝ} {V : Set Covector}
    (hV : IsOpen V) (hρ : ∀ x ∈ V, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ V, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ V, 0 < ρ x) (hstat : DensityStationaryOn p ρ S V)
    {x : Covector} (hx : x ∈ V)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : MassVelocityAt p ρ S x :=
  of_shell p ((densityStationaryOn_iff_mass_shell p hV hρ hS hp).mp hstat x hx) ht hf

/-- An extremal of the full scalar action on an open positive-density domain
satisfies the identity wherever its physical phase momentum is future timelike. -/
theorem of_scalar_extremal (p : MassiveParameters) {ρ S : Covector → ℝ} {V : Set Covector}
    (hV : IsOpen V) (hρ : ∀ x ∈ V, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ V, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ V, 0 < ρ x)
    (hstat : RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S coordinateVector V)
    {x : Covector} (hx : x ∈ V)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : MassVelocityAt p ρ S x := by
  apply of_density_variations p hV hρ hS hp _ hx ht hf
  intro a ha hc hs
  simpa only [mul_zero, add_zero] using hstat a (fun _ => 0) ha contDiff_const hc
    HasCompactSupport.zero hs (by simp)

/-- A C² polar Klein–Gordon solution gives the same mass and normalized future
velocity at the evaluation point, using actual first and second derivatives. -/
theorem of_klein_gordon (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 2 ρ x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < ρ x)
    (hkg : box (ActionDensity.actionField p ρ S) coordinateVector x +
      (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) = 0)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) : MassVelocityAt p ρ S x := by
  have hj := ((PolarRegularity.kg_eq_zero_iff_madelung_density_coordinates p hρ hS hp).mp hkg).1
  apply of_shell p _ ht hf
  unfold phaseDifferential quantumCorrection
  simpa only [mul_div_assoc] using hj

end FoliationQM.DressedMassField
