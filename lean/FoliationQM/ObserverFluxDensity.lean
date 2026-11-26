module

public import FoliationQM.ObserverBoostFactor
public import FoliationQM.ObserverRestVolume
public import FoliationQM.ScalarDressedCurrent

/-! The laboratory normal in v13 `eq:jacobian_density` is (1,0,0,0).
Its contraction with the original Klein–Gordon current gives the measured
density. On the future-timelike domain the reconstructed three-velocity,
the observer boost factor and the dressed rest density give the same flux.
Coordinates are (ct,x¹,x²,x³). -/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFluxDensity

open DressedMassDensityVariation LorentzCoordinates ScalarDressedCurrent

/-- Normal physical momentum a = −∂₀S in the given laboratory frame. -/
def normalMomentum (S : Covector → ℝ) (x : Covector) : ℝ := -phaseDifferential S x 0

/-- The three-dimensional drift defined in v13 by c ∇S/a. -/
def phaseDrift (c : ℝ) (S : Covector → ℝ) (x : Covector) : Spatial :=
  fun i => c * phaseDifferential S x i.succ / normalMomentum S x

/-- Measured scalar density obtained by contracting the actual current with
the coordinate observer's future normal and dividing by c. -/
def labDensity (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  ScalarPhaseCurrent.current p ψ x 0 / p.c

/-- The spatial-to-temporal ratio of the raised four-velocity equals the
source's laboratory phase drift. -/
theorem drift_velocity (p : MassiveParameters) {S : Covector → ℝ} {x : Covector}
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    ObserverBoostFactor.drift p.c (DressedClockWorldline.velocity p S x) = phaseDrift p.c S x := by
  have hm := (effectiveMass_pos p.c_pos ht).ne'
  funext i
  simp only [ObserverBoostFactor.drift, DressedClockWorldline.velocity, ContactReeb.sharp,
    Fin.succ_ne_zero, ite_false, ite_true, velocityCovector, neg_div, neg_neg, phaseDrift,
    normalMomentum]
  field_simp [hm, hf.ne]

/-- The coordinate flux equals ρa/(mc) on any regular polar chart. -/
theorem labDensity_polar (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    labDensity p (ActionDensity.actionField p ρ S) x = ρ x * normalMomentum S x / (p.m*p.c) := by
  rw [labDensity, current_actionField p hρ hS hp]
  unfold normalMomentum
  ring

/-- Both density expressions of the v13 observer-flux equation, together
with positivity, the subluminal bound and the exact Lorentz boost factor. -/
theorem labDensity_eq_boost_restDensity (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    let U := DressedClockWorldline.velocity p S x
    let v := phaseDrift p.c S x
    let σ := labDensity p (ActionDensity.actionField p ρ S) x
    σ = ρ x * normalMomentum S x / (p.m*p.c) ∧
      σ = gamma p.c v * restDensity p ρ S x ∧ 0 < σ ∧
      speedSq v < p.c^2 ∧ gamma p.c v = U 0 / p.c ∧ 1 ≤ gamma p.c v := by
  dsimp only
  have hs := DressedClockWorldline.velocity_sq p ht
  have hu := DressedClockWorldline.velocity_time_pos p ht hf
  have hg := ObserverBoostFactor.gamma_drift p.c_pos hs hu
  have hv := ObserverBoostFactor.speedSq_drift_lt p.c_pos hs hu
  rw [drift_velocity p ht hf] at hg hv
  have hflux := (current_eq_restDensity_velocity p hρ hS hp ht).2
  have hzero := congrFun hflux 0
  have heq : labDensity p (ActionDensity.actionField p ρ S) x =
      gamma p.c (phaseDrift p.c S x) * restDensity p ρ S x := by
    rw [labDensity, hzero, hg]
    change (restDensity p ρ S x * velocityCovector p.c (phaseDifferential S x) 0) / p.c =
      (velocityCovector p.c (phaseDifferential S x) 0 / p.c) * restDensity p ρ S x
    ring
  exact ⟨labDensity_polar p hρ hS hp, heq, heq ▸ mul_pos (hg ▸ div_pos hu p.c_pos)
    (current_eq_restDensity_velocity p hρ hS hp ht).1, hv, hg, hg ▸ ObserverBoostFactor.gamma_ge_one p.c_pos hs hu⟩

/-- Contraction with any future unit observer gives the same factorization,
where the relative boost factor is the Minkowski pairing of n and U divided by c. -/
theorem normal_flux (p : MassiveParameters) {ρ S : Covector → ℝ} {x n : Covector}
    (hn : minkowski n n = 1) (hnf : 0 < n 0)
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) :
    let σ := ContactReeb.pairing n (ScalarPhaseCurrent.current p (ActionDensity.actionField p ρ S) x) / p.c
    let γ := minkowski n (DressedClockWorldline.velocity p S x) / p.c
    σ = γ * restDensity p ρ S x ∧ 1 ≤ γ ∧ 0 < σ := by
  dsimp only
  obtain ⟨hr, hj⟩ := current_eq_restDensity_velocity p hρ hS hp ht
  have hγ := ObserverBoostFactor.normal_gamma_ge_one p.c_pos hn hnf
    (DressedClockWorldline.velocity_sq p ht) (DressedClockWorldline.velocity_time_pos p ht hf)
  rw [hj, ContactReeb.pairing_smul_right]
  have he := ContactReeb.pairing_sharp_right n (DressedClockWorldline.velocity p S x)
  rw [show ContactReeb.sharp (DressedClockWorldline.velocity p S x) =
    velocityCovector p.c (phaseDifferential S x) from ContactReeb.sharp_sharp _] at he
  rw [he, mul_div_assoc, mul_comm (restDensity p ρ S x)]
  exact ⟨rfl, hγ, mul_pos (lt_of_lt_of_le one_pos hγ) hr⟩

/-- The probability of a laboratory tangent parallelepiped agrees with the
dressed density times its corresponding comoving proper three-volume. The Gram
determinant is computed on the projected edges for the same physical velocity. -/
theorem probability_element (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x))
    (hf : phaseDifferential S x 0 < 0) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    labDensity p (ActionDensity.actionField p ρ S) x * |A.det| =
      restDensity p ρ S x * Real.sqrt (ObserverRestVolume.spatialGram
        (ObserverRestVolume.combine (ObserverRestVolume.projected p.c
          (DressedClockWorldline.velocity p S x)) A)).det := by
  have h := labDensity_eq_boost_restDensity p hρ hS hp ht hf
  rw [ObserverRestVolume.parallelepiped_volume p.c_pos (DressedClockWorldline.velocity_sq p ht)
    (DressedClockWorldline.velocity_time_pos p ht hf) A, h.2.1, h.2.2.2.2.1]
  ring

end FoliationQM.ObserverFluxDensity
