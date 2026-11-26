module

public import FoliationQM.PhaseCurrentTransport
public import FoliationQM.RelativePolarStationaryAction

/-! The material and normal-derivative identities of v13 `eq:normal_log_rho`
follow from the conserved phase current. All derivatives are taken on the
actual fields in coordinates (ct,x¹,x²,x³). The physical velocity denominator
a = −∂₀S is positive on the source's future-timelike chart. -/

@[expose] public section
noncomputable section
namespace FoliationQM.NormalLogDensity
open DressedMassDensityVariation ObserverFluxDensity LogDensityTransport LorentzCoordinates
open scoped ContDiff

/-- The two expressions printed in the manuscript, with the same physical
drift, normal momentum and log-density in both. -/
def Formulas (c : ℝ) (ρ S : Covector → ℝ) (x : Covector) : Prop :=
  let v := phaseDrift c S
  let r := fun y => Real.log (ρ y)
  let l := fun y => Real.log (normalMomentum S y)
  let d := spatialDivergence v x + material c v l x
  material c v r x = -d ∧
    phaseDifferential r x 0 = -spatialDot (v x) (spatialGradient r x) / c - d / c

/-- The relativistic continuity equation is equivalent to the two logarithmic
identities wherever the density and normal momentum are positive. -/
theorem continuity_iff_formulas {c : ℝ} {ρ S : Covector → ℝ} {x : Covector}
    (hc : 0 < c) (hρ : DifferentiableAt ℝ ρ x) (hS : ContDiffAt ℝ 2 S x)
    (hp : 0 < ρ x) (ha : 0 < normalMomentum S x) :
    PolarRegularity.densityCurrentDivergence ρ S Madelung.coordinateVector x = 0 ↔
      Formulas c ρ S x := by
  have had := PhaseCurrentTransport.differentiableAt_normalMomentum hS
  have hv := PhaseCurrentTransport.differentiableAt_phaseDrift c hS ha.ne'
  have hvi (i : Fin 3) := (differentiableAt_pi.mp hv) i
  have hbal := PhaseCurrentTransport.phase_balance (ρ := ρ) c hS ha.ne'
  have hmat := balance_iff_material c hρ had hvi hp ha
  have hnorm := balance_iff_normal hc hρ had hvi hp ha
  constructor
  · intro hz
    have hb := hbal.trans (by rw [hz, mul_zero])
    exact ⟨by simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using hmat.mp hb, hnorm.mp hb⟩
  · intro h
    have hz := hbal.symm.trans (hnorm.mpr h.2)
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hc.ne')

/-- The physical Klein–Gordon equation at a regular C² point implies both
transport formulas, including the material derivative of the normal momentum. -/
theorem of_klein_gordon (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 2 ρ x) (hS : ContDiffAt ℝ 2 S x)
    (hp : 0 < ρ x) (ha : 0 < normalMomentum S x)
    (hkg : PolarSecondDifferential.box (ActionDensity.actionField p ρ S) Madelung.coordinateVector x +
      (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) = 0) :
    Formulas p.c ρ S x :=
  (continuity_iff_formulas p.c_pos (hρ.differentiableAt (by norm_num)) hS hp ha).mp
    (((PolarRegularity.kg_eq_zero_iff_madelung_density_coordinates p hρ hS hp).mp hkg).2)

/-- On a positive polar chart of an extremal of the scalar action, conservation
and the subluminal drift on the future-timelike locus give the full source statement. -/
theorem of_scalar_extremal (p : MassiveParameters) {ρ S : Covector → ℝ} {V : Set Covector}
    (hV : IsOpen V) (hρ : ∀ x ∈ V, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ V, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ V, 0 < ρ x)
    (hst : RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S Madelung.coordinateVector V)
    {x : Covector} (hx : x ∈ V) (ha : 0 < normalMomentum S x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    speedSq (phaseDrift p.c S x) < p.c^2 ∧ Formulas p.c ρ S x := by
  have hkg := (RelativePolarStationaryAction.relativePolarStationaryOn_iff_kleinGordon p hV hρ hS hp).mp hst x hx
  have hf : phaseDifferential S x 0 < 0 := neg_pos.mp ha
  have hv := ObserverBoostFactor.speedSq_drift_lt p.c_pos (DressedClockWorldline.velocity_sq p ht)
    (DressedClockWorldline.velocity_time_pos p ht hf)
  rw [drift_velocity p ht hf] at hv
  exact ⟨hv, of_klein_gordon p ((hρ x hx).of_le (by simp)) ((hS x hx).of_le (by simp))
    (hp x hx) ha hkg⟩

/-- For the time-only phase S = exp(−x⁰), the normal momentum is exp(−x⁰)
and the drift is zero. Coupled with density exp(x⁰), the continuity equation
holds while the material derivative of log a equals −c throughout the chart. -/
theorem nonconstant_normal_momentum (c : ℝ) (x : Covector) :
    normalMomentum expMomentum = expMomentum ∧ phaseDrift c expMomentum = 0 ∧
    balance c expDensity (normalMomentum expMomentum) (phaseDrift c expMomentum) x = 0 ∧
    material c (phaseDrift c expMomentum) (fun y => Real.log (normalMomentum expMomentum y)) x = -c := by
  have hd (y : Covector) (μ : Fin 4) : phaseDifferential expMomentum y μ =
      -expMomentum y * Madelung.coordinateVector μ 0 := by
    change fderiv ℝ expMomentum y (Madelung.coordinateVector μ) = _
    rw [(hasFDerivAt_expMomentum y).fderiv]
    simp
  have ha : normalMomentum expMomentum = expMomentum := by
    funext y
    simp [normalMomentum, hd, Madelung.coordinateVector]
  have hv : phaseDrift c expMomentum = 0 := by
    funext y i
    simp [phaseDrift, hd, Madelung.coordinateVector]
  rw [ha, hv]
  exact ⟨rfl, rfl, exp_balance c x, exp_material_momentum c x⟩

end FoliationQM.NormalLogDensity
