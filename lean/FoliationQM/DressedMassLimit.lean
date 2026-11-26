module

public import FoliationQM.ObserverFluxDensity

/-! Small-correction and zero-correction limits for the ADM statement after
`eq:measure_invariance`. On a regular timelike polar chart the ratio M_eff/m
is fixed by the KG equation. Its convergence controls the relative dressing
of rest density and of the physical four-velocity. Family members may use
different positive physical parameters and different evaluation points. -/

@[expose] public section
noncomputable section
namespace FoliationQM.DressedMassLimit
open Filter Topology DressedMassDensityVariation ScalarDressedCurrent DressedMassField
open scoped ContDiff

/-- Ratio of actual effective to bare mass. -/
def massRatio (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : ℝ :=
  effectiveMass p.c (phaseDifferential S x) / p.m

/-- The raised physical phase momentum divided by the bare mass. On the
fixed-mass eikonal shell it is the particle four-velocity. -/
def bareVelocity (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) : Covector :=
  ContactReeb.sharp (fun μ => -phaseDifferential S x μ / p.m)

/-- The actual normalized velocity is the bare phase velocity rescaled by
the inverse mass ratio on the timelike chart. -/
theorem velocity_eq_scaled (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) :
    DressedClockWorldline.velocity p S x = (massRatio p S x)⁻¹ • bareVelocity p S x := by
  funext μ
  by_cases hμ : μ = 0 <;>
    simp [DressedClockWorldline.velocity, bareVelocity, massRatio, ContactReeb.sharp,
      velocityCovector, hμ, Pi.smul_apply, smul_eq_mul, field, p.m_pos.ne']

/-- On the regular shell the mass ratio is precisely the dimensionless square root. -/
theorem massRatio_eq (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (h : MassVelocityAt p ρ S x) : massRatio p S x = Real.sqrt (1 + p.ellC^2 * quantumCorrection ρ x) := by
  unfold massRatio
  rw [h.2.1]
  field_simp [p.m_pos.ne']

/-- The finite relative mass error is the absolute Compton-scale correction
divided by one plus the positive mass ratio. -/
theorem massRatio_error (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (h : MassVelocityAt p ρ S x) :
    |massRatio p S x - 1| = |p.ellC^2 * quantumCorrection ρ x| / (massRatio p S x + 1) := by
  have hr : 0 < massRatio p S x := div_pos h.2.2.2.1 p.m_pos
  have hs : massRatio p S x ^ 2 = 1 + p.ellC^2 * quantumCorrection ρ x := by
    rw [massRatio_eq p h, Real.sq_sqrt h.2.2.1.le]
  have hf : (massRatio p S x - 1) * (massRatio p S x + 1) = p.ellC^2 * quantumCorrection ρ x := by
    linarith only [hs]
  apply (eq_div_iff (by positivity : massRatio p S x + 1 ≠ 0)).mpr
  simpa only [abs_mul, abs_of_pos (by positivity : 0 < massRatio p S x + 1)] using congrArg abs hf

/-- On the exact bare mass shell the dressed density and raised velocity are
the invariant density and the bare phase velocity at the same point. -/
theorem zero_correction (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (h : MassVelocityAt p ρ S x) (hz : quantumCorrection ρ x = 0) :
    restDensity p ρ S x = ρ x ∧ DressedClockWorldline.velocity p S x = bareVelocity p S x := by
  have hm : massRatio p S x = 1 := by simp [massRatio_eq p h, hz]
  constructor
  · change ρ x * effectiveMass p.c (phaseDifferential S x) / p.m = ρ x
    rw [mul_div_assoc, ← massRatio, hm, mul_one]
  · rw [velocity_eq_scaled, hm, inv_one, one_smul]

/-- A vanishing Compton-scale correction forces unit relative dressing,
without any convergence assumption on the densities or momenta. -/
theorem tendsto_massRatio {ι : Type*} {l : Filter ι} (p : ι → MassiveParameters)
    (ρ S : ι → Covector → ℝ) (x : ι → Covector)
    (hfield : ∀ᶠ i in l, MassVelocityAt (p i) (ρ i) (S i) (x i))
    (hsmall : Tendsto (fun i => (p i).ellC^2 * |quantumCorrection (ρ i) (x i)|) l (𝓝 0)) :
    Tendsto (fun i => massRatio (p i) (S i) (x i)) l (𝓝 1) := by
  have hq : Tendsto (fun i => (p i).ellC^2 * quantumCorrection (ρ i) (x i)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hsmall.congr'
    filter_upwards with i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (p i).ellC)]
  have h1 : Tendsto (fun _ : ι => (1:ℝ)) l (𝓝 1) := tendsto_const_nhds
  have hs := (h1.add hq).sqrt
  apply (show Tendsto (fun i => Real.sqrt (1 + (p i).ellC^2 * quantumCorrection (ρ i) (x i))) l (𝓝 1) by
    simpa only [add_zero, Real.sqrt_one] using hs).congr'
  filter_upwards [hfield] with i hi
  exact (massRatio_eq (p i) hi).symm

/-- Small Compton-scale correction for a family of regular C² Klein–Gordon
solutions preserves the limits of convergent invariant densities and bare
four-velocities in the dressed fields. -/
theorem kleinGordon_limits {ι : Type*} {l : Filter ι} (p : ι → MassiveParameters)
    (ρ S : ι → Covector → ℝ) (x : ι → Covector)
    (hkg : ∀ᶠ i in l, ContDiffAt ℝ 2 (ρ i) (x i) ∧ ContDiffAt ℝ 2 (S i) (x i) ∧
      0 < ρ i (x i) ∧
      PolarSecondDifferential.box (ActionDensity.actionField (p i) (ρ i) (S i)) Madelung.coordinateVector (x i) +
        ((((p i).m^2*(p i).c^2/(p i).hbar^2 : ℝ) : ℂ) * ActionDensity.actionField (p i) (ρ i) (S i) (x i)) = 0 ∧
      0 < minkowski (phaseDifferential (S i) (x i)) (phaseDifferential (S i) (x i)) ∧
      phaseDifferential (S i) (x i) 0 < 0)
    (hsmall : Tendsto (fun i => (p i).ellC^2 * |quantumCorrection (ρ i) (x i)|) l (𝓝 0))
    {R : ℝ} {u : Covector} (hρ : Tendsto (fun i => ρ i (x i)) l (𝓝 R))
    (hu : Tendsto (fun i => bareVelocity (p i) (S i) (x i)) l (𝓝 u)) :
    Tendsto (fun i => massRatio (p i) (S i) (x i)) l (𝓝 1) ∧
      Tendsto (fun i => restDensity (p i) (ρ i) (S i) (x i)) l (𝓝 R) ∧
      Tendsto (fun i => DressedClockWorldline.velocity (p i) (S i) (x i)) l (𝓝 u) := by
  have hfield : ∀ᶠ i in l, MassVelocityAt (p i) (ρ i) (S i) (x i) := by
    filter_upwards [hkg] with i hi
    rcases hi with ⟨hr, hs, hp, hk, ht, hf⟩
    exact of_klein_gordon (p i) hr hs hp hk ht hf
  have hm := tendsto_massRatio p ρ S x hfield hsmall
  have hinv := hm.inv₀ (one_ne_zero : (1:ℝ) ≠ 0)
  refine ⟨hm, ?_, ?_⟩
  · simpa only [restDensity, massRatio, mul_one, mul_div_assoc] using hρ.mul hm
  · apply (show Tendsto (fun i => (massRatio (p i) (S i) (x i))⁻¹ • bareVelocity (p i) (S i) (x i))
        l (𝓝 u) by simpa only [inv_one, one_smul] using hinv.smul hu).congr'
    filter_upwards with i
    exact (velocity_eq_scaled (p i) (S i) (x i)).symm

end FoliationQM.DressedMassLimit
