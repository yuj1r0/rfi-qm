module

public import FoliationQM.AuxiliaryMetricPullback
public import FoliationQM.AuxiliaryCutoffEnergy

/-!
# Positive cutoff energy under actual coordinate pullback

Source: v13 `thm:wallstrom` Part (c), `eq:log_cutoff_l2_bound` and
`eq:weak_pde_cutoff_bound`, component kinds C and D. The literal differential of the composed cutoff
has genuinely integrable positive pullback-metric energy on each compact
source region. Its integral equals the established target energy, with a
common bound chosen before the radius, and tends to zero. The coordinate
map has its actual derivative and is injective with invertible differential
on that region. No normal h-distance or global manifold conclusion is used.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffPullbackEnergy

open Filter MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy RNCCoordinateVolumeChange SmoothCoordinateTubeCutoff
open scoped Topology Matrix.Norms.Operator

/-- Positive pullback-metric energy of the literal differential of the composed coordinate cutoff. -/
def energy (H : Covector → Mat4) (φ : Covector → Covector)
    (D : Covector → Covector →L[ℝ] Covector) (ε : ℝ) (x : Covector) : ℝ :=
  density (pullMetric H φ D x) * realEnergy (pullMetric H φ D x)
    (fun i => fderiv ℝ (profile ε ∘ φ) x (axis i))

/-- The actual source energy is integrable and equals its target integral, with one nonnegative compact bound chosen before the radius. -/
theorem compact_energy_data {K : Set Covector} {H : Covector → Mat4}
    {φ : Covector → Covector} {D : Covector → Covector →L[ℝ] Covector}
    (hK : IsCompact K) (hφ : ∀ x ∈ K, HasFDerivAt φ (D x) x)
    (hinj : InjOn φ K) (hdet : ∀ x ∈ K, IsUnit (D x).det)
    (hH : ContinuousOn H (φ '' K)) (hpos : ∀ y ∈ φ '' K, (H y).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      IntegrableOn (energy H φ D ε) K volume ∧
      (∫ x in K, energy H φ D ε x) =
        (∫ y in φ '' K, AuxiliaryCutoffEnergy.energy H ε y) ∧
      0 ≤ (∫ x in K, energy H φ D ε x) ∧
      (∫ x in K, energy H φ D ε x) ≤ B *
        (∫ y in φ '' K, ‖fderiv ℝ (profile ε) y‖ ^ 2) := by
  have hcont : ContinuousOn φ K := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  obtain ⟨B, hB, hb⟩ := AuxiliaryCutoffEnergy.compact_energy_data
    (hK.image_of_continuousOn hcont) hH hpos
  refine ⟨B, hB, ?_⟩
  intro ε h0 h1
  obtain ⟨hi, hn, hbound⟩ := hb h0 h1
  have ht := AuxiliaryMetricPullback.realEnergy_integral_transport H hK.measurableSet
    hφ hinj hdet
    (fun x _ => (contDiff_profile h0 h1).differentiable (by simp) (φ x)) hi
  have htrans : IntegrableOn (energy H φ D ε) K volume ∧
      (∫ x in K, energy H φ D ε x) =
        (∫ y in φ '' K, AuxiliaryCutoffEnergy.energy H ε y) := by
    exact ht
  exact ⟨htrans.1, htrans.2, htrans.2.symm ▸ hn, htrans.2.symm ▸ hbound⟩

/-- The actual compact source integral and its square-root energy both tend to zero through positive radii, by genuine transport of the fixed target compact energy. -/
theorem compact_energy_decay {K : Set Covector} {H : Covector → Mat4}
    {φ : Covector → Covector} {D : Covector → Covector →L[ℝ] Covector}
    (hK : IsCompact K) (hφ : ∀ x ∈ K, HasFDerivAt φ (D x) x)
    (hinj : InjOn φ K) (hdet : ∀ x ∈ K, IsUnit (D x).det)
    (hH : ContinuousOn H (φ '' K)) (hpos : ∀ y ∈ φ '' K, (H y).PosDef) :
    Tendsto (fun ε : ℝ => ∫ x in K, energy H φ D ε x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => Real.sqrt (∫ x in K, energy H φ D ε x))
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : ContinuousOn φ K := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have ht := (AuxiliaryCutoffEnergy.compact_energy_decay
    (hK.image_of_continuousOn hcont) hH hpos).1
  obtain ⟨_, _, hb⟩ := compact_energy_data hK hφ hinj hdet hH hpos
  have he : Tendsto (fun ε : ℝ => ∫ x in K, energy H φ D ε x)
      (𝓝[>] 0) (𝓝 0) := by
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hb hε.1 hε.2).2.1.symm
  refine ⟨he, ?_⟩
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp he

end FoliationQM.CoordinateCutoffPullbackEnergy
