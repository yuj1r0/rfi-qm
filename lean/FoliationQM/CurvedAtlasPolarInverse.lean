module

public import FoliationQM.CurvedGlobalMaster

/-!
# Local inverse clock descriptions of a global complex action

A nonzero regular complex field determines a positive density and real
clock branch near each point in a coordinate chart. Every such branch
reproduces the same normalized global action density and all its metric
integrals on regions lying in that branch.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasPolarInverse

open Set MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
  CurvedClockNormalization
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- Every nonzero global regular field admits a local real clock whose density is the normalized global complex action density. -/
theorem local_clock_density (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source)
    (hn : ψ x ≠ 0) :
    ∃ (V : Set Covector) (τ : Covector → ℝ), IsOpen V ∧ A.chart i x ∈ V ∧
      V ⊆ (A.chart i).target ∧ ContDiffOn ℝ 2 τ V ∧
      (∀ y ∈ V, 0 < Complex.normSq (repr A i ψ y) ∧
        ActionDensity.actionField p (fun z => Complex.normSq (repr A i ψ z)) (clockPhase p τ) y =
          repr A i ψ y) ∧
      ∀ z ∈ (A.chart i).source, A.chart i z ∈ V →
        kgDensityField p A ψ z / (p.m ^ 2 * p.c ^ 2) =
          normalizedClockDensity p (A.metric i) (fun y => Complex.normSq (repr A i ψ y)) τ (A.chart i z) := by
  have hlocal : ContDiffOn ℝ 2 (repr A i ψ) (A.chart i).target :=
    fun y hy => (hψ i y hy).contDiffWithinAt
  obtain ⟨V, τ, ho, hxV, hV, hρ, hτ, he⟩ :=
    local_clock_branch p (A.chart i).open_target hlocal ((A.chart i).map_source hx)
      (by rwa [repr_chart A i ψ hx])
  refine ⟨V, τ, ho, hxV, hV, hτ, he, ?_⟩
  intro z hz hzV
  have hrec : ActionDensity.actionField p (fun y => Complex.normSq (repr A i ψ y)) (clockPhase p τ) =ᶠ[𝓝 (A.chart i z)] repr A i ψ :=
    Filter.eventually_of_mem (ho.mem_nhds hzV) (fun y hy => (he y hy).2)
  rw [kgDensityField_chart p A hA hψ i hz, ← CurvedPolarAction.kgDensity_congr p (A.metric i) hrec]
  have hphase : DifferentiableAt ℝ (clockPhase p τ) (A.chart i z) :=
    (((hτ _ hzV).contDiffAt (ho.mem_nhds hzV)).differentiableAt (by decide)).const_mul _
  rw [CurvedPolarAction.density_eq p (A.metric i)
    ((hρ _ hzV).contDiffAt (ho.mem_nhds hzV) |>.differentiableAt (by decide))
    hphase
    (he _ hzV).1]
  exact CurvedClockNormalization.hydro_density_normalized p (A.metric i) _
    (((hτ _ hzV).contDiffAt (ho.mem_nhds hzV)).differentiableAt (by decide))

variable [MeasurableSpace X]

/-- The local inverse clock reproduces the normalized global metric action on every measurable region inside its branch. -/
theorem local_clock_action (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source)
    (hn : ψ x ≠ 0) :
    ∃ (V : Set Covector) (τ : Covector → ℝ), IsOpen V ∧ A.chart i x ∈ V ∧
      V ⊆ (A.chart i).target ∧ ContDiffOn ℝ 2 τ V ∧
      (∀ y ∈ V, 0 < Complex.normSq (repr A i ψ y) ∧
        ActionDensity.actionField p (fun z => Complex.normSq (repr A i ψ z)) (clockPhase p τ) y =
          repr A i ψ y) ∧
      ∀ W : Set X, MeasurableSet W → W ⊆ (A.chart i).source ∩ (A.chart i) ⁻¹' V →
        (∫ z in W, kgDensityField p A ψ z ∂A.measure) / (p.m ^ 2 * p.c ^ 2) =
          ∫ z in W, normalizedClockDensity p (A.metric i)
            (fun y => Complex.normSq (repr A i ψ y)) τ (A.chart i z) ∂A.measure := by
  obtain ⟨V, τ, ho, hxV, hV, hτ, he, hd⟩ := local_clock_density p A hA hψ i hx hn
  refine ⟨V, τ, ho, hxV, hV, hτ, he, ?_⟩
  intro W hW hsub
  rw [← integral_div]
  exact setIntegral_congr_fun hW (fun z hz => hd z (hsub hz).1 (hsub hz).2)

end FoliationQM.CurvedAtlasPolarInverse
