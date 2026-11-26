module

public import FoliationQM.ManifoldNodalChart
public import FoliationQM.CurvedAtlasDescent

/-!
# The weak equation and continuation across a nodal surface on a metric atlas

Source: v13 `thm:wallstrom` Part(c), "`Pψ = 0` holds distributionally across
all of `𝓜`" and "`ψ` coincides with the unique global smooth solution having
nodal set `𝒩`", component kinds C and D. Let `𝓜` be a smooth four-manifold
with a regular Lorentzian metric atlas whose charts belong to the maximal
atlas, and `𝒩` the closed image of a smooth embedding of a surface. Let `Ψ` be
twice continuously differentiable off `𝒩` with the global curvature-coupled
Klein–Gordon operator vanishing off `𝒩`.

* The global operator at a point is computed in any chart from the chart
  representative, needing regularity of the field only at that point.
* In every atlas chart, if the representative of `Ψ` is square integrable with
  square-integrable coordinate derivatives on a subset `U` of the chart image,
  the weak equation with the chart metric holds against every smooth compact
  test supported in `U`.
* A field `u` that is twice continuously differentiable in every chart and
  almost everywhere equal to `Ψ` in every chart equals `Ψ` off `𝒩`, solves the
  global equation at every point of `𝓜`, and has zero set exactly `𝒩` when a
  continuous extension of `|Ψ|²` vanishes exactly on `𝒩`.

The existence of `u` is the content of the cited Cauchy theorem and is a
hypothesis. Almost everywhere is for coordinate volume in each chart.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MetricAtlasNodalWeakKG

open MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity RealLorentzFrame
open CurvedKGFirstVariation CurvedKGTestResidual RNCCoordinateConnection
open CurvedMetricChartMeasure CurvedAtlasDescent ManifoldNodalChart
open scoped ContDiff Topology Manifold Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- The coordinate wave of a field computed in two charts agrees at a point
where the field is twice continuously differentiable in the charts. -/
theorem wave_compatible_at (A : MetricAtlas X) (hA : SmoothLorentz A) {ψ : X → ℂ} {x : X}
    (hψ : ∀ j, x ∈ (A.chart j).source → ContDiffAt ℝ 2 (repr A j ψ) (A.chart j x))
    (i j : ℕ) (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    CurvedWaveDivergence.wave (A.metric i) (repr A i ψ) (A.chart i x) =
      CurvedWaveDivergence.wave (A.metric j) (repr A j ψ) (A.chart j x) := by
  let φ := A.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = A.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have hg := hA.metric_smooth j _ ((A.chart j).map_source hj)
  have hf := hψ j hj
  rw [CurvedWaveOverlap.wave_germ (metric_germ A i j hi hj) (repr_germ A i j ψ hi hj)]
  have H := CurvedWaveOverlap.wave_pullback_complex (φ := φ) (f := repr A j ψ)
    ((hA.transition_smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
    (by simpa only [he] using hg.differentiableAt (by decide))
    (by simpa only [he] using symmetry_germ A hA j ((A.chart j).map_source hj))
    (by simpa only [he] using hA.negative j _ ((A.chart j).map_source hj))
    (transition_unit A hA i j hi hj) (by simpa only [he] using hf)
  rw [he] at H
  exact H

/-- The global Klein–Gordon operator at a point is the coordinate operator of
the representative in any chart containing the point, when the field is twice
continuously differentiable there. -/
theorem kgOperatorField_chart_at (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) {ψ : X → ℂ} {x : X}
    (hψ : ∀ j, x ∈ (A.chart j).source → ContDiffAt ℝ 2 (repr A j ψ) (A.chart j x))
    (i : ℕ) (hx : x ∈ (A.chart i).source) :
    kgOperatorField p A ψ x = kgOperator p (A.metric i) (repr A i ψ) (A.chart i x) := by
  have hw : waveField A ψ x =
      CurvedWaveDivergence.wave (A.metric i) (repr A i ψ) (A.chart i x) :=
    wave_compatible_at A hA hψ _ i (Classical.choose_spec (exists_chart A x)) hx
  rw [kgOperatorField, kgOperator, hw, scalarField_chart A hA i hx, repr_chart A i ψ hx]

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [ChartedSpace Covector X]
  {f : S → X} {Ψ u : X → ℂ}

/-- A field twice continuously differentiable at a point of the manifold is
so in every atlas chart containing the point. -/
theorem contDiffAt_repr_chart (A : MetricAtlas X)
    (hAc : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ X) {x : X}
    (h : ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ x) (j : ℕ) (hj : x ∈ (A.chart j).source) :
    ContDiffAt ℝ 2 (repr A j Ψ) (A.chart j x) :=
  contDiffAt_repr (hAc j) ((A.chart j).map_source hj) (by rwa [(A.chart j).left_inv hj])

variable [IsManifold 𝓘(ℝ, Covector) ∞ X]

/-- The weak Klein–Gordon equation in every chart of a metric atlas, across a
closed embedded nodal surface, from the global equation off the surface. -/
theorem atlas_weak_equation (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hAc : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ X)
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hΨ : ∀ x, x ∉ range f → ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ x)
    (hKG : ∀ x, x ∉ range f → kgOperatorField p A Ψ x = 0)
    (i : ℕ) {U : Set Covector} (hU : U ⊆ (A.chart i).target) {φ : Covector → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp (repr A i Ψ) 2 (volume.restrict U))
    (hD : ∀ j : Fin 4,
      MemLp (fun z => fderiv ℝ (repr A i Ψ) z (axis j)) 2 (volume.restrict U)) :
    Integrable (fun z => volumeFactor (A.metric i z) •
      cross p (A.metric i) φ (repr A i Ψ) z) volume ∧
    (∫ z, volumeFactor (A.metric i z) • cross p (A.metric i) φ (repr A i Ψ) z) = 0 := by
  refine chart_weak_equation p hf hN (hAc i) hU hφ hcφ hs
    (fun z hz => hA.metric_smooth i z (hU hz)) (fun z hz => hA.negative i z (hU hz)) hψ hD hΨ
    fun z hz hn => ?_
  have hx : (A.chart i).symm z ∈ (A.chart i).source := (A.chart i).map_target (hU hz)
  have h := kgOperatorField_chart_at p A hA
    (fun j hj => contDiffAt_repr_chart A hAc (hΨ _ hn) j hj) i hx
  rw [(A.chart i).right_inv (hU hz)] at h
  exact h.symm.trans (hKG _ hn)

/-- Continuation on a metric atlas: a field twice continuously differentiable
in every chart and almost everywhere equal there to a solution off the nodal
surface equals it off the surface, solves the global equation everywhere, and
vanishes exactly on the surface when a continuous extension of the squared
modulus does. -/
theorem atlas_continuation (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hAc : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ X)
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hΨ : ∀ x, x ∉ range f → ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ x)
    (hKG : ∀ x, x ∉ range f → kgOperatorField p A Ψ x = 0)
    (hu : Regular A 2 u)
    (hae : ∀ i, repr A i u =ᵐ[volume.restrict (A.chart i).target] repr A i Ψ)
    {ρ : X → ℝ} (hρ : Continuous ρ) (hρψ : ∀ x, x ∉ range f → ρ x = ‖Ψ x‖ ^ 2)
    (hzero : ∀ x, ρ x = 0 ↔ x ∈ range f) :
    (∀ x, x ∉ range f → u x = Ψ x) ∧ (∀ x, kgOperatorField p A u x = 0) ∧
    (∀ x, ‖u x‖ ^ 2 = ρ x) ∧ ∀ x, u x = 0 ↔ x ∈ range f := by
  have key (i : ℕ) := chart_continuation p hf hN (hAc i) (A.chart i).open_target Subset.rfl
    (fun z hz => hA.metric_smooth i z hz) (fun z hz => hA.negative i z hz) hΨ
    (fun z hz hn => by
      have hx : (A.chart i).symm z ∈ (A.chart i).source := (A.chart i).map_target hz
      have h := kgOperatorField_chart_at p A hA
        (fun j hj => contDiffAt_repr_chart A hAc (hΨ _ hn) j hj) i hx
      rw [(A.chart i).right_inv hz] at h
      exact h.symm.trans (hKG _ hn))
    (hu i) (hae i) (hρ.comp_continuousOn (A.chart i).continuousOn_symm)
    (fun z _ hn => hρψ _ hn) (fun z _ => hzero _)
  refine ⟨fun x hn => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  all_goals
    obtain ⟨i, hi⟩ := exists_chart A x
    have hz : A.chart i x ∈ (A.chart i).target := (A.chart i).map_source hi
    have hl : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  · have h := (key i).1 _ hz (by rwa [hl])
    rwa [hl] at h
  · rw [kgOperatorField_chart p A hA hu i hi]
    exact (key i).2.1 _ hz
  · have h := (key i).2.2.1 _ hz
    rwa [hl] at h
  · have h := (key i).2.2.2 _ hz
    rwa [hl] at h

end FoliationQM.MetricAtlasNodalWeakKG
