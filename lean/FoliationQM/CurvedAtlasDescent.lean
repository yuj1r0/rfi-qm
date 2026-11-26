module

public import FoliationQM.CurvedMetricChartMeasure
public import FoliationQM.CurvedWaveOverlap
public import FoliationQM.CurvedKGTestResidual
public import FoliationQM.CurvedRicciOverlap

/-!
# Actual local representatives and their descent through a Lorentz atlas

The metric atlas already records the Jacobian differential and metric
pullback on each overlap. Local smoothness and negative determinant imply
the regularity of these Jacobians. Compatible coordinate observables
therefore define global fields with the same value in every chart.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasDescent

open Set Filter LorentzMatrixGroup CurvedMetricChartMeasure RNCCoordinateVolumeChange
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- Regular Lorentz metric data on the chart targets and C³ transition maps on their actual overlaps. -/
structure SmoothLorentz (A : MetricAtlas X) : Prop where
  metric_smooth : ∀ i y, y ∈ (A.chart i).target → ContDiffAt ℝ 2 (A.metric i) y
  symmetric : ∀ i y, y ∈ (A.chart i).target → (A.metric i y).IsSymm
  negative : ∀ i y, y ∈ (A.chart i).target → (A.metric i y).det < 0
  transition_smooth : ∀ i j y, y ∈ A.chart i '' ((A.chart i).source ∩ (A.chart j).source) →
    ContDiffAt ℝ 3 (A.chart j ∘ (A.chart i).symm) y

/-- The scalar or vector-valued coordinate representative of an actual global field. -/
def repr {F : Type*} (A : MetricAtlas X) (i : ℕ) (f : X → F) : Covector → F := f ∘ (A.chart i).symm

/-- Coordinate regularity of a global field is tested on the open target of every chart. -/
def Regular {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : MetricAtlas X)
    (n : WithTop ℕ∞) (f : X → F) : Prop :=
  ∀ i y, y ∈ (A.chart i).target → ContDiffAt ℝ n (repr A i f) y

/-- The value of a coordinate representative at the coordinate of a point in its chart. -/
theorem repr_chart {F : Type*} (A : MetricAtlas X) (i : ℕ) (f : X → F) {x : X}
    (hx : x ∈ (A.chart i).source) : repr A i f (A.chart i x) = f x := by
  simp only [repr, Function.comp_apply, (A.chart i).left_inv hx]

/-- The coordinate overlap is an open subset of the first chart's target. -/
theorem overlap_open (A : MetricAtlas X) (i j : ℕ) :
    IsOpen (A.chart i '' ((A.chart i).source ∩ (A.chart j).source)) :=
  (A.chart i).isOpen_image_source_inter (A.chart j).open_source

/-- The atlas's supplied differential agrees with the actual Fréchet differential on the overlap. -/
theorem transitionDeriv_eq (A : MetricAtlas X) (i j : ℕ) {y : Covector}
    (hy : y ∈ A.chart i '' ((A.chart i).source ∩ (A.chart j).source)) :
    A.transitionDeriv i j y = fderiv ℝ (A.chart j ∘ (A.chart i).symm) y :=
  (A.hasDeriv i j y hy).fderiv.symm

/-- Negative metric determinants force every transition Jacobian to be nonsingular. -/
theorem transition_unit (A : MetricAtlas X) (hA : SmoothLorentz A) (i j : ℕ) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    IsUnit (jacobianMatrix (fderiv ℝ (A.chart j ∘ (A.chart i).symm) (A.chart i x))).det := by
  have hp := A.metric_pullback i j (A.chart i x) ⟨x, ⟨hi, hj⟩, rfl⟩
  rw [pullMetric, transitionDeriv_eq A i j ⟨x, ⟨hi, hj⟩, rfl⟩] at hp
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he := congrArg Matrix.det hp
  rw [det_pullMatrix, hz, zero_pow (by decide), zero_mul] at he
  exact (hA.negative i _ ((A.chart i).map_source hi)).ne he

/-- Actual pullback of the second metric represents the first metric on a neighborhood of an overlap point. -/
theorem metric_germ (A : MetricAtlas X) (i j : ℕ) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    A.metric i =ᶠ[𝓝 (A.chart i x)]
      pullMetric (A.metric j) (A.chart j ∘ (A.chart i).symm) (fderiv ℝ (A.chart j ∘ (A.chart i).symm)) := by
  filter_upwards [(overlap_open A i j).mem_nhds ⟨x, ⟨hi, hj⟩, rfl⟩] with y hy
  rw [A.metric_pullback i j y hy, pullMetric, transitionDeriv_eq A i j hy]
  rfl

/-- Representatives of one global field agree as germs after composition with the transition. -/
theorem repr_germ {F : Type*} (A : MetricAtlas X) (i j : ℕ) (f : X → F) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    repr A i f =ᶠ[𝓝 (A.chart i x)] repr A j f ∘ (A.chart j ∘ (A.chart i).symm) := by
  filter_upwards [(overlap_open A i j).mem_nhds ⟨x, ⟨hi, hj⟩, rfl⟩] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [repr, Function.comp_apply, (A.chart i).left_inv hz.1, (A.chart j).left_inv hz.2]

/-- Local metric symmetry holds on a full neighborhood of each coordinate point in a chart. -/
theorem symmetry_germ (A : MetricAtlas X) (hA : SmoothLorentz A) (i : ℕ) {y : Covector}
    (hy : y ∈ (A.chart i).target) : ∀ᶠ z in 𝓝 y, (A.metric i z).IsSymm :=
  Filter.Eventually.mono ((A.chart i).open_target.mem_nhds hy) fun _ hz => hA.symmetric i _ hz

/-- Compatibility means equality of the observed scalar or vector value in every pair of charts at the same point. -/
def Compatible {F : Type*} (A : MetricAtlas X) (chartwise : ℕ → Covector → F) : Prop :=
  ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source → chartwise i (A.chart i x) = chartwise j (A.chart j x)

/-- Every point lies in at least one atlas chart. -/
theorem exists_chart (A : MetricAtlas X) (x : X) : ∃ i, x ∈ (A.chart i).source :=
  mem_iUnion.mp (A.cover.symm ▸ mem_univ x)

/-- An auxiliary pointwise chart choice defines an observable; compatibility removes dependence on that choice. -/
def descend {F : Type*} (A : MetricAtlas X) (chartwise : ℕ → Covector → F) (x : X) : F :=
  chartwise (Classical.choose (exists_chart A x)) (A.chart (Classical.choose (exists_chart A x)) x)

/-- The descended global observable evaluates in any chart containing the point. -/
theorem descend_chart {F : Type*} (A : MetricAtlas X) {chartwise : ℕ → Covector → F} (h : Compatible A chartwise)
    (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) : descend A chartwise x = chartwise i (A.chart i x) :=
  h _ i x (Classical.choose_spec (exists_chart A x)) hx

/-- The coordinate complex wave representatives of a globally regular field are compatible. -/
theorem wave_compatible (A : MetricAtlas X) (hA : SmoothLorentz A) {ψ : X → ℂ}
    (hψ : Regular A 2 ψ) : Compatible A (fun i => CurvedWaveDivergence.wave (A.metric i) (repr A i ψ)) := by
  intro i j x hi hj
  change CurvedWaveDivergence.wave (A.metric i) (repr A i ψ) (A.chart i x) =
    CurvedWaveDivergence.wave (A.metric j) (repr A j ψ) (A.chart j x)
  let φ := A.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = A.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have hg := hA.metric_smooth j _ ((A.chart j).map_source hj)
  have hf := hψ j _ ((A.chart j).map_source hj)
  rw [CurvedWaveOverlap.wave_germ (metric_germ A i j hi hj) (repr_germ A i j ψ hi hj)]
  have H := CurvedWaveOverlap.wave_pullback_complex (φ := φ) (f := repr A j ψ)
    ((hA.transition_smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
    (by simpa only [he] using hg.differentiableAt (by decide))
    (by simpa only [he] using symmetry_germ A hA j ((A.chart j).map_source hj))
    (by simpa only [he] using hA.negative j _ ((A.chart j).map_source hj))
    (transition_unit A hA i j hi hj) (by simpa only [he] using hf)
  rw [he] at H
  exact H

/-- The global complex wave computed from chart representatives of the field. -/
def waveField (A : MetricAtlas X) (ψ : X → ℂ) : X → ℂ :=
  descend A (fun i => CurvedWaveDivergence.wave (A.metric i) (repr A i ψ))

/-- Every chart computes exactly the descended global complex wave. -/
theorem waveField_chart (A : MetricAtlas X) (hA : SmoothLorentz A) {ψ : X → ℂ}
    (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    waveField A ψ x = CurvedWaveDivergence.wave (A.metric i) (repr A i ψ) (A.chart i x) :=
  descend_chart A (wave_compatible A hA hψ) i hx

/-- The inverse-metric Hermitian kinetic field computed in different charts is compatible. -/
theorem kinetic_compatible (A : MetricAtlas X) (hA : SmoothLorentz A) {u f : X → ℂ}
    (hu : Regular A 2 u) (hf : Regular A 2 f) :
    Compatible A (fun i => CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f)) := by
  intro i j x hi hj
  let φ := A.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = A.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have hkin : CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f) (A.chart i x) =
      CurvedFluxGreen.kinetic (pullMetric (A.metric j) φ (fderiv ℝ φ))
        (repr A j u ∘ φ) (repr A j f ∘ φ) (A.chart i x) := by
    simp only [CurvedFluxGreen.kinetic, (metric_germ A i j hi hj).self_of_nhds,
      (repr_germ A i j u hi hj).fderiv_eq (𝕜 := ℝ), (repr_germ A i j f hi hj).fderiv_eq (𝕜 := ℝ), φ]
  change CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f) (A.chart i x) = _
  rw [hkin]
  have hp := (hA.transition_smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩).differentiableAt (by decide)
  have H := CurvedKineticCovariance.kinetic_pullback (φ := φ) (A.metric j) hp.hasFDerivAt
    (transition_unit A hA i j hi hj)
    (by simpa only [he] using (hu j _ ((A.chart j).map_source hj)).differentiableAt (by decide))
    (by simpa only [he] using (hf j _ ((A.chart j).map_source hj)).differentiableAt (by decide))
  rw [he] at H
  exact H

/-- The global complex kinetic pairing computed from the field differentials in compatible charts. -/
def kineticField (A : MetricAtlas X) (u f : X → ℂ) : X → ℂ :=
  descend A (fun i => CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f))

/-- The global kinetic pairing evaluates in every chart containing the point. -/
theorem kineticField_chart (A : MetricAtlas X) (hA : SmoothLorentz A) {u f : X → ℂ}
    (hu : Regular A 2 u) (hf : Regular A 2 f) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    kineticField A u f x = CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f) (A.chart i x) :=
  descend_chart A (kinetic_compatible A hA hu hf) i hx

/-- A positive density and real action of coordinate class C² produce a global complex field of the same class. -/
theorem regular_actionField (A : MetricAtlas X) (p : MassiveParameters) {ρ S : X → ℝ}
    (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    Regular A 2 (ActionDensity.actionField p ρ S) := by
  intro i y hy
  exact PolarRegularity.contDiffAt_actionField p (hρ i y hy) (hS i y hy) (hp ((A.chart i).symm y))

/-- The computed coordinate scalar curvatures agree on every overlap of the regular metric atlas. -/
theorem scalar_compatible (A : MetricAtlas X) (hA : SmoothLorentz A) :
    Compatible A (fun i => RNCCoordinateCurvature.scalar (A.metric i)) := by
  intro i j x hi hj
  let φ := A.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = A.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have hg := hA.metric_smooth j _ ((A.chart j).map_source hj)
  have H := CurvedRicciOverlap.scalar_overlap (φ := φ)
    (hA.transition_smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩)
    (by simpa only [he] using hg)
    (by simpa only [he] using symmetry_germ A hA j ((A.chart j).map_source hj))
    (by simpa only [he] using isUnit_iff_ne_zero.mpr (hA.negative j _ ((A.chart j).map_source hj)).ne)
    (transition_unit A hA i j hi hj) (metric_germ A i j hi hj)
  rw [he] at H
  exact H

/-- Global scalar curvature computed from the metric's actual local coordinate derivatives. -/
def scalarField (A : MetricAtlas X) : X → ℝ :=
  descend A (fun i => RNCCoordinateCurvature.scalar (A.metric i))

/-- Scalar curvature may be evaluated in any chart containing the point. -/
theorem scalarField_chart (A : MetricAtlas X) (hA : SmoothLorentz A) (i : ℕ) {x : X}
    (hx : x ∈ (A.chart i).source) :
    scalarField A x = RNCCoordinateCurvature.scalar (A.metric i) (A.chart i x) :=
  descend_chart A (scalar_compatible A hA) i hx

/-- The global normalized Klein–Gordon field operator combines the descended wave and scalar curvature. -/
def kgOperatorField (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) (x : X) : ℂ :=
  waveField A ψ x + (p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 - scalarField A x / 6) • ψ x

/-- Every chart gives the same normalized global Klein–Gordon operator on a regular field. -/
theorem kgOperatorField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    kgOperatorField p A ψ x = CurvedKGTestResidual.kgOperator p (A.metric i) (repr A i ψ) (A.chart i x) := by
  rw [kgOperatorField, CurvedKGTestResidual.kgOperator, waveField_chart A hA hψ i hx,
    scalarField_chart A hA i hx, repr_chart A i ψ hx]

end FoliationQM.CurvedAtlasDescent
