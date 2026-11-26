module

public import FoliationQM.CurvedAtlasAction

/-!
# Independence of the chosen regular metric atlas

Cross-atlas transitions are genuine smooth coordinate changes whose actual
differentials relate the metric arrays. The computed scalar curvature,
Hermitian kinetic pairing and determinant measure consequently agree,
so both global action integrals are independent of the atlas.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasIndependence

open Set LorentzMatrixGroup CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
open RNCCoordinateVolumeChange MeasureTheory
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- Cross-atlas transition regularity and metric congruence with the actual coordinate derivative. -/
structure CrossTransition (A B : MetricAtlas X) : Prop where
  smooth : ∀ i j y, y ∈ A.chart i '' ((A.chart i).source ∩ (B.chart j).source) →
    ContDiffAt ℝ 3 (B.chart j ∘ (A.chart i).symm) y
  metric : ∀ i j y, y ∈ A.chart i '' ((A.chart i).source ∩ (B.chart j).source) →
    A.metric i y = pullMetric (B.metric j) (B.chart j ∘ (A.chart i).symm)
      (fderiv ℝ (B.chart j ∘ (A.chart i).symm)) y

variable {A B : MetricAtlas X}

/-- The cross-atlas metric relation is an equality on a full neighborhood at an overlap point. -/
theorem metric_germ (h : CrossTransition A B) (i j : ℕ) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (B.chart j).source) :
    A.metric i =ᶠ[𝓝 (A.chart i x)] pullMetric (B.metric j) (B.chart j ∘ (A.chart i).symm)
      (fderiv ℝ (B.chart j ∘ (A.chart i).symm)) := by
  filter_upwards [((A.chart i).isOpen_image_source_inter (B.chart j).open_source).mem_nhds
    ⟨x, ⟨hi, hj⟩, rfl⟩] with y hy
  exact h.metric i j y hy

/-- An actual global field has coordinate representatives related by the cross-atlas transition germ. -/
theorem repr_germ {F : Type*} (A B : MetricAtlas X) (i j : ℕ) (f : X → F) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (B.chart j).source) :
    repr A i f =ᶠ[𝓝 (A.chart i x)] repr B j f ∘ (B.chart j ∘ (A.chart i).symm) := by
  filter_upwards [((A.chart i).isOpen_image_source_inter (B.chart j).open_source).mem_nhds
    ⟨x, ⟨hi, hj⟩, rfl⟩] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [CurvedAtlasDescent.repr, Function.comp_apply, (A.chart i).left_inv hz.1, (B.chart j).left_inv hz.2]

/-- The cross-atlas Jacobian is nonsingular because it pulls back a metric to a metric with negative determinant. -/
theorem transition_unit (h : CrossTransition A B) (hA : SmoothLorentz A) (i j : ℕ) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (B.chart j).source) :
    IsUnit (jacobianMatrix (fderiv ℝ (B.chart j ∘ (A.chart i).symm) (A.chart i x))).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he := congrArg Matrix.det (h.metric i j _ ⟨x, ⟨hi, hj⟩, rfl⟩)
  rw [pullMetric, det_pullMatrix, hz, zero_pow (by decide), zero_mul] at he
  exact (hA.negative i _ ((A.chart i).map_source hi)).ne he

/-- The global computed curvature scalar is the same for the two compatible regular metric atlases. -/
theorem scalarField_eq (h : CrossTransition A B) (hA : SmoothLorentz A) (hB : SmoothLorentz B) :
    scalarField A = scalarField B := by
  funext x
  obtain ⟨i, hi⟩ := exists_chart A x
  obtain ⟨j, hj⟩ := exists_chart B x
  rw [scalarField_chart A hA i hi, scalarField_chart B hB j hj]
  let φ := B.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = B.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have H := CurvedRicciOverlap.scalar_overlap (φ := φ) (h.smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩)
    (by simpa only [he] using hB.metric_smooth j _ ((B.chart j).map_source hj))
    (by simpa only [he] using symmetry_germ B hB j ((B.chart j).map_source hj))
    (by simpa only [he] using isUnit_iff_ne_zero.mpr (hB.negative j _ ((B.chart j).map_source hj)).ne)
    (transition_unit h hA i j hi hj) (metric_germ h i j hi hj)
  rw [he] at H
  exact H

/-- The full complex wave field is independent of the compatible regular metric atlas. -/
theorem waveField_eq (h : CrossTransition A B) (hA : SmoothLorentz A) (hB : SmoothLorentz B)
    {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) : waveField A ψ = waveField B ψ := by
  funext x
  obtain ⟨i, hi⟩ := exists_chart A x
  obtain ⟨j, hj⟩ := exists_chart B x
  rw [waveField_chart A hA hψA i hi, waveField_chart B hB hψB j hj,
    CurvedWaveOverlap.wave_germ (metric_germ h i j hi hj) (repr_germ A B i j ψ hi hj)]
  let φ := B.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = B.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have H := CurvedWaveOverlap.wave_pullback_complex (φ := φ) (f := repr B j ψ)
    ((h.smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
    (by simpa only [he] using (hB.metric_smooth j _ ((B.chart j).map_source hj)).differentiableAt (by decide))
    (by simpa only [he] using symmetry_germ B hB j ((B.chart j).map_source hj))
    (by simpa only [he] using hB.negative j _ ((B.chart j).map_source hj))
    (transition_unit h hA i j hi hj)
    (by simpa only [he] using hψB j _ ((B.chart j).map_source hj))
  rw [he] at H
  exact H

/-- The full Hermitian kinetic field is the same for two compatible atlases. -/
theorem kineticField_eq (h : CrossTransition A B) (hA : SmoothLorentz A) (hB : SmoothLorentz B)
    {u f : X → ℂ} (huA : Regular A 2 u) (hfA : Regular A 2 f)
    (huB : Regular B 2 u) (hfB : Regular B 2 f) : kineticField A u f = kineticField B u f := by
  funext x
  obtain ⟨i, hi⟩ := exists_chart A x
  obtain ⟨j, hj⟩ := exists_chart B x
  rw [kineticField_chart A hA huA hfA i hi, kineticField_chart B hB huB hfB j hj]
  let φ := B.chart j ∘ (A.chart i).symm
  have he : φ (A.chart i x) = B.chart j x := by simp [φ, (A.chart i).left_inv hi]
  have hk : CurvedFluxGreen.kinetic (A.metric i) (repr A i u) (repr A i f) (A.chart i x) =
      CurvedFluxGreen.kinetic (pullMetric (B.metric j) φ (fderiv ℝ φ))
        (repr B j u ∘ φ) (repr B j f ∘ φ) (A.chart i x) := by
    simp only [CurvedFluxGreen.kinetic, (metric_germ h i j hi hj).self_of_nhds,
      (repr_germ A B i j u hi hj).fderiv_eq (𝕜 := ℝ), (repr_germ A B i j f hi hj).fderiv_eq (𝕜 := ℝ), φ]
  rw [hk]
  have H := CurvedKineticCovariance.kinetic_pullback (φ := φ) (B.metric j)
    ((h.smooth i j _ ⟨x, ⟨hi, hj⟩, rfl⟩).differentiableAt (by decide)).hasFDerivAt
    (transition_unit h hA i j hi hj)
    (by simpa only [he] using (huB j _ ((B.chart j).map_source hj)).differentiableAt (by decide))
    (by simpa only [he] using (hfB j _ ((B.chart j).map_source hj)).differentiableAt (by decide))
  rw [he] at H
  exact H

private theorem density_intrinsic (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (x : X) :
    kgDensityField p A ψ x = p.hbar ^ 2 * (kineticField A ψ ψ x).re -
      (p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 / 6 * scalarField A x) * Complex.normSq (ψ x) := by
  obtain ⟨i, hi⟩ := exists_chart A x
  rw [kgDensityField_chart p A hA hψ i hi, kineticField_chart A hA hψ hψ i hi, scalarField_chart A hA i hi]
  simp only [CurvedPolarAction.kgDensity, CurvedKineticCovariance.actionDensity, CurvedPolarAction.massTerm,
    repr_chart A i ψ hi]

/-- The computed global complex action density is independent of which compatible metric atlas represents it. -/
theorem kgDensityField_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    kgDensityField p A ψ = kgDensityField p B ψ := by
  funext x
  rw [density_intrinsic p A hA hψA, density_intrinsic p B hB hψB,
    kineticField_eq h hA hB hψA hψA hψB hψB, scalarField_eq h hA hB]

variable [MeasurableSpace X] [BorelSpace X]

/-- The actual constructed metric measures coincide by cross-atlas Jacobian change of variables. -/
theorem measure_eq (h : CrossTransition A B) : A.measure = B.measure :=
  A.measure_independent B (fun i j => fderiv ℝ (B.chart j ∘ (A.chart i).symm))
    (fun i j y hy => ((h.smooth i j y hy).differentiableAt (by decide)).hasFDerivAt)
    h.metric

/-- Integrating the complex-field density gives the same global action in any compatible regular metric atlas. -/
theorem kgAction_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    kgAction p A ψ = kgAction p B ψ := by
  rw [kgAction, kgAction, kgDensityField_eq p h hA hB hψA hψB, measure_eq h]

/-- The global density-action-phase action is equally independent of a compatible metric atlas. -/
theorem hydroAction_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ρ S : X → ℝ} (hρA : Regular A 2 ρ) (hSA : Regular A 2 S)
    (hρB : Regular B 2 ρ) (hSB : Regular B 2 S) (hp : ∀ x, 0 < ρ x) :
    hydroAction p A ρ S = hydroAction p B ρ S := by
  rw [← action_eq p A hA hρA hSA hp, ← action_eq p B hB hρB hSB hp]
  exact kgAction_eq p h hA hB (regular_actionField A p hρA hSA hp) (regular_actionField B p hρB hSB hp)

end FoliationQM.CurvedAtlasIndependence
