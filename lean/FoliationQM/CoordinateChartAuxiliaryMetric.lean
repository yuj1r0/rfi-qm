module

public import FoliationQM.CoordinateCutoffPullbackEnergy
public import FoliationQM.CurvedScalarAtlasOverlap

/-!
# Prescribed auxiliary metric in chart coordinates

Source: v13 `thm:wallstrom` Part(c), prerequisite to `eq:log_cutoff_l2_bound`,
component kind B. For a continuously differentiable coordinate chart with
continuously differentiable inverse, the two differentials are mutually
inverse, so their determinants are units. Writing a prescribed metric `H` in
chart coordinates by inverse pullback and pulling it forward again recovers `H`
exactly, and continuity and positive definiteness are preserved. Consequently
the `H`-energy of the chart-composed coordinate cutoff on a compact set is
integrable and tends to zero.

The cutoff is a function of the coordinate normal radius in the chart. Its
identification with the auxiliary-metric normal distance `dist_h(x, 𝒩)` of the
source is not asserted here. No chart is assumed isometric or volume preserving.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CoordinateChartAuxiliaryMetric

open Filter MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection RealLorentzFrame
open AuxiliaryMetricEnergy RNCCoordinateVolumeChange SmoothCoordinateTubeCutoff
open scoped Topology Matrix.Norms.Operator ContDiff

variable {e : OpenPartialHomeomorph Covector Covector} {x : Covector}

private theorem isUnit_det_of_comp_eq_id {A B : Covector →L[ℝ] Covector}
    (h : A.comp B = ContinuousLinearMap.id ℝ Covector) : IsUnit B.det := by
  have h' : LinearMap.det (A : Covector →ₗ[ℝ] Covector) *
      LinearMap.det (B : Covector →ₗ[ℝ] Covector) = 1 := by
    rw [← LinearMap.det_comp]
    change LinearMap.det ((A.comp B : Covector →L[ℝ] Covector) : Covector →ₗ[ℝ] Covector) = 1
    rw [h]
    exact LinearMap.det_id
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h')

/-- The chart has its actual derivative at every point of its source. -/
theorem hasFDerivAt (he : ContDiffOn ℝ 1 e e.source) (hx : x ∈ e.source) :
    HasFDerivAt e (fderiv ℝ e x) x :=
  ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt

private theorem differentiableAt_symm (hi : ContDiffOn ℝ 1 e.symm e.target) (hx : x ∈ e.source) :
    DifferentiableAt ℝ e.symm (e x) :=
  (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt one_ne_zero

/-- The differential of the inverse chart is a left inverse of the differential of the chart. -/
theorem fderiv_symm_comp_fderiv (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (hx : x ∈ e.source) :
    (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ Covector := by
  have h : fderiv ℝ (e.symm ∘ e) x = fderiv ℝ id x :=
    Filter.EventuallyEq.fderiv_eq (e.eventually_left_inverse hx)
  rw [fderiv_comp x (differentiableAt_symm hi hx) (hasFDerivAt he hx).differentiableAt,
    fderiv_id] at h
  exact h

/-- The differential of the inverse chart is a right inverse of the differential of the chart. -/
theorem fderiv_comp_fderiv_symm (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (hx : x ∈ e.source) :
    (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x)) = ContinuousLinearMap.id ℝ Covector := by
  have hd : DifferentiableAt ℝ e (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact (hasFDerivAt he hx).differentiableAt
  have h : fderiv ℝ (e ∘ e.symm) (e x) = fderiv ℝ id (e x) :=
    Filter.EventuallyEq.fderiv_eq (e.eventually_right_inverse' hx)
  rw [fderiv_comp (e x) hd (differentiableAt_symm hi hx), fderiv_id, e.left_inv hx] at h
  exact h

/-- The chart differential has unit determinant; this is derived, not assumed. -/
theorem isUnit_det_fderiv (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (hx : x ∈ e.source) :
    IsUnit (fderiv ℝ e x).det :=
  isUnit_det_of_comp_eq_id (fderiv_symm_comp_fderiv he hi hx)

/-- The inverse-chart differential has unit determinant. -/
theorem isUnit_det_fderiv_symm (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (hx : x ∈ e.source) :
    IsUnit (fderiv ℝ e.symm (e x)).det :=
  isUnit_det_of_comp_eq_id (fderiv_comp_fderiv_symm he hi hx)

/-- A source metric written in chart coordinates: its pullback by the inverse chart. -/
def inverseMetric (e : OpenPartialHomeomorph Covector Covector) (H : Covector → Mat4) :
    Covector → Mat4 :=
  pullMetric H e.symm (fderiv ℝ e.symm)

/-- Pulling the chart-coordinate metric back by the chart recovers the prescribed
metric exactly. The metric field is arbitrary. -/
theorem pullMetric_inverseMetric (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (H : Covector → Mat4) (hx : x ∈ e.source) :
    pullMetric (inverseMetric e H) e (fderiv ℝ e) x = H x := by
  have hKJ : jacobianMatrix (fderiv ℝ e.symm (e x)) * jacobianMatrix (fderiv ℝ e x) = 1 := by
    rw [jacobianMatrix, jacobianMatrix, ← LinearMap.toMatrix'_comp]
    change LinearMap.toMatrix' (((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) :
      Covector →L[ℝ] Covector) : Covector →ₗ[ℝ] Covector) = 1
    rw [fderiv_symm_comp_fderiv he hi hx]
    exact LinearMap.toMatrix'_id
  simp only [pullMetric, inverseMetric, pullMatrix, e.left_inv hx]
  calc _ = (jacobianMatrix (fderiv ℝ e.symm (e x)) *
          jacobianMatrix (fderiv ℝ e x)).transpose * H x *
        (jacobianMatrix (fderiv ℝ e.symm (e x)) * jacobianMatrix (fderiv ℝ e x)) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = H x := by rw [hKJ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- Positive definiteness of the prescribed metric passes to chart coordinates. -/
theorem inverseMetric_posDef (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) {H : Covector → Mat4} (hx : x ∈ e.source)
    (hpos : (H x).PosDef) : (inverseMetric e H (e x)).PosDef := by
  have hJ : IsUnit (jacobianMatrix (fderiv ℝ e.symm (e x))).det := by
    rw [det_jacobianMatrix]
    exact isUnit_det_fderiv_symm he hi hx
  have hH : (H (e.symm (e x))).PosDef := by rwa [e.left_inv hx]
  exact AuxiliaryMetricPullback.posDef_pullMatrix hH hJ

/-- Continuity of the prescribed metric on a set in the chart source passes to
chart coordinates on the image set. -/
theorem inverseMetric_continuousOn (hi : ContDiffOn ℝ 1 e.symm e.target)
    {H : Covector → Mat4} {K : Set Covector} (hK : K ⊆ e.source) (hH : ContinuousOn H K) :
    ContinuousOn (inverseMetric e H) (e '' K) := by
  have hsub : e '' K ⊆ e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (hK hy)
  have hJ : ContinuousOn (fun y => jacobianMatrix (fderiv ℝ e.symm y)) (e '' K) :=
    CurvedScalarAtlasOverlap.jacobianMap.continuous.comp_continuousOn
      ((hi.continuousOn_fderiv_of_isOpen e.open_target le_rfl).mono hsub)
  have hHs : ContinuousOn (fun y => H (e.symm y)) (e '' K) := by
    refine hH.comp (e.continuousOn_symm.mono hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa only [e.left_inv (hK hy)] using hy
  have hp : Continuous fun p : Mat4 × Mat4 => pullMatrix p.1 p.2 :=
    ((continuous_fst.matrix_transpose).matrix_mul continuous_snd).matrix_mul continuous_fst
  have key := hp.comp_continuousOn (hJ.prodMk hHs)
  change ContinuousOn
    (fun y => pullMatrix (jacobianMatrix (fderiv ℝ e.symm y)) (H (e.symm y))) (e '' K)
  simpa only [Function.comp_def] using key

/-- Positive `H`-energy density of the differential of the chart-composed coordinate cutoff. -/
def energy (H : Covector → Mat4) (e : OpenPartialHomeomorph Covector Covector) (ε : ℝ)
    (x : Covector) : ℝ :=
  density (H x) * realEnergy (H x) (fun i => fderiv ℝ (profile ε ∘ e) x (axis i))

/-- On the chart source this is the pullback energy of the chart-coordinate metric. -/
theorem pullbackEnergy_inverseMetric (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (H : Covector → Mat4) (hx : x ∈ e.source) (ε : ℝ) :
    CoordinateCutoffPullbackEnergy.energy (inverseMetric e H) e (fderiv ℝ e) ε x =
      energy H e ε x := by
  simp only [CoordinateCutoffPullbackEnergy.energy, energy, pullMetric_inverseMetric he hi H hx]

/-- For a prescribed continuous positive metric on a compact set in the chart
source, the cutoff energy is integrable, nonnegative and bounded by one constant,
chosen before the radius, times the flat coordinate cutoff energy of the image. -/
theorem compact_energy_data (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hKs : K ⊆ e.source) (hH : ContinuousOn H K)
    (hpos : ∀ y ∈ K, (H y).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      IntegrableOn (energy H e ε) K volume ∧
      0 ≤ (∫ y in K, energy H e ε y) ∧
      (∫ y in K, energy H e ε y) ≤ B * (∫ y in e '' K, ‖fderiv ℝ (profile ε) y‖ ^ 2) := by
  obtain ⟨B, hB, hb⟩ := CoordinateCutoffPullbackEnergy.compact_energy_data
    (H := inverseMetric e H) (φ := e) (D := fderiv ℝ e) hK
    (fun y hy => hasFDerivAt he (hKs hy)) (e.injOn.mono hKs)
    (fun y hy => isUnit_det_fderiv he hi (hKs hy))
    (inverseMetric_continuousOn hi hKs hH)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact inverseMetric_posDef he hi (hKs hy) (hpos y hy))
  refine ⟨B, hB, fun {ε} h0 h1 => ?_⟩
  obtain ⟨hint, -, hnn, hle⟩ := hb h0 h1
  have heq : EqOn (CoordinateCutoffPullbackEnergy.energy (inverseMetric e H) e (fderiv ℝ e) ε)
      (energy H e ε) K := fun y hy => pullbackEnergy_inverseMetric he hi H (hKs hy) ε
  have hI := setIntegral_congr_fun (μ := volume) hK.measurableSet heq
  exact ⟨hint.congr_fun heq hK.measurableSet, hI ▸ hnn, hI ▸ hle⟩

/-- The prescribed-metric energy of the chart-composed cutoff on a compact set,
and its square root, tend to zero through positive radii. -/
theorem compact_energy_decay (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hKs : K ⊆ e.source) (hH : ContinuousOn H K)
    (hpos : ∀ y ∈ K, (H y).PosDef) :
    Tendsto (fun ε : ℝ => ∫ y in K, energy H e ε y) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => Real.sqrt (∫ y in K, energy H e ε y)) (𝓝[>] 0) (𝓝 0) := by
  have h := CoordinateCutoffPullbackEnergy.compact_energy_decay
    (H := inverseMetric e H) (φ := e) (D := fderiv ℝ e) hK
    (fun y hy => hasFDerivAt he (hKs hy)) (e.injOn.mono hKs)
    (fun y hy => isUnit_det_fderiv he hi (hKs hy))
    (inverseMetric_continuousOn hi hKs hH)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact inverseMetric_posDef he hi (hKs hy) (hpos y hy))
  have hI : ∀ ε : ℝ,
      (∫ y in K, CoordinateCutoffPullbackEnergy.energy (inverseMetric e H) e (fderiv ℝ e) ε y) =
        ∫ y in K, energy H e ε y := fun ε =>
    setIntegral_congr_fun hK.measurableSet
      fun y hy => pullbackEnergy_inverseMetric he hi H (hKs hy) ε
  simpa only [hI] using h

end FoliationQM.CoordinateChartAuxiliaryMetric
