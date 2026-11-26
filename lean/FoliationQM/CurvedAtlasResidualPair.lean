module

public import FoliationQM.CurvedAtlasCross

/-!
# Global residual testing through actual coordinate integrals

The Euler–Lagrange residual is the squared action scale times the descended
Klein–Gordon operator. Its pairing with a compact coordinate test has the
same integral under the assembled metric measure as the coordinate
residual pairing. Compact support supplies absolute integrability.
This is a component of v13 `thm:conformal_coupling`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasResidualPair

open Set Filter MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent
  CurvedAtlasAction CurvedAtlasCross RNCVolumeDensity
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X]

/-- The actual global Euler–Lagrange residual with the unnormalized action scale. -/
def residualField (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) (x : X) : ℂ :=
  p.hbar ^ 2 • kgOperatorField p A ψ x

/-- Every metric chart computes the same unnormalized residual. -/
theorem residualField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    residualField p A ψ x = CurvedKGTestResidual.residual p (A.metric i) (repr A i ψ) (A.chart i x) := by
  rw [residualField, kgOperatorField_chart p A hA hψ i hx]
  exact (CurvedKGTestResidual.residual_eq_smul_operator p (A.metric i) _ _).symm

/-- The global residual can vanish exactly when the normalized Klein–Gordon operator vanishes. -/
theorem residualField_zero_iff (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) (x : X) :
    residualField p A ψ x = 0 ↔ kgOperatorField p A ψ x = 0 := by
  rw [residualField, smul_eq_zero]
  simp [p.hbar_pos.ne']


/-- The conjugate test paired pointwise with the global Euler–Lagrange residual. -/
def pairField (p : MassiveParameters) (A : MetricAtlas X) (η ψ : X → ℂ) (x : X) : ℂ :=
  star (η x) * residualField p A ψ x

/-- Residual pairing distributes over any finite sum of test fields. -/
theorem pairField_sum {ι : Type*} (p : MassiveParameters) (A : MetricAtlas X)
    (s : Finset ι) (η : ι → X → ℂ) (ψ : X → ℂ) :
    pairField p A (∑ i ∈ s, η i) ψ = ∑ i ∈ s, pairField p A (η i) ψ := by
  classical
  funext x
  simp [pairField, Finset.sum_apply, Finset.sum_mul]

/-- The residual pairing is supported wherever its test field is nonzero. -/
theorem pairField_support (p : MassiveParameters) (A : MetricAtlas X) (η ψ : X → ℂ) :
    Function.support (pairField p A η ψ) ⊆ Function.support η := by
  intro x hx
  by_contra hn
  exact hx (by simp [pairField, show η x = 0 from not_ne_iff.mp hn])

/-- In the chart target a zero-extended test pairs with the literal coordinate residual. -/
theorem pairField_extended_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) (ζ : Covector → ℂ)
    {y : Covector} (hy : y ∈ (A.chart i).target) :
    pairField p A (CurvedAtlasTests.extend A i ζ) ψ ((A.chart i).symm y) =
      star (ζ y) * CurvedKGTestResidual.residual p (A.metric i) (repr A i ψ) y := by
  rw [pairField, residualField_chart p A hA hψ i ((A.chart i).map_target hy),
    CurvedAtlasTests.extend_apply A i ζ ((A.chart i).map_target hy), (A.chart i).right_inv hy]

variable [MeasurableSpace X] [BorelSpace X]

/-- The residual test integral under the assembled metric measure is its actual coordinate integral. -/
theorem integral_pair_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) (ζ : Covector → ℂ) :
    (∫ x, pairField p A (CurvedAtlasTests.extend A i ζ) ψ x ∂A.measure) =
      ∫ y in (A.chart i).target, volumeFactor (A.metric i y) •
        (star (ζ y) * CurvedKGTestResidual.residual p (A.metric i) (repr A i ψ) y) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (A.chart i).source) (fun x hx => ?_)]
  · rw [CurvedChartIntegration.integral_chart A i _
      (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)]
    exact setIntegral_congr_fun (A.chart i).open_target.measurableSet
      (fun y hy => congrArg (volumeFactor (A.metric i y) • ·) (pairField_extended_chart p A hA hψ i ζ hy))
  · simp only [pairField, CurvedAtlasTests.extend_zero A i ζ hx, star_zero, zero_mul]

/-- A compact smooth coordinate test has an absolutely integrable global residual pairing. -/
theorem integrable_pair_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {ζ : Covector → ℂ}
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    Integrable (pairField p A (CurvedAtlasTests.extend A i ζ) ψ) A.measure := by
  have hsupport : Function.support (pairField p A (CurvedAtlasTests.extend A i ζ) ψ) ⊆
      (A.chart i).source := by
    intro x hx
    by_contra hn
    exact hx (by simp only [pairField, CurvedAtlasTests.extend_zero A i ζ hn, star_zero, zero_mul])
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply (CurvedChartIntegration.integrable_chart A i _
    (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)).mpr
  have H := (CurvedWeakEquation.integrable_pair
    (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)
    (F := CurvedKGTestResidual.residual p (A.metric i) (repr A i ψ))
    (fun y hy => (CurvedKGTestResidual.residual_continuousAt p
      (hA.metric_smooth i y hy) (hA.negative i y hy) (hψ i y hy)).continuousWithinAt)
    hζ.continuous hc hs).integrableOn (s := (A.chart i).target)
  apply H.congr
  filter_upwards [ae_restrict_mem (A.chart i).open_target.measurableSet] with y hy
  rw [pairField_extended_chart p A hA hψ i ζ hy]
  rfl

end FoliationQM.CurvedAtlasResidualPair
