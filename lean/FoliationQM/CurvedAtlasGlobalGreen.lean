module

public import FoliationQM.CurvedAtlasCompactIntegrability
public import FoliationQM.CurvedAtlasResidualPair

/-!
# Global Green identity for arbitrary compact variations

The finite smooth partition is applied to the first argument of the
polarized action density. Each term has an actual coordinate integration
by parts and an integrable residual pairing. Their finite sum proves the
global identity for every compact C² test, including tests spanning charts.
This supplies the integrated analytic bridge for v13 `thm:conformal_coupling`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasGlobalGreen

open Set MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasCross
  CurvedAtlasCompactPartition CurvedAtlasCompactIntegrability CurvedAtlasResidualPair
open scoped Topology Matrix.Norms.Operator Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]

/-- The global mixed density and residual obey Green's identity for a zero-extended compact coordinate test. -/
theorem integral_green_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {ζ : Covector → ℂ}
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    (∫ x, crossField p A (CurvedAtlasTests.extend A i ζ) ψ x ∂A.measure) =
      -(∫ x, pairField p A (CurvedAtlasTests.extend A i ζ) ψ x ∂A.measure) := by
  rw [integral_cross_extended p A hA hψ i hζ hc hs, integral_pair_extended p A hA hψ i ζ]
  exact CurvedKGTestResidual.integral_cross_residual p (hζ.of_le (by decide)) hc hs
    (hA.metric_smooth i) (hA.negative i) (hψ i)

variable [ChartedSpace Covector X] [IsManifold 𝓘(ℝ, Covector) ∞ X] [SecondCountableTopology X]

/-- Pairing a regular residual with any compact C² global variation is absolutely integrable. -/
theorem integrable_pair (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (hc : HasCompactSupport η) :
    Integrable (pairField p A η ψ) A.measure := by
  classical
  obtain ⟨s, θ, hθ, he⟩ := exists_coordinate_decomposition A hcharts hη hc
  rw [he, pairField_sum]
  convert integrable_finsetSum s (fun i _ =>
    integrable_pair_extended p A hA hψ i (hθ i).1 (hθ i).2.1 (hθ i).2.2.1) using 1
  funext x
  exact Finset.sum_apply x s (fun i => pairField p A (CurvedAtlasTests.extend A i (θ i)) ψ)

/-- The actual assembled metric integral satisfies Green's identity for every compact C² global variation. -/
theorem integral_green (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (hc : HasCompactSupport η) :
    (∫ x, crossField p A η ψ x ∂A.measure) =
      -(∫ x, pairField p A η ψ x ∂A.measure) := by
  classical
  obtain ⟨s, θ, hθ, he⟩ := exists_coordinate_decomposition A hcharts hη hc
  have hcross : crossField p A η ψ =
      ∑ i ∈ s, crossField p A (CurvedAtlasTests.extend A i (θ i)) ψ := by
    rw [he, crossField_sum_left p A hA s (fun i _ => (hθ i).2.2.2.1) hψ]
  have hpair : pairField p A η ψ =
      ∑ i ∈ s, pairField p A (CurvedAtlasTests.extend A i (θ i)) ψ := by
    rw [he, pairField_sum]
  rw [hcross, hpair]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum s (fun i _ =>
      integrable_cross_extended p A hA hψ i (hθ i).1 (hθ i).2.1 (hθ i).2.2.1),
    integral_finsetSum s (fun i _ =>
      integrable_pair_extended p A hA hψ i (hθ i).1 (hθ i).2.1 (hθ i).2.2.1),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_green_extended p A hA hψ i (hθ i).1 (hθ i).2.1 (hθ i).2.2.1)

/-- The real part of the global Green identity gives the sign and coefficient of the real first variation. -/
theorem integral_green_re (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (hc : HasCompactSupport η) :
    (∫ x, (crossField p A η ψ x).re ∂A.measure) =
      -(∫ x, (pairField p A η ψ x).re ∂A.measure) := by
  calc
    _ = (∫ x, crossField p A η ψ x ∂A.measure).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (integrable_cross p A hA hcharts hη hψ hc)
    _ = -(∫ x, pairField p A η ψ x ∂A.measure).re :=
      congrArg Complex.re (integral_green p A hA hcharts hη hψ hc)
    _ = _ := by
      apply congrArg Neg.neg
      simpa only [RCLike.re_eq_complex_re] using (integral_re (integrable_pair p A hA hcharts hη hψ hc)).symm



end FoliationQM.CurvedAtlasGlobalGreen
