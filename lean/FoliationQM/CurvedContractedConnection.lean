module

public import FoliationQM.CurvedMetricDerivatives

/-!
# Divergence of the densitized inverse metric

Expanding the scalar wave operator of v13 gives a coefficient for each first
derivative of the scalar field. Differentiating the volume and the inverse
metric and summing over the divergence index cancels the connection trace.
The remaining coefficient is the negative metric contraction of the
Levi-Civita connection.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedContractedConnection

open LorentzMatrixGroup RNCCoordinateConnection RNCVolumeDensity Filter
open scoped Topology Matrix.Norms.Operator

/-- In any finite dimension the trace from the volume derivative cancels the trace
from the inverse-metric derivative by symmetry of the metric and torsion freedom. -/
theorem cancel_connection_trace {I : Type*} [Fintype I] (A : Matrix I I ℝ)
    (Γ : I → I → I → ℝ) (hA : A.IsSymm) (hΓ : ∀ i j k, Γ i j k = Γ i k j) (j : I) :
    (∑ i : I, (A i j * (∑ k : I, Γ k i k) - ∑ k : I, (A i k * Γ j i k + A j k * Γ i i k))) =
      -(∑ i : I, ∑ k : I, A i k * Γ j i k) := by
  have ht : (∑ i : I, A i j * ∑ k : I, Γ k i k) = ∑ i : I, ∑ k : I, A j k * Γ i i k := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
      rw [hA.apply j k, hΓ i k i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ht]
  ring

variable {g : Covector → Mat4} {x : Covector}

/-- The first partial of each entry of the densitized inverse metric follows by the
product rule on the actual volume factor and inverse matrix. -/
theorem density_inverse_partial (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hd : (g x).det < 0) (a i j : Fin 4) :
    fderiv ℝ (fun y => volumeFactor (g y) * (g y)⁻¹ i j) x (axis a) =
      volumeFactor (g x) * ((g x)⁻¹ i j * (∑ r, christoffel g x r a r) -
        ∑ r, ((g x)⁻¹ i r * christoffel g x j a r + (g x)⁻¹ j r * christoffel g x i a r)) := by
  let entry : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hu := (g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd.ne)
  have hv : DifferentiableAt ℝ (volumeFactor ∘ g) x :=
    (RNCMetricHalfDensity.volume_smooth hd 1).differentiableAt_one.comp x hg
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    entry.differentiableAt.comp x ((LorentzCayleySmooth.contDiffAt_inverse 1 hu).differentiableAt_one.comp x hg)
  change fderiv ℝ (fun y => (volumeFactor ∘ g) y * (g y)⁻¹ i j) x (axis a) = _
  rw [fderiv_fun_mul hv hi]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply,
    CurvedMetricDerivatives.volume_partial hg hs hd, CurvedMetricDerivatives.inverse_partial hg hs hd]
  ring

/-- The divergence of the densitized inverse metric divided by the volume is the negative contracted Christoffel symbol. -/
theorem contracted_connection (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hd : (g x).det < 0) (j : Fin 4) :
    (volumeFactor (g x))⁻¹ * (∑ i, fderiv ℝ (fun y => volumeFactor (g y) * (g y)⁻¹ i j) x (axis i)) =
      -(∑ i, ∑ k, (g x)⁻¹ i k * christoffel g x j i k) := by
  have hv : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr hd)).ne'
  simp only [density_inverse_partial hg hs hd, ← Finset.mul_sum, inv_mul_cancel_left₀ hv]
  exact cancel_connection_trace (g x)⁻¹ (christoffel g x) (mem_of_mem_nhds hs).inv
    (christoffel_symmetric (dG_isSymm hg hs)) j

end FoliationQM.CurvedContractedConnection
