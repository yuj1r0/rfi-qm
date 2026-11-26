module

public import FoliationQM.RNCCoordinateConnection
public import FoliationQM.RNCMetricHalfDensity

/-!
# Coordinate derivatives of metric volume and the inverse metric

For the scalar wave operator of v13, the derivative of its densitized
inverse metric splits into the derivative of the volume factor and that of
the inverse matrix. Jacobi's formula and metric compatibility evaluate both
terms at an arbitrary point of a differentiable symmetric metric.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedMetricDerivatives

open LorentzMatrixGroup RNCCoordinateConnection RNCVolumeDensity

variable {g : Covector → Mat4} {x : Covector}

/-- The matrix of connection coefficients for a fixed coordinate direction. -/
def connectionMatrix (g : Covector → Mat4) (x : Covector) (a : Fin 4) : Mat4 :=
  fun r b => christoffel g x r a b

/-- Metric compatibility in matrix form at an arbitrary regular chart point. -/
theorem metric_partial_matrix (hg : DifferentiableAt ℝ g x) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hu : IsUnit (g x)) (a : Fin 4) :
    dG g x (axis a) = (connectionMatrix g x a).transpose * g x + g x * connectionMatrix g x a := by
  ext b c
  rw [metric_compatibility hu (dG_isSymm hg hs)]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [hs.self_of_nhds.apply r c, mul_comm]

/-- The variation of the log-volume trace is twice the Christoffel trace
before multiplication by the Jacobi factor one half. -/
theorem trace_metric_partial (hg : DifferentiableAt ℝ g x) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hu : IsUnit (g x)) (a : Fin 4) :
    ((g x)⁻¹ * dG g x (axis a)).trace = 2 * ∑ r, christoffel g x r a r := by
  let C := connectionMatrix g x a
  have hdet := (g x).isUnit_iff_isUnit_det.mp hu
  have hl : ((g x)⁻¹ * (C.transpose * g x)).trace = C.trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (g x), ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.trace_transpose]
  rw [metric_partial_matrix hg hs hu a, Matrix.mul_add, Matrix.trace_add, hl,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  change (∑ r, christoffel g x r a r) + _ = _
  exact (two_mul _).symm

/-- The true coordinate derivative of the volume density equals its Christoffel trace. -/
theorem volume_partial (hg : DifferentiableAt ℝ g x) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hd : (g x).det < 0) (a : Fin 4) :
    fderiv ℝ (volumeFactor ∘ g) x (axis a) = volumeFactor (g x) * ∑ r, christoffel g x r a r := by
  rw [fderiv_comp x (RNCMetricHalfDensity.volume_smooth hd 1).differentiableAt_one hg,
    ContinuousLinearMap.comp_apply]
  calc
    _ = volumeFactor (g x) / 2 * ((g x)⁻¹ * dG g x (axis a)).trace :=
      RNCMetricHalfDensity.volume_differential hd _
    _ = _ := by
      rw [trace_metric_partial hg hs ((g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd.ne))]
      ring

/-- The derivative of inversion for an arbitrary invertible real metric matrix. -/
theorem inverse_differential (hg : DifferentiableAt ℝ g x) (hu : IsUnit (g x)) (v : Covector) :
    fderiv ℝ (fun y => (g y)⁻¹) x v = -((g x)⁻¹ * fderiv ℝ g x v * (g x)⁻¹) := by
  have hi (A : Mat4) (hA : IsUnit A) : HasFDerivAt (fun B : Mat4 => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Mat4 A⁻¹ A⁻¹) A := by
    obtain ⟨u, rfl⟩ := hA
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  exact congrArg (fun L : Covector →L[ℝ] Mat4 => L v) ((hi _ hu).comp x hg.hasFDerivAt).fderiv

/-- Raising the two metric indices gives the inverse-metric compatibility equation. -/
theorem inverse_partial_matrix (hg : DifferentiableAt ℝ g x) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hu : IsUnit (g x)) (a : Fin 4) :
    fderiv ℝ (fun y => (g y)⁻¹) x (axis a) =
      -((g x)⁻¹ * (connectionMatrix g x a).transpose + connectionMatrix g x a * (g x)⁻¹) := by
  have hdet := (g x).isUnit_iff_isUnit_det.mp hu
  rw [inverse_differential hg hu]
  change -((g x)⁻¹ * dG g x (axis a) * (g x)⁻¹) = _
  rw [metric_partial_matrix hg hs hu, Matrix.mul_add, Matrix.add_mul]
  congr 2
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  · rw [← Matrix.mul_assoc (g x)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- Each actual derivative of an inverse-metric entry is the negative sum of the
two raised connection terms. -/
theorem inverse_partial (hg : DifferentiableAt ℝ g x) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hd : (g x).det < 0) (a i j : Fin 4) :
    fderiv ℝ (fun y => (g y)⁻¹ i j) x (axis a) =
      -(∑ r, ((g x)⁻¹ i r * christoffel g x j a r + (g x)⁻¹ j r * christoffel g x i a r)) := by
  let entry : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hu := (g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd.ne)
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x :=
    (LorentzCayleySmooth.contDiffAt_inverse 1 hu).differentiableAt_one.comp x hg
  change fderiv ℝ (entry ∘ (fun y => (g y)⁻¹)) x (axis a) = _
  have he : fderiv ℝ (entry ∘ (fun y => (g y)⁻¹)) x (axis a) =
      entry (fderiv ℝ (fun y => (g y)⁻¹) x (axis a)) :=
    congrArg (fun L : Covector →L[ℝ] ℝ => L (axis a)) (entry.hasFDerivAt.comp x hi.hasFDerivAt).fderiv
  rw [he, inverse_partial_matrix hg hs hu]
  change -((_ * _ + _ * _ : Mat4) i j) = _
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix,
    Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  rw [hs.self_of_nhds.inv.apply j r, mul_comm]

end FoliationQM.CurvedMetricDerivatives
