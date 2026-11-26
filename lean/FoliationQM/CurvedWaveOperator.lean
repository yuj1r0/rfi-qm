module

public import FoliationQM.CurvedWaveDivergence
public import FoliationQM.CurvedContractedConnection

/-!
# The covariant wave operator in an arbitrary Lorentz coordinate chart

For a scalar field the covariant Hessian subtracts the coordinate
Levi-Civita coefficient acting on the first derivative. Contracting this
Hessian with the inverse metric equals the metric-volume divergence in
Theorem 9.2. Real and complex fields use the same real differentiation.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedWaveOperator

open LorentzMatrixGroup RNCCoordinateConnection CurvedWaveDivergence
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The covariant Hessian of a scalar field, written in a coordinate basis. -/
def covariantHessian (g : Covector → Mat4) (f : Covector → F) (x : Covector) (i j : Fin 4) : F :=
  fderiv ℝ (fderiv ℝ f) x (axis i) (axis j) -
    ∑ k, christoffel g x k i j • fderiv ℝ f x (axis k)

/-- Contracting the covariant scalar Hessian with the actual inverse metric. -/
def hessianTrace (g : Covector → Mat4) (f : Covector → F) (x : Covector) : F :=
  ∑ i, ∑ j, (g x)⁻¹ i j • covariantHessian g f x i j

/-- The Christoffel contribution can be summed by its output index. -/
theorem connection_trace_sum (A : Mat4) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (v : Fin 4 → F) :
    (∑ i, ∑ j, A i j • ∑ k, Γ k i j • v k) =
      ∑ k, (∑ i, ∑ j, A i j * Γ k i j) • v k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  calc
    _ = ∑ i, ∑ k, ∑ j, (A i j * Γ k i j) • v k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The inverse-metric trace separates into the ordinary second derivative and the contracted connection term. -/
theorem hessianTrace_expand (g : Covector → Mat4) (f : Covector → F) (x : Covector) :
    hessianTrace g f x = (∑ i, ∑ j, (g x)⁻¹ i j • fderiv ℝ (fderiv ℝ f) x (axis i) (axis j)) -
      ∑ k, (∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x k i j) • fderiv ℝ f x (axis k) := by
  simp only [hessianTrace, covariantHessian, smul_sub, Finset.sum_sub_distrib, connection_trace_sum]

variable {g : Covector → Mat4} {f : Covector → F} {x : Covector}

/-- The metric-volume divergence of the gradient is the covariant Hessian trace in general coordinates. -/
theorem wave_eq_hessianTrace (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hneg : (g x).det < 0) (hf : ContDiffAt ℝ 2 f x) :
    wave g f x = hessianTrace g f x := by
  have hd (k : Fin 4) : drift g x k = -(∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x k i j) :=
    CurvedContractedConnection.contracted_connection hg hs hneg k
  rw [wave_expansion hg hneg hf, hessianTrace_expand]
  simp only [hd, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

/-- Torsion symmetry and commutation of the scalar field's second derivatives give a symmetric covariant Hessian. -/
theorem hessian_symmetric (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hf : ContDiffAt ℝ 2 f x) (i j : Fin 4) :
    covariantHessian g f x i j = covariantHessian g f x j i := by
  have hc (k : Fin 4) := christoffel_symmetric (dG_isSymm hg hs) k i j
  simp only [covariantHessian, hc, hf.isSymmSndFDerivAt (by simp) (axis i) (axis j)]

/-- At a radial normal center only the ordinary mixed second derivative survives in the covariant Hessian. -/
theorem hessian_center (hg : RNCNormalChart.IsNormal g) (hd : DifferentiableAt ℝ g 0)
    (f : Covector → F) (i j : Fin 4) :
    covariantHessian g f 0 i j = fderiv ℝ (fderiv ℝ f) 0 (axis i) (axis j) := by
  simp only [covariantHessian, RNCNormalChart.connection_zero hg hd, zero_smul,
    Finset.sum_const_zero, sub_zero]

end FoliationQM.CurvedWaveOperator
