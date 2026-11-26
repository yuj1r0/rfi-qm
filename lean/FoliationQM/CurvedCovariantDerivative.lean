module

public import FoliationQM.CurvedConnectionComponents

/-!
# Covariant differentiation of actual coordinate vector fields

The derivative is the actual Fréchet derivative plus the coordinate
Koszul connection. The varying-metric product rule, metric compatibility,
and the derivative of the squared metric norm follow from these definitions.
Scalar rescaling retains the derivative of the scalar factor, as required
when normalizing the phase velocity in the quantum-force identity.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCovariantDerivative

open LorentzMatrixGroup RNCCoordinateConnection RNCHalfDensityJet CurvedScalarAtlasOverlap
  CurvedConnectionComponents ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The genuine coordinate covariant derivative of a vector field in one tangent direction. -/
def covDeriv (g : Covector → Mat4) (W : Covector → Covector) (x v : Covector) : Covector :=
  fderiv ℝ W x v + connection g x v (W x)

/-- The genuine covariant acceleration differentiates the vector field in its own direction. -/
def acceleration (g : Covector → Mat4) (W : Covector → Covector) (x : Covector) : Covector :=
  covDeriv g W x (W x)

variable {g : Covector → Mat4} {x : Covector}

/-- Symmetry of the actual metric derivative gives the torsion-free symmetry of the Koszul connection. -/
theorem connection_symmetric (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (u v : Covector) :
    connection g x u v = connection g x v u := by
  unfold connection
  apply congrArg ((g x)⁻¹.mulVec)
  funext i
  rw [koszul_apply, koszul_apply, form_symmetric (dG_isSymm hg hs (axis i)) u v]
  ring

/-- The derivative of the metric on fixed vectors is the sum of its two connection contractions. -/
theorem metric_connection (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det) (v u w : Covector) :
    form (dG g x v) u w = form (g x) (connection g x v u) w +
      form (g x) u (connection g x v w) := by
  rw [form_symmetric hs.self_of_nhds (connection g x v u) w,
    form_connection hu, form_connection hu, koszul_apply, koszul_apply,
    form_symmetric (dG_isSymm hg hs v) w u]
  ring

variable {W Z : Covector → Covector}

/-- Differentiating a varying metric paired with two varying vector fields gives all three actual product-rule terms. -/
theorem metric_derivative (hg : DifferentiableAt ℝ g x)
    (hW : DifferentiableAt ℝ W x) (hZ : DifferentiableAt ℝ Z x) (v : Covector) :
    fderiv ℝ (fun y => form (g y) (W y) (Z y)) x v =
      form (dG g x v) (W x) (Z x) + form (g x) (fderiv ℝ W x v) (Z x) +
        form (g x) (W x) (fderiv ℝ Z x v) := by
  have hm : HasFDerivAt (fun M : Mat4 => formMap M) formMap (g x) := by
    exact ContinuousLinearMap.hasFDerivAt (F := Covector →L[ℝ] Covector →L[ℝ] ℝ) formMap
  have hF : HasFDerivAt (fun y => formMap (g y)) (formMap.comp (fderiv ℝ g x)) x :=
    HasFDerivAt.comp (G := Covector →L[ℝ] Covector →L[ℝ] ℝ) x hm hg.hasFDerivAt
  have hF₁ := hF.clm_apply hW.hasFDerivAt
  have h := hF₁.clm_apply hZ.hasFDerivAt
  have hv := congrArg (fun L : Covector →L[ℝ] ℝ => L v) h.fderiv
  change fderiv ℝ (fun y => form (g y) (W y) (Z y)) x v =
    form (g x) (W x) (fderiv ℝ Z x v) +
      (form (g x) (fderiv ℝ W x v) (Z x) + form (dG g x v) (W x) (Z x)) at hv
  rw [hv]
  ring

/-- The actual coordinate derivative of a metric pairing is the sum of the pairings with the two covariant derivatives. -/
theorem metric_compatibility (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hW : DifferentiableAt ℝ W x) (hZ : DifferentiableAt ℝ Z x) (v : Covector) :
    fderiv ℝ (fun y => form (g y) (W y) (Z y)) x v =
      form (g x) (covDeriv g W x v) (Z x) + form (g x) (W x) (covDeriv g Z x v) := by
  rw [metric_derivative hg hW hZ v, metric_connection hg hs hu v (W x) (Z x)]
  simp only [covDeriv, map_add, add_apply]
  ring

/-- The actual derivative of a squared metric norm is twice the metric pairing with the covariant derivative. -/
theorem norm_derivative (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hW : DifferentiableAt ℝ W x) (v : Covector) :
    fderiv ℝ (fun y => form (g y) (W y) (W y)) x v =
      2 * form (g x) (W x) (covDeriv g W x v) := by
  rw [metric_compatibility hg hs hu hW hW v,
    form_symmetric hs.self_of_nhds (covDeriv g W x v) (W x)]
  ring

/-- A constant coordinate vector has precisely its connection term as covariant derivative. -/
theorem covDeriv_const (g : Covector → Mat4) (w x v : Covector) :
    covDeriv g (fun _ => w) x v = connection g x v w := by
  simp only [covDeriv, fderiv_const_apply, zero_apply, zero_add]

/-- The covariant derivative is additive in its tangent direction. -/
theorem covDeriv_direction_add (g : Covector → Mat4) (W : Covector → Covector) (x u v : Covector) :
    covDeriv g W x (u + v) = covDeriv g W x u + covDeriv g W x v := by
  simp only [covDeriv, ← connectionBilin_apply, map_add, add_apply]
  abel

/-- The covariant derivative scales linearly with its tangent direction. -/
theorem covDeriv_direction_smul (g : Covector → Mat4) (W : Covector → Covector) (x v : Covector)
    (a : ℝ) : covDeriv g W x (a • v) = a • covDeriv g W x v := by
  simp only [covDeriv, ← connectionBilin_apply, map_smul, smul_apply, smul_add]

/-- Differentiable vector fields add under the actual covariant derivative. -/
theorem covDeriv_add (g : Covector → Mat4) (hW : DifferentiableAt ℝ W x)
    (hZ : DifferentiableAt ℝ Z x) (v : Covector) :
    covDeriv g (fun y => W y + Z y) x v = covDeriv g W x v + covDeriv g Z x v := by
  simp only [covDeriv, fderiv_fun_add hW hZ, add_apply, ← connectionBilin_apply, map_add]
  abel

/-- A varying scalar contributes its actual directional derivative to the covariant product rule. -/
theorem covDeriv_smul (g : Covector → Mat4) {a : Covector → ℝ}
    (ha : DifferentiableAt ℝ a x) (hW : DifferentiableAt ℝ W x) (v : Covector) :
    covDeriv g (fun y => a y • W y) x v =
      fderiv ℝ a x v • W x + a x • covDeriv g W x v := by
  simp only [covDeriv, fderiv_fun_smul ha hW, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ← connectionBilin_apply, map_smul, smul_add]
  abel

/-- A spacetime-constant scalar has no additional derivative term in the covariant product rule. -/
theorem covDeriv_const_smul (g : Covector → Mat4) (hW : DifferentiableAt ℝ W x)
    (a : ℝ) (v : Covector) :
    covDeriv g (fun y => a • W y) x v = a • covDeriv g W x v := by
  simpa only [fderiv_const_apply, zero_apply, zero_smul, zero_add] using
    covDeriv_smul g (differentiableAt_const a) hW v

/-- The acceleration of a scalar-rescaled vector field retains both the scalar derivative and the squared scalar factor. -/
theorem acceleration_smul (g : Covector → Mat4) {a : Covector → ℝ}
    (ha : DifferentiableAt ℝ a x) (hW : DifferentiableAt ℝ W x) :
    acceleration g (fun y => a y • W y) x =
      (a x * fderiv ℝ a x (W x)) • W x + (a x) ^ 2 • acceleration g W x := by
  rw [acceleration, covDeriv_smul g ha hW, covDeriv_direction_smul]
  simp only [map_smul, smul_eq_mul, smul_smul, acceleration, pow_two]

/-- Constant rescaling multiplies the actual covariant acceleration by the square of the scalar. -/
theorem acceleration_const_smul (g : Covector → Mat4) (hW : DifferentiableAt ℝ W x) (a : ℝ) :
    acceleration g (fun y => a • W y) x = a ^ 2 • acceleration g W x := by
  simpa only [fderiv_const_apply, zero_apply, mul_zero, zero_smul, zero_add] using
    acceleration_smul g (differentiableAt_const a) hW

end FoliationQM.CurvedCovariantDerivative
