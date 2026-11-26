module

public import FoliationQM.CurvedCovariantDerivative
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Positive normalization of an actual coordinate vector field

Division by the positive square root of `1 + q` preserves regularity and
the sign of a supplied time-orienting linear functional. Differentiating
the genuine reconstruction `W = √(1 + q) U` gives the exact covariant
acceleration relation, with no assumed force equation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPositiveNormalization

open LorentzMatrixGroup RNCHalfDensityJet CurvedCovariantDerivative
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- Positive square-root normalization of a coordinate vector field. -/
def normalized (W : Covector → Covector) (q : Covector → ℝ) (x : Covector) : Covector :=
  (Real.sqrt (1 + q x))⁻¹ • W x

variable {W Z : Covector → Covector} {q : Covector → ℝ} {x : Covector}

/-- Multiplying the normalized vector by the positive square root recovers the actual vector. -/
theorem reconstruct (W : Covector → Covector) (hp : 0 < 1 + q x) :
    Real.sqrt (1 + q x) • normalized W q x = W x := by
  rw [normalized, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hp).ne', one_smul]

/-- Continuity of the defect makes reconstruction a genuine equality of vector-field germs. -/
theorem reconstruct_germ (W : Covector → Covector) (hq : ContinuousAt q x) (hp : 0 < 1 + q x) :
    (fun y => Real.sqrt (1 + q y) • normalized W q y) =ᶠ[𝓝 x] W := by
  filter_upwards [((continuousAt_const (y := (1 : ℝ))).add hq).eventually (Ioi_mem_nhds hp)] with y hy
  exact reconstruct W hy

/-- A differentiable vector and defect give an actually differentiable normalized vector on the positive region. -/
theorem differentiableAt_normalized (hW : DifferentiableAt ℝ W x) (hq : DifferentiableAt ℝ q x)
    (hp : 0 < 1 + q x) : DifferentiableAt ℝ (normalized W q) x :=
  ((((differentiableAt_const (1 : ℝ)).add hq).sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').fun_smul hW

/-- Positive normalization preserves any given order of local continuous differentiability. -/
theorem contDiffAt_normalized {n : WithTop ℕ∞} (hW : ContDiffAt ℝ n W x) (hq : ContDiffAt ℝ n q x)
    (hp : 0 < 1 + q x) : ContDiffAt ℝ n (normalized W q) x :=
  (((contDiffAt_const.add hq).sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hW

/-- The squared metric norm scales by the reciprocal of the positive normalization factor. -/
theorem form_normalized (g : Covector → Mat4) (hp : 0 < 1 + q x) :
    form (g x) (normalized W q x) (normalized W q x) =
      form (g x) (W x) (W x) / (1 + q x) := by
  simp only [normalized, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hp.le]
  ring

/-- A vector satisfying the scaled mass shell has constant metric norm after positive normalization. -/
theorem form_normalized_of_mass_shell (g : Covector → Mat4) {c : ℝ} (hp : 0 < 1 + q x)
    (hmass : form (g x) (W x) (W x) = c ^ 2 * (1 + q x)) :
    form (g x) (normalized W q x) (normalized W q x) = c ^ 2 := by
  rw [form_normalized g hp, hmass, mul_div_cancel_right₀ _ hp.ne']

/-- A supplied real linear time-orientation test has the same positive sign after normalization. -/
theorem positive_iff (L : Covector →L[ℝ] ℝ) (hp : 0 < 1 + q x) :
    0 < L (normalized W q x) ↔ 0 < L (W x) := by
  rw [normalized, map_smul, smul_eq_mul]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr (Real.sqrt_pos.mpr hp))

/-- Equal vector-field germs have equal genuine covariant accelerations. -/
theorem acceleration_congr (g : Covector → Mat4) (he : W =ᶠ[𝓝 x] Z) :
    acceleration g W x = acceleration g Z x := by
  simp only [acceleration, covDeriv, he.fderiv_eq (𝕜 := ℝ), he.self_of_nhds]

/-- Differentiating the reconstructed field gives the exact acceleration relation for positive normalization. -/
theorem acceleration_relation (g : Covector → Mat4) (hW : DifferentiableAt ℝ W x)
    (hq : DifferentiableAt ℝ q x) (hp : 0 < 1 + q x) :
    (1 + q x) • acceleration g (normalized W q) x +
      (fderiv ℝ q x (normalized W q x) / 2) • normalized W q x = acceleration g W x := by
  have hr : HasFDerivAt (fun y => Real.sqrt (1 + q y))
      ((1 / (2 * Real.sqrt (1 + q x))) • fderiv ℝ q x) x :=
    ((hq.hasFDerivAt.const_add 1).sqrt hp.ne')
  have hU := differentiableAt_normalized hW hq hp
  have hacc := acceleration_smul g hr.differentiableAt hU
  rw [acceleration_congr g (reconstruct_germ W hq.continuousAt hp), hr.fderiv,
    smul_apply, smul_eq_mul, Real.sq_sqrt hp.le] at hacc
  have hc : Real.sqrt (1 + q x) *
      (1 / (2 * Real.sqrt (1 + q x)) * fderiv ℝ q x (normalized W q x)) =
      fderiv ℝ q x (normalized W q x) / 2 := by
    field_simp [(Real.sqrt_pos.mpr hp).ne']
  rw [hc] at hacc
  exact (add_comm _ _).trans hacc.symm

/-- Solving the actual acceleration relation isolates the normalized acceleration without any force assumption. -/
theorem acceleration_normalized (g : Covector → Mat4) (hW : DifferentiableAt ℝ W x)
    (hq : DifferentiableAt ℝ q x) (hp : 0 < 1 + q x) :
    acceleration g (normalized W q) x = (1 + q x)⁻¹ •
      (acceleration g W x - (fderiv ℝ q x (normalized W q x) / 2) • normalized W q x) := by
  have he := acceleration_relation g hW hq hp
  rw [← he, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]

end FoliationQM.CurvedPositiveNormalization
