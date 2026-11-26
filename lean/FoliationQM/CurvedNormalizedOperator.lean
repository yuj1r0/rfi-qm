module

public import FoliationQM.CurvedKGTestResidual

/-!
# The normalized master wave operator with its boundary divergence

In v13 Eq. `eq:master_variational_equivalence` the quadratic action divided
by m²c² appears alongside the complex operator density. Their pointwise
difference is a signed multiple of the actual densitized flux divergence.
Compact interior support removes its integral.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedNormalizedOperator

open MeasureTheory LorentzMatrixGroup RNCCoordinateCurvature CurvedWaveDivergence
  CurvedFluxGreen CurvedGreenBoundary CurvedPolarAction CurvedKGFirstVariation CurvedKGTestResidual
  RNCVolumeDensity
open scoped Matrix.Norms.Operator

/-- The linear operator in the dimensionless master action, written in reduced Compton units. -/
def masterOp (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) : ℂ :=
  (-(p.ellC ^ 2)) • wave g ψ x + (-1 + p.ellC ^ 2 * scalar g x / 6) • ψ x

/-- The squared reduced Compton length is the conversion from the action's kinetic coefficient. -/
theorem ellC_sq (p : MassiveParameters) : p.ellC ^ 2 = p.hbar ^ 2 / (p.m ^ 2 * p.c ^ 2) := by
  simp [MassiveParameters.ellC, div_pow, mul_pow]

/-- The master operator is the negative Euler–Lagrange residual divided by m²c². -/
theorem masterOp_eq_residual (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) :
    masterOp p g ψ x = (-(1 / (p.m ^ 2 * p.c ^ 2))) • residual p g ψ x := by
  rw [masterOp, CurvedKGTestResidual.residual, smul_add, smul_smul, smul_smul, ellC_sq, massTerm]
  congr 2 <;> field_simp [p.m_pos.ne', p.c_pos.ne']
  ring

/-- The normalized linear equation and its unnormalized variational residual have the same zeros. -/
theorem masterOp_zero_iff (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) :
    masterOp p g ψ x = 0 ↔ residual p g ψ x = 0 := by
  rw [masterOp_eq_residual, smul_eq_zero]
  simp [p.m_pos.ne', p.c_pos.ne']

variable {g : Covector → Mat4} {ψ : Covector → ℂ} {x : Covector} {U : Set Covector}

/-- For a symmetric metric the diagonal cross density is exactly real, including the curvature potential. -/
theorem cross_self_complex (p : MassiveParameters) (hs : (g x).IsSymm) (ψ : Covector → ℂ) :
    (kgDensity p g ψ x : ℂ) = cross p g ψ ψ x := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using (cross_self_re p g ψ x).symm
  · have he := congrArg Complex.im (cross_hermitian p hs ψ ψ)
    simp only [Complex.star_def, Complex.conj_im] at he
    simp only [Complex.ofReal_im]
    linarith

/-- The full complex density identity retains the divergence of the conjugate-field flux with its exact coefficient. -/
theorem density_boundary (p : MassiveParameters) (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hs : (g x).IsSymm) (hψ : ContDiffAt ℝ 2 ψ x) :
    volumeFactor (g x) • (star (ψ x) * masterOp p g ψ x) =
      (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ) -
        p.ellC ^ 2 • boundaryDivergence g ψ ψ x := by
  rw [masterOp_eq_residual, cross_self_complex p hs, first_green hg hd (hψ.differentiableAt (by decide)) hψ,
    ellC_sq, CurvedKGTestResidual.residual, cross]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- Restricted-volume integration retains the complex boundary term for a field with no support condition. -/
theorem integral_boundary (p : MassiveParameters) (hU : MeasurableSet U) (hg : ∀ x ∈ U, DifferentiableAt ℝ g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hs : ∀ x ∈ U, (g x).IsSymm) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hA : IntegrableOn (fun x => (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ)) U)
    (hB : IntegrableOn (boundaryDivergence g ψ ψ) U) :
    (∫ x in U, volumeFactor (g x) • (star (ψ x) * masterOp p g ψ x)) =
      (∫ x in U, (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ)) -
        p.ellC ^ 2 • ∫ x in U, boundaryDivergence g ψ ψ x := by
  rw [← integral_smul, ← integral_sub hA (hB.fun_smul (p.ellC ^ 2))]
  exact integral_congr_ae ((ae_restrict_mem hU).mono fun y hy => density_boundary p
    (hg y hy) (hd y hy) (hs y hy) (hψ y hy))

/-- A compact interior field gives an integrable normalized operator density from continuity of the residual. -/
theorem integrable_compact_operator (p : MassiveParameters) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ₂ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    IntegrableOn (fun x => volumeFactor (g x) • (star (ψ x) * masterOp p g ψ x)) U := by
  apply (CurvedWeakEquation.integrable_pair (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (F := masterOp p g ψ) _ hψ.continuous hc hsupp).integrableOn
  intro x hx
  have he := residual_continuousAt p (hg x hx) (hd x hx) (hψ₂ x hx)
  rw [funext (masterOp_eq_residual p g ψ)]
  exact ((continuousAt_const (y := -(1 / (p.m ^ 2 * p.c ^ 2)))).smul he).continuousWithinAt

/-- The quadratic-action side of the compact identity is absolutely integrable under the same hypotheses. -/
theorem integrable_compact_action (p : MassiveParameters) (hU : MeasurableSet U) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hs : ∀ x ∈ U, (g x).IsSymm) (hψ₂ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    IntegrableOn (fun x => (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ)) U := by
  have hi := integrable_cross p hψ hc hsupp hg hd hψ₂
  apply (hi.fun_smul (1 / (p.m ^ 2 * p.c ^ 2))).congr
  filter_upwards [ae_restrict_mem hU] with y hy
  rw [smul_smul, cross_self_complex p (hs y hy)]
  congr 1
  ring

/-- For a compact interior field the normalized complex operator integral equals the quadratic action integral. -/
theorem integral_compact (p : MassiveParameters) (hU : MeasurableSet U) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hs : ∀ x ∈ U, (g x).IsSymm) (hψ₂ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    (∫ x in U, volumeFactor (g x) • (star (ψ x) * masterOp p g ψ x)) =
      ∫ x in U, (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ) := by
  have he := integral_cross_residual p hψ hc hsupp hg hd hψ₂
  have hscaled (y : Covector) : volumeFactor (g y) • (star (ψ y) * masterOp p g ψ y) =
      (-(1 / (p.m ^ 2 * p.c ^ 2))) • (volumeFactor (g y) • (star (ψ y) * residual p g ψ y)) := by
    rw [masterOp_eq_residual, mul_smul_comm, smul_comm]
  simp_rw [hscaled]
  rw [integral_smul, neg_smul, ← smul_neg, ← he, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU] with y hy
  rw [cross_self_complex p (hs y hy), smul_smul]
  congr 1
  ring

end FoliationQM.CurvedNormalizedOperator
