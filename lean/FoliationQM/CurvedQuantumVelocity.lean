module

public import FoliationQM.CurvedGradientHessian
public import FoliationQM.Conventions

/-!
# The actual phase velocity and its covariant acceleration

The velocity follows v13's convention `w = -grad S / m`, with fixed positive
mass. Its metric square and acceleration are derived from the actual raised
phase differential and Koszul connection. These statements do not assume a
Klein–Gordon equation, amplitude, or prescribed mass defect.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumVelocity

open LorentzMatrixGroup RNCCoordinateConnection RNCHalfDensityJet CurvedGradientCovariance
  CurvedScalarGradient CurvedCovariantDerivative CurvedGradientHessian
open scoped Topology Matrix.Norms.Operator

/-- The physical phase velocity is the negative actual metric gradient divided by the fixed mass. -/
def velocity (p : MassiveParameters) (g : Covector → Mat4) (S : Covector → ℝ)
    (x : Covector) : Covector :=
  -(1 / p.m) • grad g S x

/-- Every component of the phase velocity includes the full inverse-metric contraction with the genuine differential. -/
theorem velocity_components (p : MassiveParameters) (g : Covector → Mat4)
    (S : Covector → ℝ) (x : Covector) (a : Fin 4) :
    velocity p g S x a =
      -(∑ b, (g x)⁻¹ a b * fderiv ℝ S x (axis b)) / p.m := by
  change -(1 / p.m) * (∑ b, (g x)⁻¹ a b * fderiv ℝ S x (axis b)) = _
  ring

variable {g : Covector → Mat4} {S : Covector → ℝ} {x : Covector}

/-- Lowering the phase velocity gives minus the actual action differential divided by the mass. -/
theorem form_velocity (p : MassiveParameters) (hu : IsUnit (g x).det) (u : Covector) :
    form (g x) u (velocity p g S x) = -fderiv ℝ S x u / p.m := by
  rw [velocity, map_smul, smul_eq_mul, form_gradient hu]
  ring

/-- The velocity's indefinite metric square is the phase-gradient pairing divided by the squared mass. -/
theorem form_velocity_self (p : MassiveParameters) (hu : IsUnit (g x).det)
    (S : Covector → ℝ) :
    form (g x) (velocity p g S x) (velocity p g S x) = pairing g S S x / p.m ^ 2 := by
  simp only [velocity, map_smul, smul_apply, smul_eq_mul, form_grad_self hu S]
  ring

/-- A differentiable nonsingular metric and locally C² action phase give a differentiable actual phase velocity. -/
theorem differentiableAt_velocity (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hu : IsUnit (g x).det) (hS : ContDiffAt ℝ 2 S x) :
    DifferentiableAt ℝ (velocity p g S) x :=
  (differentiableAt_grad hg hu hS).const_smul (-(1 / p.m))

/-- A locally C¹ nonsingular metric and locally C² action phase give a locally C¹ phase velocity. -/
theorem contDiffAt_velocity (p : MassiveParameters) (hg : ContDiffAt ℝ 1 g x)
    (hu : IsUnit (g x).det) (hS : ContDiffAt ℝ 2 S x) :
    ContDiffAt ℝ 1 (velocity p g S) x :=
  (contDiffAt_grad hg hu hS).const_smul (-(1 / p.m))

/-- Actual covariant differentiation of the phase velocity gives the raised derivative of its phase-gradient square with coefficient `1/(2m²)`. -/
theorem acceleration_eq (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hS : ContDiffAt ℝ 2 S x) :
    acceleration g (velocity p g S) x =
      (1 / (2 * p.m ^ 2)) • grad g (pairing g S S) x := by
  change acceleration g (fun y => -(1 / p.m) • grad g S y) x = _
  rw [acceleration_const_smul g (differentiableAt_grad hg hu hS),
    acceleration_grad hg hs hu hS, smul_smul]
  congr 1
  field_simp [p.m_pos.ne']

/-- The coordinate acceleration formula retains every inverse-metric coefficient in the derivative of the phase-gradient square. -/
theorem acceleration_components (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hS : ContDiffAt ℝ 2 S x) (a : Fin 4) :
    acceleration g (velocity p g S) x a = (1 / (2 * p.m ^ 2)) *
      ∑ b, (g x)⁻¹ a b * fderiv ℝ (pairing g S S) x (axis b) := by
  rw [acceleration_eq p hg hs hu hS]
  rfl

end FoliationQM.CurvedQuantumVelocity
