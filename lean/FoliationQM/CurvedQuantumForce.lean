module

public import FoliationQM.CurvedQuantumVelocity
public import FoliationQM.CurvedMassDefectRegularity

/-!
# The exact unnormalized quantum force of a curved KG solution

For v13 Proposition 9.4, the velocity is the actual raised phase gradient
scaled by the negative inverse constant mass. Its metric square is fixed
by the real part of KG. The covariant force uses the field equation on a
neighborhood, so differentiating the mass shell is justified. The defect
is the computed wave-and-curvature expression, with its C¹ regularity
derived from that equation. Future direction and normalization belong to
the subsequent positive-timelike theorem.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedQuantumForce

open LorentzMatrixGroup RNCHalfDensityJet CurvedScalarGradient CurvedQuantumVelocity
  CurvedCovariantDerivative CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- The actual constant-mass phase velocity has exactly the KG mass-defect metric square. -/
theorem mass_shell (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    form (g x) (velocity p g S x) (velocity p g S x) =
      p.c ^ 2 * (1 + defect p g R x) := by
  rw [form_velocity_self p (isUnit_iff_ne_zero.mpr hd.ne) S]
  exact CurvedPolarKG.mass_shell p hg hd hs hR hS hp hKG

/-- For a positive polar KG solution, positivity of the velocity's metric square is equivalent to positivity of one plus the computed defect. -/
theorem metric_positive_iff (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    0 < form (g x) (velocity p g S x) (velocity p g S x) ↔ 0 < 1 + defect p g R x := by
  rw [mass_shell p hg hd hs hR hS hp hKG]
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos p.c_pos)

/-- A genuine KG solution germ gives the exact unnormalized covariant force for the actual quantum mass defect. -/
theorem unnormalized_force (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    acceleration g (velocity p g S) x = (p.c ^ 2 / 2) • grad g (defect p g R) x := by
  rw [CurvedQuantumVelocity.acceleration_eq p (hg.differentiableAt (by decide)) hs
    (isUnit_iff_ne_zero.mpr hd.ne) hS,
    CurvedMassDefectRegularity.grad_defect p hg hd hs hR hS hp hKG, smul_smul]
  have hc : (1 / (2 * p.m ^ 2) : ℝ) = (p.c ^ 2 / 2) * (p.m ^ 2 * p.c ^ 2)⁻¹ := by
    field_simp [p.m_pos.ne', p.c_pos.ne']
  rw [hc]

/-- Lowering the force index with the actual metric recovers half the squared light speed times the actual defect differential. -/
theorem force_lowered (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (v : Covector) :
    form (g x) v (acceleration g (velocity p g S) x) =
      p.c ^ 2 / 2 * fderiv ℝ (defect p g R) x v := by
  rw [unnormalized_force p hg hd hs hR hS hp hKG, map_smul, smul_eq_mul,
    form_gradient (isUnit_iff_ne_zero.mpr hd.ne)]

/-- Every component of the actual covariant acceleration equals the full inverse-metric contraction of the computed defect derivative. -/
theorem force_components (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (a : Fin 4) :
    acceleration g (velocity p g S) x a = p.c ^ 2 / 2 *
      ∑ b, (g x)⁻¹ a b * fderiv ℝ (defect p g R) x (RNCCoordinateConnection.axis b) := by
  rw [unnormalized_force p hg hd hs hR hS hp hKG]
  rfl

variable {U : Set Covector}

/-- On an actual regular open solution domain, the constant-mass velocity has the exact defect-dependent mass shell at every point. -/
theorem mass_shell_on (p : MassiveParameters) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) (hd : ∀ y ∈ U, (g y).det < 0)
    (hs : ∀ y ∈ U, (g y).IsSymm) (hR : ContDiffOn ℝ 2 R U)
    (hS : ContDiffOn ℝ 2 S U) (hp : ∀ y ∈ U, 0 < R y)
    (hKG : ∀ y ∈ U, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    ∀ x ∈ U, form (g x) (velocity p g S x) (velocity p g S x) =
      p.c ^ 2 * (1 + defect p g R x) := by
  intro x hx
  have hn := hU.mem_nhds hx
  exact mass_shell p (((hg x hx).contDiffAt hn).differentiableAt (by decide)) (hd x hx) (hs x hx)
    ((hR x hx).contDiffAt hn) ((hS x hx).contDiffAt hn) (hp x hx) (hKG x hx)

/-- The full unnormalized quantum-force identity holds at every point of the stated open KG solution domain. -/
theorem unnormalized_force_on (p : MassiveParameters) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) (hd : ∀ y ∈ U, (g y).det < 0)
    (hs : ∀ y ∈ U, (g y).IsSymm) (hR : ContDiffOn ℝ 2 R U)
    (hS : ContDiffOn ℝ 2 S U) (hp : ∀ y ∈ U, 0 < R y)
    (hKG : ∀ y ∈ U, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    ∀ x ∈ U, acceleration g (velocity p g S) x =
      (p.c ^ 2 / 2) • grad g (defect p g R) x := by
  intro x hx
  have hn := hU.mem_nhds hx
  exact unnormalized_force p ((hg x hx).contDiffAt hn) (hd x hx)
    (Filter.eventually_of_mem hn hs) ((hR x hx).contDiffAt hn)
    ((hS x hx).contDiffAt hn) (hp x hx) (Filter.eventually_of_mem hn hKG)

end FoliationQM.CurvedQuantumForce
