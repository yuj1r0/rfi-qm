module

public import FoliationQM.CurvedQuantumForce
public import FoliationQM.CurvedPositiveNormalization
public import FoliationQM.CurvedLogGradientProjection
public import FoliationQM.GeometricLorentzNormalization

/-!
# Exact normalized quantum force and geometric future orientation

For v13 Proposition 9.4 and Eq. normalized_quantum_force, the normalized
velocity is the actual constant-mass phase velocity divided by sqrt(1+q).
The square root is differentiated on its positive domain. The previously
proved KG force, the actual normalization product rule and the logarithm
chain rule give the projected acceleration. A supplied genuine Lorentz
frame identifies the geometric future cone, which positive normalization
preserves.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedNormalizedQuantumForce

open LorentzMatrixGroup RNCHalfDensityJet CurvedScalarGradient CurvedQuantumVelocity
  CurvedCovariantDerivative CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential
  CurvedPositiveNormalization CurvedLogGradientProjection

/-- The physical normalized velocity of the actual positive polar solution, on one plus its computed defect greater than zero. -/
def normalizedVelocity (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) : Covector → Covector :=
  normalized (velocity p g S) (defect p g R)

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- The normalized velocity is genuinely C¹ on the positive normalization domain of a KG solution. -/
theorem contDiffAt_normalizedVelocity (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) :
    ContDiffAt ℝ 1 (normalizedVelocity p g R S) x :=
  contDiffAt_normalized (contDiffAt_velocity p (hg.of_le (by decide))
    (isUnit_iff_ne_zero.mpr hd.ne) hS)
    (CurvedMassDefectRegularity.contDiffAt_defect p hg hd hs hR hS hRpos hKG) hqpos

/-- The actual normalized phase velocity has metric square c² wherever the positive polar KG mass shell permits normalization. -/
theorem metric_square (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0)
    (hqpos : 0 < 1 + defect p g R x) :
    form (g x) (normalizedVelocity p g R S x) (normalizedVelocity p g R S x) = p.c ^ 2 :=
  form_normalized_of_mass_shell g hqpos
    (CurvedQuantumForce.mass_shell p hg hd hs hR hS hRpos hKG)

/-- Differentiating the genuine normalization of a KG solution gives the exact projected logarithmic-gradient acceleration. -/
theorem normalized_force (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) :
    acceleration g (normalizedVelocity p g R S) x = (p.c ^ 2 / 2) •
      projectedGradient p.c g (normalizedVelocity p g R S)
        (fun y => Real.log (1 + defect p g R y)) x := by
  have hw := differentiableAt_velocity p (hg.differentiableAt (by decide))
    (isUnit_iff_ne_zero.mpr hd.ne) hS
  have hq := CurvedMassDefectRegularity.differentiableAt_defect p hg hd hs hR hS hRpos hKG
  have H : acceleration g (normalizedVelocity p g R S) x =
      (1 + defect p g R x)⁻¹ • (acceleration g (velocity p g S) x -
        (fderiv ℝ (defect p g R) x (normalizedVelocity p g R S x) / 2) •
          normalizedVelocity p g R S x) :=
    acceleration_normalized g hw hq hqpos
  rw [CurvedQuantumForce.unnormalized_force p hg hd hs hR hS hRpos hKG] at H
  rw [H, projected_log_eq p.c g (normalizedVelocity p g R S) hq hqpos]
  unfold projectedGradient
  ext a
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hqpos.ne', p.c_pos.ne']

/-- The exact normalized force has the source tensor components, including the full spacetime logarithmic derivative. -/
theorem normalized_force_components (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) (a : Fin 4) :
    acceleration g (normalizedVelocity p g R S) x a = p.c ^ 2 / 2 *
      ∑ b, ((g x)⁻¹ a b -
        normalizedVelocity p g R S x a * normalizedVelocity p g R S x b / p.c ^ 2) *
        fderiv ℝ (fun y => Real.log (1 + defect p g R y)) x (RNCCoordinateConnection.axis b) := by
  rw [normalized_force p hg hd hs hR hS hRpos hKG hqpos]
  change (p.c ^ 2 / 2) * projectedGradient p.c g (normalizedVelocity p g R S)
    (fun y => Real.log (1 + defect p g R y)) x a = _
  rw [projectedGradient_components]

/-- The actual normalized proper acceleration is orthogonal to the normalized velocity in the metric. -/
theorem force_orthogonal (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) :
    form (g x) (normalizedVelocity p g R S x)
      (acceleration g (normalizedVelocity p g R S) x) = 0 := by
  have hn := metric_square p (hg.differentiableAt (by decide)) hd hs.self_of_nhds
    hR hS hRpos hKG.self_of_nhds hqpos
  rw [normalized_force p hg hd hs hR hS hRpos hKG hqpos, map_smul, smul_eq_mul,
    projectedGradient_orthogonal (isUnit_iff_ne_zero.mpr hd.ne) p.c_pos.ne' hn, mul_zero]

/-- Positive normalization preserves precisely the supplied geometric future cone of the actual Lorentz metric frame. -/
theorem future_iff (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (x : Covector) {orientation : Orientation ℝ Covector (Fin 4)} {future : Set Covector}
    (e : GeometricLorentzFrame.Frame (g x).toBilin' orientation future)
    (hqpos : 0 < 1 + defect p g R x) :
    normalizedVelocity p g R S x ∈ future ↔ velocity p g S x ∈ future := by
  unfold normalizedVelocity normalized
  exact GeometricLorentzNormalization.mem_future_smul_iff e
    (inv_pos.mpr (Real.sqrt_pos.mpr hqpos)) _

variable {U : Set Covector}

/-- The exact normalized source force holds on every regular open positive-normalization KG solution domain. -/
theorem normalized_force_on (p : MassiveParameters) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) (hd : ∀ y ∈ U, (g y).det < 0)
    (hs : ∀ y ∈ U, (g y).IsSymm) (hR : ContDiffOn ℝ 2 R U)
    (hS : ContDiffOn ℝ 2 S U) (hRpos : ∀ y ∈ U, 0 < R y)
    (hKG : ∀ y ∈ U, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : ∀ y ∈ U, 0 < 1 + defect p g R y) :
    ∀ x ∈ U, acceleration g (normalizedVelocity p g R S) x = (p.c ^ 2 / 2) •
      projectedGradient p.c g (normalizedVelocity p g R S)
        (fun y => Real.log (1 + defect p g R y)) x := by
  intro x hx
  have hn := hU.mem_nhds hx
  exact normalized_force p ((hg x hx).contDiffAt hn) (hd x hx)
    (Filter.eventually_of_mem hn hs) ((hR x hx).contDiffAt hn) ((hS x hx).contDiffAt hn)
    (hRpos x hx) (Filter.eventually_of_mem hn hKG) (hqpos x hx)

end FoliationQM.CurvedNormalizedQuantumForce
