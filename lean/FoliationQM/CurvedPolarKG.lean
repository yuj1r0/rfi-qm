module

public import FoliationQM.CurvedKGTestResidual
public import FoliationQM.PolarSecondDifferential
public import FoliationQM.CurvedPolarWave
public import FoliationQM.CurvedPolarCurrent

/-!
# Curved polar Klein–Gordon equations and the mass defect

The real and imaginary parts use the actual metric-volume wave operator
and current divergence. The quantum mass defect is the v13 expression
with the computed scalar curvature and spacetime-constant parameters.
All division by amplitude is restricted to the positive-amplitude domain.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedPolarKG

open LorentzMatrixGroup RNCCoordinateCurvature CurvedWaveDivergence
  CurvedGradientCovariance PolarSecondDifferential CurvedKGTestResidual

/-- The dimensionless mass defect in v13, using the genuine curved wave and curvature. -/
def defect (p : MassiveParameters) (g : Covector → Mat4) (R : Covector → ℝ)
    (x : Covector) : ℝ :=
  p.ellC ^ 2 * (wave g R x / R x - scalar g x / 6)

/-- The real Hamilton–Jacobi residual with the curvature sign fixed by the curved KG equation. -/
def hjResidual (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (x : Covector) : ℝ :=
  pairing g S S x - p.m ^ 2 * p.c ^ 2 -
    p.hbar ^ 2 * wave g R x / R x + p.hbar ^ 2 * scalar g x / 6

/-- The computed mass defect expresses the real residual as an exact mass-shell difference. -/
theorem hjResidual_eq_defect (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (x : Covector) :
    hjResidual p g R S x = pairing g S S x - p.m ^ 2 * p.c ^ 2 * (1 + defect p g R x) := by
  unfold hjResidual defect MassiveParameters.ellC
  field_simp [p.m_pos.ne', p.c_pos.ne']
  ring

/-- The vanishing real residual is precisely the inverse-metric phase-gradient mass shell. -/
theorem hjResidual_zero_iff (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (x : Covector) :
    hjResidual p g R S x = 0 ↔
      pairing g S S x / p.m ^ 2 = p.c ^ 2 * (1 + defect p g R x) := by
  rw [hjResidual_eq_defect, sub_eq_zero, div_eq_iff (pow_ne_zero 2 p.m_pos.ne')]
  ring_nf

private theorem factor_algebra (p : MassiveParameters) (r s bR bS ps pr sc : ℝ) (hr : r ≠ 0) :
    phase (s / p.hbar) *
        (((bR - r * ps / p.hbar ^ 2 : ℝ) : ℂ) +
          Complex.I * (((2 * pr + r * bS) / p.hbar : ℝ) : ℂ)) +
      ((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 - sc / 6 : ℝ) : ℂ) *
        ((r : ℂ) * phase (s / p.hbar)) =
      phase (s / p.hbar) *
        (((-r / p.hbar ^ 2 *
          (ps - p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 * bR / r + p.hbar ^ 2 * sc / 6) : ℝ) : ℂ) +
          Complex.I * (((2 * r * pr + r ^ 2 * bS) / (p.hbar * r) : ℝ) : ℂ)) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hh0 : (p.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.hbar_pos.ne'
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_ofNat]
  field_simp
  ring

private theorem factor_zero_iff (p : MassiveParameters) (r s H J : ℝ) (hr : r ≠ 0) :
    phase (s / p.hbar) *
      (((-r / p.hbar ^ 2 * H : ℝ) : ℂ) +
        Complex.I * ((J / (p.hbar * r) : ℝ) : ℂ)) = 0 ↔ H = 0 ∧ J = 0 := by
  have he : phase (s / p.hbar) ≠ 0 := Complex.exp_ne_zero _
  rw [mul_eq_zero, or_iff_right he]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im] at him
    exact ⟨(mul_eq_zero.mp hre).resolve_left
      (div_ne_zero (neg_ne_zero.mpr hr) (pow_ne_zero 2 p.hbar_pos.ne')),
      (div_eq_zero_iff.mp him).resolve_right (mul_ne_zero p.hbar_pos.ne' hr)⟩
  · rintro ⟨rfl, rfl⟩
    simp

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- The actual curved KG operator splits into the real Hamilton–Jacobi residual and the genuine current divergence. -/
theorem operator_decomposition (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x) :
    kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x =
      phase (S x / p.hbar) *
        (((-R x / p.hbar ^ 2 * hjResidual p g R S x : ℝ) : ℂ) +
          Complex.I * ((CurvedPolarCurrent.currentDivergence g R S x / (p.hbar * R x) : ℝ) : ℂ)) := by
  have hw := CurvedPolarWave.wave_actionField p hg hd hs hR hS
  unfold Madelung.actionField at hw
  rw [kgOperator, hw,
    CurvedPolarCurrent.currentDivergence_eq hg hd (hR.differentiableAt (by decide)) hS]
  simpa only [hjResidual, amplitudeField, Complex.real_smul] using
    factor_algebra p (R x) (S x) (wave g R x) (wave g S x)
      (pairing g S S x) (pairing g R S x) (scalar g x) hp.ne'

/-- On positive amplitude, the curved complex field equation is equivalent to its exact real and imaginary equations. -/
theorem operator_zero_iff (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x) :
    kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0 ↔
      hjResidual p g R S x = 0 ∧ CurvedPolarCurrent.currentDivergence g R S x = 0 := by
  rw [operator_decomposition p hg hd hs hR hS hp]
  exact factor_zero_iff p (R x) (S x) _ _ hp.ne'

/-- The real part of an actual curved KG solution gives the exact inverse-metric phase-gradient mass shell. -/
theorem mass_shell (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hkg : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    pairing g S S x / p.m ^ 2 = p.c ^ 2 * (1 + defect p g R x) :=
  (hjResidual_zero_iff p g R S x).mp ((operator_zero_iff p hg hd hs hR hS hp).mp hkg).1

/-- On KG solutions the wave-and-curvature defect equals a first-derivative expression, useful for its regularity. -/
theorem defect_eq (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hkg : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    defect p g R x = pairing g S S x / (p.m ^ 2 * p.c ^ 2) - 1 := by
  have H := mass_shell p hg hd hs hR hS hp hkg
  field_simp [p.m_pos.ne', p.c_pos.ne'] at H ⊢
  nlinarith [H]

/-- The imaginary part of an actual curved KG solution is conservation of its densitized phase current. -/
theorem current_conserved (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hkg : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    CurvedPolarCurrent.currentDivergence g R S x = 0 :=
  ((operator_zero_iff p hg hd hs hR hS hp).mp hkg).2

/-- The constant-mass velocity current has zero actual metric-volume divergence on every positive polar KG solution. -/
theorem velocity_current_conserved (p : MassiveParameters) (hg : DifferentiableAt ℝ g x)
    (hd : (g x).det < 0) (hs : (g x).IsSymm) (hR : ContDiffAt ℝ 2 R x)
    (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hkg : kgOperator p g (amplitudeField R (fun y => S y / p.hbar)) x = 0) :
    (RNCVolumeDensity.volumeFactor (g x))⁻¹ * ∑ i,
      fderiv ℝ (fun y => CurvedPolarCurrent.velocityCurrentFlux p.m g R S y i)
        x (RNCCoordinateConnection.axis i) = 0 := by
  unfold CurvedPolarCurrent.velocityCurrentFlux
  rw [CurvedPolarCurrent.scaled_currentDivergence _ hg hd (hR.differentiableAt (by decide)) hS,
    current_conserved p hg hd hs hR hS hp hkg, mul_zero]

end FoliationQM.CurvedPolarKG
