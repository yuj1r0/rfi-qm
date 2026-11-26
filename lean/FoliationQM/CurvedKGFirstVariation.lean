module

public import FoliationQM.CurvedPolarAction

/-!
# Pointwise first variation of the curved Klein–Gordon density

The real line of complex fields differentiates in both slots of the
Hermitian kinetic pairing. Symmetry of the metric identifies the real
parts of these contributions. The signed mass coefficient already
contains the scalar-curvature term from v13.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedKGFirstVariation

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection CurvedFluxGreen CurvedPolarAction
open scoped Matrix.Norms.Operator ComplexConjugate

/-- The affine line of complex fields with real variation parameter. -/
def perturb (ψ η : Covector → ℂ) (t : ℝ) (x : Covector) : ℂ := ψ x + t • η x

/-- The polarized curved kinetic and mass density, conjugate-linear in the first field. -/
def cross (p : MassiveParameters) (g : Covector → Mat4) (η ψ : Covector → ℂ) (x : Covector) : ℂ :=
  (p.hbar ^ 2 : ℝ) • kinetic g η ψ x - massTerm p g x • (star (η x) * ψ x)

variable {g : Covector → Mat4} {x : Covector} {ψ η χ : Covector → ℂ}

/-- Actual differential along an arbitrary coordinate direction of the perturbed field. -/
theorem fderiv_perturb (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) (t : ℝ) (v : Covector) :
    fderiv ℝ (perturb ψ η t) x v = fderiv ℝ ψ x v + t • fderiv ℝ η x v := by
  have hd : HasFDerivAt (perturb ψ η t) (fderiv ℝ ψ x + t • fderiv ℝ η x) x :=
    hψ.hasFDerivAt.add (hη.hasFDerivAt.const_smul t)
  rw [hd.fderiv, add_apply, smul_apply]

/-- Real perturbations of the test slot distribute over the kinetic form. -/
theorem kinetic_perturb_left (g : Covector → Mat4) (hχ : DifferentiableAt ℝ χ x)
    (hη : DifferentiableAt ℝ η x) (ψ : Covector → ℂ) (t : ℝ) :
    kinetic g (perturb χ η t) ψ x = kinetic g χ ψ x + t • kinetic g η ψ x := by
  simp only [kinetic, fderiv_perturb hχ hη, star_add, star_smul, star_trivial, add_mul, smul_add,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.real_smul]
  ring

/-- Real perturbations of the field slot distribute over the kinetic form. -/
theorem kinetic_perturb_right (g : Covector → Mat4) (χ : Covector → ℂ) (hψ : DifferentiableAt ℝ ψ x)
    (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    kinetic g χ (perturb ψ η t) x = kinetic g χ ψ x + t • kinetic g χ η x := by
  simp only [kinetic, fderiv_perturb hψ hη, mul_add, smul_add, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.real_smul]
  ring

/-- An independent perturbation of the conjugate test field changes only the first slot of the polarized density. -/
theorem cross_perturb_left (p : MassiveParameters) (g : Covector → Mat4) (hχ : DifferentiableAt ℝ χ x)
    (hη : DifferentiableAt ℝ η x) (ψ : Covector → ℂ) (t : ℝ) :
    cross p g (perturb χ η t) ψ x = cross p g χ ψ x + t • cross p g η ψ x := by
  simp only [cross, kinetic_perturb_left g hχ hη, perturb, star_add, star_smul, star_trivial]
  simp only [Complex.real_smul]
  ring

/-- An independent perturbation of the field changes only the second slot of the polarized density. -/
theorem cross_perturb_right (p : MassiveParameters) (g : Covector → Mat4) (χ : Covector → ℂ)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    cross p g χ (perturb ψ η t) x = cross p g χ ψ x + t • cross p g χ η x := by
  simp only [cross, kinetic_perturb_right g χ hψ hη, perturb, Complex.real_smul]
  ring

/-- Exchanging the two fields conjugates the polarized density for a symmetric metric. -/
theorem cross_hermitian (p : MassiveParameters) (hs : (g x).IsSymm) (u f : Covector → ℂ) :
    star (cross p g f u x) = cross p g u f x := by
  simp only [cross, star_sub, star_smul, star_trivial, CurvedGreenBoundary.kinetic_hermitian hs,
    star_mul, star_star]

/-- Evaluating the real polarized density twice on the same field recovers the curved action density. -/
theorem cross_self_re (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) :
    (cross p g ψ ψ x).re = kgDensity p g ψ x := by
  simp only [cross, kgDensity, CurvedKineticCovariance.actionDensity, Complex.sub_re, Complex.smul_re,
    smul_eq_mul, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- The exact density along an affine variation line is quadratic, with linear coefficient twice the real cross term. -/
theorem density_perturb (p : MassiveParameters) (hs : (g x).IsSymm) (hψ : DifferentiableAt ℝ ψ x)
    (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    kgDensity p g (perturb ψ η t) x = kgDensity p g ψ x + 2*t*(cross p g η ψ x).re +
      t^2 * kgDensity p g η x := by
  have he := congrArg Complex.re (cross_hermitian p hs ψ η)
  simp only [Complex.star_def, Complex.conj_re] at he
  simp only [← cross_self_re, cross_perturb_left p g hψ hη, cross_perturb_right p g _ hψ hη,
    Complex.add_re, Complex.smul_re, smul_eq_mul, he]
  ring

/-- The actual derivative of the curved integrand at every real parameter on the line. -/
theorem hasDerivAt_density_perturb_at (p : MassiveParameters) (hs : (g x).IsSymm)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    HasDerivAt (fun s => kgDensity p g (perturb ψ η s) x)
      (2*(cross p g η ψ x).re + 2*t*kgDensity p g η x) t := by
  simp_rw [density_perturb p hs hψ hη]
  have hd := ((hasDerivAt_id t).const_mul 2).mul_const (cross p g η ψ x).re
  convert! (hd.const_add (kgDensity p g ψ x)).add (((hasDerivAt_id t).pow 2).mul_const (kgDensity p g η x)) using 1
  simp only [id_eq]
  ring

/-- The pointwise first variation at zero is twice the real mixed density. -/
theorem hasDerivAt_density_perturb (p : MassiveParameters) (hs : (g x).IsSymm)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    HasDerivAt (fun s => kgDensity p g (perturb ψ η s) x) (2*(cross p g η ψ x).re) 0 := by
  simpa using hasDerivAt_density_perturb_at p hs hψ hη 0

end FoliationQM.CurvedKGFirstVariation
