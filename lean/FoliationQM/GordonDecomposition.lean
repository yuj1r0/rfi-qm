module

public import FoliationQM.PolarSpinorBilinears
public import FoliationQM.RealLorentzFrame
public import FoliationQM.DiracEquation
public import FoliationQM.DiracCurrent
/-!
# The actual conditional Gordon decomposition

Source: v13 `eq:gordon_decomp` in `rem:gordon_osmotic_bridge`. The actual
flat Dirac equation has normalization i hbar gamma^nu partial_nu minus m c.
For nonzero m c, its gamma-contracted equation and its actual complex
conjugate yield the vector bilinear as the source magnetization divergence
plus the raised convective difference. No separate adjoint Dirac equation
is a premise.

The first-jet algebra uses the actual gamma and sigma matrices, actual
Dirac bilinears and actual index raising with signature (+---). The field
bridge substitutes genuine Frechet coordinate derivatives and the genuine
bilinear product rule. The final row formula also displays the actual
derivative of the Dirac-adjoint row. Parameters hbar, m and c are fixed
real constants; only m c must be nonzero for the division.

This is a conditional first-order identity. It does not expand a general
polar magnetization tensor, eliminate auxiliary frames, derive an osmotic
Fisher term, construct a polar inverse, or derive Dirac from an action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace FoliationQM.GordonDecomposition
open DiracMatrices DiracAdjoint PolarSpinorBilinears RealLorentzFrame

private theorem bilinear_sum_right (psi : Spinor) (A : Mat) (jet : Fin 4 → Spinor) :
    bilinear psi A (∑nu, jet nu) = ∑nu, bilinear psi A (jet nu) := by
  simp only [bilinear, Matrix.mulVec_sum, dotProduct_sum]

private theorem gamma_product (mu nu : Fin 4) :
    gamma mu*gamma nu = eta mu nu • (1:Mat) + (-Complex.I) • sigma mu nu := by
  have hc := clifford mu nu
  have hs : (-Complex.I) • sigma mu nu =
      (1/2:ℂ) • (gamma mu*gamma nu-gamma nu*gamma mu) := by
    unfold sigma
    rw [smul_smul]
    congr 1
    ring_nf
    norm_num
  rw [hs]
  have hhalf := congrArg (fun M : Mat => (1/2:ℂ) • M) hc
  simp only [smul_add, smul_smul] at hhalf
  rw [show (1/2:ℂ)*(2*eta mu nu)=eta mu nu by ring] at hhalf
  rw [← hhalf]
  module

private theorem gamma_product_reverse (mu nu : Fin 4) :
    gamma nu*gamma mu = eta mu nu • (1:Mat) + Complex.I • sigma mu nu := by
  have h := gamma_product nu mu
  rw [sigma_swap] at h
  have heta : eta nu mu = eta mu nu := by
    by_cases heq : mu=nu
    · subst nu; rfl
    · simp [eta, heq, Ne.symm heq]
  simpa only [heta, smul_neg, neg_smul, neg_neg] using h

private theorem contracted_right (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor)
    (heq : (Complex.I*(hbar:ℂ)) • (∑nu, (gamma nu).mulVec (jet nu)) = ((m*c:ℝ):ℂ) • psi)
    (mu : Fin 4) :
    (Complex.I*(hbar:ℂ))*(∑nu, bilinear psi (gamma mu*gamma nu) (jet nu)) =
      ((m*c:ℝ):ℂ)*bilinear psi (gamma mu) psi := by
  have h := congrArg (fun chi : Spinor => bilinear psi (gamma mu) chi) heq
  simpa only [bilinear_smul_right, bilinear_sum_right, ← bilinear_mul_matrix] using h

private theorem contracted_left (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor)
    (heq : (Complex.I*(hbar:ℂ)) • (∑nu, (gamma nu).mulVec (jet nu)) = ((m*c:ℝ):ℂ) • psi)
    (mu : Fin 4) :
    (-Complex.I*(hbar:ℂ))*(∑nu, bilinear (jet nu) (gamma nu*gamma mu) psi) =
      ((m*c:ℝ):ℂ)*bilinear psi (gamma mu) psi := by
  have h := congrArg star (contracted_right hbar m c psi jet heq mu)
  simpa only [star_mul, star_sum, star_bilinear, diracAdjoint_mul, diracAdjoint_gamma,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
    mul_comm, mul_left_comm, mul_assoc] using h


private theorem eta_contract (mu : Fin 4) (f : Fin 4 → ℂ) :
    (∑nu, eta mu nu*f nu) = (sign mu:ℂ)*f mu := by
  by_cases h : mu=0 <;> simp [eta, sign, h]

private theorem gordon_kernel_identity (psi : Spinor) (jet : Fin 4 → Spinor) (mu : Fin 4) :
    (∑nu, bilinear psi (gamma mu*gamma nu) (jet nu)) -
      (∑nu, bilinear (jet nu) (gamma nu*gamma mu) psi) =
      (sign mu:ℂ)*(bilinear psi 1 (jet mu)-bilinear (jet mu) 1 psi) -
        Complex.I*(∑nu, (bilinear (jet nu) (sigma mu nu) psi+
          bilinear psi (sigma mu nu) (jet nu))) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑nu, (eta mu nu*(bilinear psi 1 (jet nu)-bilinear (jet nu) 1 psi) -
        Complex.I*(bilinear (jet nu) (sigma mu nu) psi+bilinear psi (sigma mu nu) (jet nu))) := by
      apply Finset.sum_congr rfl
      intro nu _
      rw [gamma_product, gamma_product_reverse]
      simp only [bilinear_add_matrix, bilinear_smul_matrix]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, eta_contract]


/-- The actual raised jet component multiplies its coordinate component by the Minkowski diagonal sign. -/
def raisedJet (jet : Fin 4 → Spinor) (mu : Fin 4) : Spinor := (sign mu:ℂ) • jet mu

private theorem raisedJet_difference (psi : Spinor) (jet : Fin 4 → Spinor) (mu : Fin 4) :
    bilinear psi 1 (raisedJet jet mu)-bilinear (raisedJet jet mu) 1 psi =
      (sign mu:ℂ)*(bilinear psi 1 (jet mu)-bilinear (jet mu) 1 psi) := by
  simp only [raisedJet, bilinear_smul_left, bilinear_smul_right,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The actual Dirac first-jet equation and its derived adjoint consequence give the exact Gordon identity with the source coefficients. -/
theorem gordon_jet (hbar m c : ℝ) (hmc : m*c ≠ 0) (psi : Spinor) (jet : Fin 4 → Spinor)
    (heq : DiracEquation.jetEquation hbar m c psi jet) (mu : Fin 4) :
    bilinear psi (gamma mu) psi =
      ((hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (∑nu, (bilinear (jet nu) (sigma mu nu) psi+bilinear psi (sigma mu nu) (jet nu))) +
      (Complex.I*(hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (bilinear psi 1 (raisedJet jet mu)-bilinear (raisedJet jet mu) 1 psi) := by
  have hR := contracted_right hbar m c psi jet heq mu
  have hL := contracted_left hbar m c psi jet heq mu
  have hscaled : (2*((m*c:ℝ):ℂ))*bilinear psi (gamma mu) psi =
      (hbar:ℂ)*(∑nu, (bilinear (jet nu) (sigma mu nu) psi+
        bilinear psi (sigma mu nu) (jet nu))) +
      Complex.I*(hbar:ℂ)*(bilinear psi 1 (raisedJet jet mu)-bilinear (raisedJet jet mu) 1 psi) := by
    calc
      _ = (Complex.I*(hbar:ℂ))*((∑nu, bilinear psi (gamma mu*gamma nu) (jet nu)) -
          (∑nu, bilinear (jet nu) (gamma nu*gamma mu) psi)) := by
        linear_combination -hR -hL
      _ = _ := by
        rw [gordon_kernel_identity, raisedJet_difference]
        ring_nf
        norm_num
  have hmass : ((m*c:ℝ):ℂ) ≠ 0 := by exact_mod_cast hmc
  have hden : (2:ℂ)*((m*c:ℝ):ℂ) ≠ 0 := mul_ne_zero (by norm_num) hmass
  calc
    _ = ((hbar:ℂ)*(∑nu, (bilinear (jet nu) (sigma mu nu) psi+
        bilinear psi (sigma mu nu) (jet nu))) +
      Complex.I*(hbar:ℂ)*(bilinear psi 1 (raisedJet jet mu)-bilinear (raisedJet jet mu) 1 psi)) /
        (2*((m*c:ℝ):ℂ)) := by
      apply (eq_div_iff hden).2
      simpa only [mul_comm] using hscaled
    _ = _ := by ring


/-- The genuine raised coordinate derivative evaluates the real Frechet derivative on the metric-raised coordinate direction. -/
def raisedPartial (psi : Covector → Spinor) (x : Covector) (mu : Fin 4) : Spinor :=
  fderiv ℝ psi x (sign mu • DiracFieldDensity.coordinateDirections mu)

/-- The actual raised coordinate derivative equals the sign-raised actual derivative jet. -/
theorem raisedPartial_eq_raisedJet (psi : Covector → Spinor) (x : Covector) (mu : Fin 4) :
    raisedPartial psi x mu = raisedJet
      (fun nu => fderiv ℝ psi x (DiracFieldDensity.coordinateDirections nu)) mu := by
  unfold raisedPartial raisedJet
  rw [map_smul]
  rw [← IsScalarTower.algebraMap_smul ℂ (sign mu)
    (fderiv ℝ psi x (DiracFieldDensity.coordinateDirections mu))]
  rfl

/-- The actual differentiable flat Dirac field satisfies the complete complex Gordon identity with the genuine magnetization derivative. -/
theorem gordon_field (hbar m c : ℝ) (hmc : m*c ≠ 0)
    {psi : Covector → Spinor} {x : Covector} (hpsi : DifferentiableAt ℝ psi x)
    (heq : DiracEquation.diracField hbar m c psi x=0) (mu : Fin 4) :
    bilinear (psi x) (gamma mu) (psi x) =
      ((hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (∑nu, fderiv ℝ (fun y => bilinear (psi y) (sigma mu nu) (psi y)) x
          (DiracFieldDensity.coordinateDirections nu)) +
      (Complex.I*(hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (bilinear (psi x) 1 (raisedPartial psi x mu)-
          bilinear (raisedPartial psi x mu) 1 (psi x)) := by
  have hjet := (DiracEquation.diracField_eq_zero_iff hbar m c psi x).mp heq
  have hg := gordon_jet hbar m c hmc (psi x)
    (fun nu => fderiv ℝ psi x (DiracFieldDensity.coordinateDirections nu)) hjet mu
  simpa only [DiracCurrent.fderiv_bilinear_apply hpsi hpsi, raisedPartial_eq_raisedJet] using hg


/-- The actual Gordon decomposition has the literal source spinor-adjoint row formula, including its genuine raised derivative. -/
theorem gordon_field_row (hbar m c : ℝ) (hmc : m*c ≠ 0)
    {psi : Covector → Spinor} {x : Covector} (hpsi : DifferentiableAt ℝ psi x)
    (heq : DiracEquation.diracField hbar m c psi x=0) (mu : Fin 4) :
    dotProduct (MatrixDifferential.spinorAdjoint (psi x)) ((gamma mu).mulVec (psi x)) =
      ((hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (∑nu, fderiv ℝ (fun y => dotProduct (MatrixDifferential.spinorAdjoint (psi y))
          ((sigma mu nu).mulVec (psi y))) x (DiracFieldDensity.coordinateDirections nu)) +
      (Complex.I*(hbar:ℂ)/(2*((m*c:ℝ):ℂ))) *
        (dotProduct (MatrixDifferential.spinorAdjoint (psi x)) (raisedPartial psi x mu)-
          dotProduct (fderiv ℝ (fun y => MatrixDifferential.spinorAdjoint (psi y)) x
            (sign mu • DiracFieldDensity.coordinateDirections mu)) (psi x)) := by
  simpa only [DiracDensity.bilinear_eq_row, Matrix.one_mulVec,
    MatrixDifferential.fderiv_spinorAdjoint_apply hpsi, raisedPartial] using
      gordon_field hbar m c hmc hpsi heq mu

end FoliationQM.GordonDecomposition
