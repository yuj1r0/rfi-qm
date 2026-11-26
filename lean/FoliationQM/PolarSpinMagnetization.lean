module

public import FoliationQM.PolarVectorGeometry
public import FoliationQM.CliffordCommutators
public import FoliationQM.RNCCoordinateConnection

/-!
# The polar spin-magnetization tensor

Source: v13 `rem:gordon_osmotic_bridge`, "the spin-magnetization divergence
`∂_ν(ψ̄ σ^{μν} ψ) = ∂_ν(ρ ε^{03ab} u_a^μ u_b^ν cos β + …)`", component kinds A
and C. For the forward polar spinor with density `ρ`, chiral angle `β` and a
matrix factor `L` that is a Dirac isometry commuting with `γ⁵` and carrying a
real frame, the tensor bilinear is

`ψ̄ σ^{μν} ψ = ρ [cos β (e₁^μ e₂^ν - e₂^μ e₁^ν) - sin β (e₀^μ e₃^ν - e₃^μ e₀^ν)]`,

where `e_A^μ` are the inverse frame coefficients, `e₀` the time vector and
`e₃` the spin vector. The `cos β` term is the one displayed in the source;
the `sin β` term is the part the source abbreviates by an ellipsis. For a
positive differentiable density the divergence of `ρ M^{μν}` is
`ρ (M^{μν} ∂_ν ln ρ + ∂_ν M^{μν})`, which is how the logarithmic density
gradient enters the magnetization divergence of the Gordon decomposition.

These are forward identities for the stated ansatz. The identification of
the logarithmic gradient with the Maurer–Cartan connection components of
`eq:canonical_P_L`, the elimination of the auxiliary frame and the resulting
Fisher term of `eq:spinor_quadratic_exact` are not addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarSpinMagnetization

open DiracMatrices DiracAdjoint ChiralMatrix PolarSpinorBilinears PolarVectorGeometry
open RealLorentzFrame RNCCoordinateConnection Matrix Complex

/-- Equal chiral factors on both sides of a bivector matrix combine to the
full chiral angle. -/
theorem chiral_sigma_sandwich (beta : ℝ) (a b : Fin 4) :
    chiral beta * sigma a b * chiral beta =
      (Real.cos beta : ℂ) • sigma a b + (I * (Real.sin beta : ℂ)) • (sigma a b * gamma5) := by
  have h5 : gamma5 * sigma a b = sigma a b * gamma5 :=
    ((CliffordCommutators.sigma_gamma5_commute a b).eq).symm
  have hc : chiral beta * sigma a b = sigma a b * chiral beta := by
    simp only [chiral, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h5]
  have hb : (beta + beta) / 2 = beta := by ring
  rw [hc, mul_assoc, ← chiral_add]
  simp only [chiral, hb, mul_add, mul_smul_comm, mul_one]

/-- The rest spinor has bivector bilinear `±1` in the spin plane and zero
elsewhere. -/
theorem rest_sigma (a b : Fin 4) :
    bilinear restSpinor (sigma a b) restSpinor =
      if a = 1 ∧ b = 2 then 1 else if a = 2 ∧ b = 1 then -1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [bilinear, sigma, gamma, restSpinor, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    first | linear_combination (-1 : ℂ) * I_sq | linear_combination I_sq

/-- The rest spinor has dual bivector bilinear `±i` in the time-spin plane and
zero elsewhere. -/
theorem rest_sigma_gamma5 (a b : Fin 4) :
    bilinear restSpinor (sigma a b * gamma5) restSpinor =
      if a = 0 ∧ b = 3 then I else if a = 3 ∧ b = 0 then -I else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [bilinear, sigma, gamma, gamma5, restSpinor, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ]

variable {L : Mat} {u : Fin 4 → Covector}

/-- The inverse matrix factor transports a bivector matrix to the bivectors
of the inverse frame coefficients. -/
theorem inverse_sigma (hL : IsUnit L) (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A))
    (mu nu : Fin 4) :
    L⁻¹ * sigma mu nu * L = ∑ A, ∑ B,
      ((inverseCoefficients u mu A : ℂ) * (inverseCoefficients u nu B : ℂ)) • sigma A B := by
  have hunit := Matrix.mul_nonsing_inv L ((Matrix.isUnit_iff_isUnit_det L).mp hL)
  have hprod (a b : Fin 4) :
      L⁻¹ * (gamma a * gamma b) * L = (L⁻¹ * gamma a * L) * (L⁻¹ * gamma b * L) := by
    calc L⁻¹ * (gamma a * gamma b) * L = L⁻¹ * gamma a * 1 * gamma b * L := by noncomm_ring
      _ = L⁻¹ * gamma a * (L * L⁻¹) * gamma b * L := by rw [hunit]
      _ = _ := by noncomm_ring
  have hP (m n : Fin 4) :
      (L⁻¹ * gamma m * L) * (L⁻¹ * gamma n * L) = ∑ A, ∑ B,
        ((inverseCoefficients u m A : ℂ) * (inverseCoefficients u n B : ℂ)) •
          (gamma A * gamma B) := by
    rw [inverse_expansion hL hu m, inverse_expansion hL hu n]
    simp only [gammaExpansion, Finset.sum_mul_sum, smul_mul_smul_comm]
  have hQ : (L⁻¹ * gamma nu * L) * (L⁻¹ * gamma mu * L) = ∑ A, ∑ B,
      ((inverseCoefficients u mu A : ℂ) * (inverseCoefficients u nu B : ℂ)) •
        (gamma B * gamma A) := by
    rw [hP nu mu, Finset.sum_comm]
    exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => by
      rw [mul_comm (inverseCoefficients u nu B : ℂ)]
  have hs : L⁻¹ * sigma mu nu * L = (I / 2) •
      ((L⁻¹ * gamma mu * L) * (L⁻¹ * gamma nu * L) -
        (L⁻¹ * gamma nu * L) * (L⁻¹ * gamma mu * L)) := by
    rw [← hprod, ← hprod]
    simp only [sigma, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
  rw [hs, hP mu nu, hQ, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [sigma]
  module

/-- The polar spin-magnetization tensor: `ψ̄ σ^{μν} ψ` is `ρ` times
`cos β` times the spin-plane bivector minus `sin β` times the time-spin
bivector of the frame. -/
theorem polar_magnetization (rho beta : ℝ) (hrho : 0 ≤ rho) (hL : IsUnit L)
    (hiso : diracAdjoint L * L = 1) (h5 : Commute L gamma5)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu nu : Fin 4) :
    bilinear (polarSpinor rho beta L) (sigma mu nu) (polarSpinor rho beta L) =
      ((rho * (Real.cos beta *
          (inverseCoefficients u mu 1 * inverseCoefficients u nu 2 -
            inverseCoefficients u mu 2 * inverseCoefficients u nu 1) -
        Real.sin beta *
          (timeVector u mu * spinVector u nu - spinVector u mu * timeVector u nu)) : ℝ) : ℂ) := by
  have hinv := MaurerCartanDifferential.inverse_eq_diracAdjoint hiso
  have h1 : diracAdjoint L * (chiral beta * sigma mu nu * chiral beta) * L =
      (Real.cos beta : ℂ) • (L⁻¹ * sigma mu nu * L) +
        (I * (Real.sin beta : ℂ)) • ((L⁻¹ * sigma mu nu * L) * gamma5) := by
    rw [chiral_sigma_sandwich, ← hinv]
    have h2 : L⁻¹ * (sigma mu nu * gamma5) * L = (L⁻¹ * sigma mu nu * L) * gamma5 := by
      calc L⁻¹ * (sigma mu nu * gamma5) * L = L⁻¹ * sigma mu nu * (gamma5 * L) := by
            noncomm_ring
        _ = L⁻¹ * sigma mu nu * (L * gamma5) := by rw [h5.eq]
        _ = _ := by noncomm_ring
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h2]
  rw [polar_bilinear rho beta L (sigma mu nu) hrho, h1, inverse_sigma hL hu]
  simp only [bilinear_add_matrix, bilinear_smul_matrix, Finset.sum_mul, smul_mul_assoc,
    bilinear_sum, rest_sigma, rest_sigma_gamma5, timeVector, spinVector]
  simp only [Fin.sum_univ_four]
  simp only [Fin.isValue, Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
    mul_zero, mul_one, add_zero, zero_add, mul_neg]
  simp only [ofReal_mul, ofReal_sub]
  linear_combination (rho : ℂ) * (Real.sin beta : ℂ) *
    ((inverseCoefficients u mu 0 : ℂ) * (inverseCoefficients u nu 3 : ℂ) -
      (inverseCoefficients u mu 3 : ℂ) * (inverseCoefficients u nu 0 : ℂ)) * I_sq

/-- The divergence of a density times a tensor row is the density times the
row contracted with the logarithmic density gradient plus the row
divergence. -/
theorem divergence_density_mul {rho : Covector → ℝ} {M : Fin 4 → Covector → ℝ} {x : Covector}
    (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x)
    (hM : ∀ nu, DifferentiableAt ℝ (M nu) x) :
    (∑ nu, fderiv ℝ (fun y => rho y * M nu y) x (axis nu)) =
      rho x * ∑ nu, (M nu x * fderiv ℝ (fun y => Real.log (rho y)) x (axis nu) +
        fderiv ℝ (M nu) x (axis nu)) := by
  have hlog : fderiv ℝ (fun y => Real.log (rho y)) x = (rho x)⁻¹ • fderiv ℝ rho x :=
    (hrho.hasFDerivAt.log hpos.ne').fderiv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun nu _ => ?_
  rw [fderiv_fun_mul hrho (hM nu), hlog]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  field_simp
  ring

end FoliationQM.PolarSpinMagnetization
