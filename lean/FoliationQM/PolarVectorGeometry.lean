module
public import FoliationQM.RealLorentzFrame
public import FoliationQM.PolarSpinorBilinears
public import FoliationQM.MaurerCartanDifferential

/-!
# Actual polar vector and axial geometry

Source: v13 `eq:vector_axial_bilinears`. The real frame expansion is supplied
as an actual matrix equality. Its normalization and inverse coefficients are
proved by Clifford algebra in RealLorentzFrame. Here they are connected to
the actual complex vector and axial bilinears of the forward polar ansatz.
The velocity includes the source factor c; the spin vector has unit spacelike
norm. No general Spin reconstruction or time-orientation theorem is claimed.
-/
@[expose] public section
noncomputable section
namespace FoliationQM.PolarVectorGeometry
open DiracMatrices DiracAdjoint PolarSpinorBilinears RealLorentzFrame

/-- The dimensionless physical time column of the inverse gamma expansion. -/
def timeVector (u : Fin 4 → Covector) : Covector := fun mu => inverseCoefficients u mu 0

/-- The physical spin column of the inverse gamma expansion. -/
def spinVector (u : Fin 4 → Covector) : Covector := fun mu => inverseCoefficients u mu 3

/-- The physical velocity includes the source speed-of-light scale. -/
def velocity (c : ℝ) (u : Fin 4 → Covector) : Covector := fun mu => c*timeVector u mu

/-- Lowering an actual gamma index multiplies by its real Minkowski sign. -/
theorem gammaLower_eq_sign (A : Fin 4) : gammaLower A = (sign A : ℂ) • gamma A := by
  by_cases h : A = 0 <;> simp [gammaLower, sign, h]

/-- The physical inverse-expansion columns are exactly the source tetrad coefficients in the lower gamma basis. -/
theorem physical_frame_expansion {L : Mat} {u : Fin 4 → Covector}
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (A : Fin 4) :
    L * gammaLower A * L⁻¹ =
      ∑ nu, (inverseCoefficients u nu A : ℂ) • gammaLower nu := by
  rw [gammaLower_eq_sign, mul_smul_comm, smul_mul_assoc, hu]
  simp only [gammaExpansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro nu _
  rw [gammaLower_eq_sign, smul_smul, smul_smul]
  congr 1
  simp only [inverseCoefficients, Complex.ofReal_mul, sign]
  split_ifs <;> norm_num

/-- The actual polar vector bilinear is rho times the real physical time column. -/
theorem polar_vector_frame (rho beta : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hL : IsUnit L) (hiso : diracAdjoint L * L = 1)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu : Fin 4) :
    bilinear (polarSpinor rho beta L) (gamma mu) (polarSpinor rho beta L) =
      (rho : ℂ) * (timeVector u mu : ℂ) := by
  apply polar_vector_projection rho beta L mu hrho (fun A => inverseCoefficients u mu A)
  rw [← MaurerCartanDifferential.inverse_eq_diracAdjoint hiso]
  exact inverse_expansion hL hu mu

/-- The actual polar axial bilinear is rho times the real physical spin column. -/
theorem polar_axial_frame (rho beta : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hL : IsUnit L) (hiso : diracAdjoint L * L = 1)
    (h5 : Commute L gamma5)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu : Fin 4) :
    bilinear (polarSpinor rho beta L) (gamma mu * gamma5) (polarSpinor rho beta L) =
      (rho : ℂ) * (spinVector u mu : ℂ) := by
  apply polar_axial_projection rho beta L mu hrho h5 (fun A => inverseCoefficients u mu A)
  rw [← MaurerCartanDifferential.inverse_eq_diracAdjoint hiso]
  exact inverse_expansion hL hu mu

/-- The actual vector bilinear also equals rho over c times the physical velocity when c is nonzero. -/
theorem polar_vector_velocity (rho beta c : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hc : c ≠ 0) (hrho : 0 ≤ rho) (hL : IsUnit L) (hiso : diracAdjoint L * L = 1)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu : Fin 4) :
    bilinear (polarSpinor rho beta L) (gamma mu) (polarSpinor rho beta L) =
      ((rho/c : ℝ) : ℂ) * (velocity c u mu : ℂ) := by
  rw [polar_vector_frame rho beta hrho hL hiso hu]
  simp only [velocity, Complex.ofReal_div, Complex.ofReal_mul]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-- The physical velocity has Minkowski norm squared c squared, derived from the actual matrix frame. -/
theorem velocity_normalized (c : ℝ) {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (velocity c u) (velocity c u) = c^2 := by
  have hn := inverse_velocity_normalized hL hu
  change minkowski (timeVector u) (timeVector u) = 1 at hn
  calc
    _ = c^2 * minkowski (timeVector u) (timeVector u) := by simp only [velocity, minkowski]; ring
    _ = _ := by rw [hn, mul_one]

/-- The physical spin vector has unit spacelike Minkowski norm, derived from the actual matrix frame. -/
theorem spin_normalized {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (spinVector u) (spinVector u) = -1 := inverse_spin_normalized hL hu

/-- The physical velocity and spin are Minkowski orthogonal, derived from the actual matrix frame. -/
theorem velocity_spin_orthogonal (c : ℝ) {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (velocity c u) (spinVector u) = 0 := by
  have hn := inverse_velocity_spin_orthogonal hL hu
  change minkowski (timeVector u) (spinVector u) = 0 at hn
  calc
    _ = c * minkowski (timeVector u) (spinVector u) := by simp only [velocity, minkowski]; ring
    _ = _ := by rw [hn, mul_zero]

end FoliationQM.PolarVectorGeometry
