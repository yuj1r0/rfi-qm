module

public import FoliationQM.RotorFrameEvolution
public import FoliationQM.MatrixDifferential
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!
# Actual real gamma expansions and Lorentz frame normalization

Source: the tetrad and Ricci-rotation constructions in v13 `lem:maurer_cartan`
and the vector/axial identification in `prop:takabayasi`. An actual real
expansion of L gamma_A L inverse in the upper-index Dirac gamma basis is an
explicit premise. Uniqueness and Minkowski normalization are proved from
that expansion and the Clifford relation; they are not additional premises.
No assertion is made that every invertible complex matrix has a real frame
expansion, or that the resulting Lorentz frame has a chosen time orientation.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator

namespace FoliationQM.RealLorentzFrame
open DiracMatrices RotorFrameEvolution

/-- The real diagonal Minkowski sign in signature (+---). -/
def sign (a : Fin 4) : ℝ := if a=0 then 1 else -1

/-- The actual real linear combination of the upper-index Dirac gamma basis. -/
def gammaExpansion (v : Covector) : Mat := ∑ a : Fin 4, (v a : ℂ) • gamma a

/-- The actual gamma expansion has these explicit complex matrix entries. -/
theorem gammaExpansion_explicit (v : Covector) :
    gammaExpansion v =
      !![(v 0 : ℂ), 0, (v 3 : ℂ), (v 1 : ℂ)-Complex.I*(v 2 : ℂ);
        0, (v 0 : ℂ), (v 1 : ℂ)+Complex.I*(v 2 : ℂ), -(v 3 : ℂ);
        -(v 3 : ℂ), -(v 1 : ℂ)+Complex.I*(v 2 : ℂ), -(v 0 : ℂ), 0;
        -(v 1 : ℂ)-Complex.I*(v 2 : ℂ), (v 3 : ℂ), 0, -(v 0 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaExpansion, gamma, Fin.sum_univ_succ] <;> ring

/-- The actual upper-index Dirac gamma expansion uniquely determines its four real coefficients. -/
theorem gammaExpansion_injective : Function.Injective gammaExpansion := by
  intro u v h
  have h0 := congrArg (fun M : Mat => (M 0 0).re) h
  have h1 := congrArg (fun M : Mat => (M 0 3).re) h
  have h2 := congrArg (fun M : Mat => (M 0 3).im) h
  have h3 := congrArg (fun M : Mat => (M 0 2).re) h
  simp [gammaExpansion_explicit] at h0 h1 h2 h3
  funext a
  fin_cases a
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The actual gamma expansion as a real continuous-linear map. -/
def gammaExpansionCLM : Covector →L[ℝ] Mat :=
  ({ toFun := gammaExpansion
     map_add' := by
       intro u v
       simp [gammaExpansion, add_smul, Finset.sum_add_distrib]
     map_smul' := by
       intro r v
       change (∑ a : Fin 4, ((r*v a : ℝ) : ℂ) • gamma a) = r • gammaExpansion v
       rw [← IsScalarTower.algebraMap_smul ℂ r (gammaExpansion v)]
       simp [gammaExpansion, Finset.smul_sum, mul_smul] } :
    Covector →ₗ[ℝ] Mat).toContinuousLinearMap

/-- The real continuous-linear expansion evaluates to the actual gamma sum. -/
theorem gammaExpansionCLM_apply (v : Covector) : gammaExpansionCLM v = gammaExpansion v := rfl

/-- The actual anticommutator of two real gamma expansions is twice their explicit Minkowski pairing times the identity. -/
theorem gammaExpansion_anticomm (u v : Covector) :
    gammaExpansion u * gammaExpansion v + gammaExpansion v * gammaExpansion u =
      (2 * (minkowski u v : ℂ)) • (1 : Mat) := by
  rw [gammaExpansion_explicit, gammaExpansion_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowski] <;>
    ring_nf <;> norm_num <;> ring

/-- An actual real gamma expansion of an invertible conjugated frame is Minkowski orthonormal by the Clifford relation. -/
theorem row_orthonormal {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (A B : Fin 4) :
    minkowski (u A) (u B) = if A = B then sign A else 0 := by
  have hconj : conjugate L (gamma A) * conjugate L (gamma B) +
      conjugate L (gamma B) * conjugate L (gamma A) = (2*eta A B) • (1 : Mat) := by
    simp only [← conjugate_mul hL, ← conjugate_add, clifford, conjugate_smul, conjugate_one hL]
  have he : (2*(minkowski (u A) (u B) : ℂ)) • (1 : Mat) = (2*eta A B) • (1 : Mat) := by
    simpa only [conjugate, hu, gammaExpansion_anticomm] using hconj
  have hs := congrArg (fun M : Mat => (M 0 0).re) he
  have hs' : 2*minkowski (u A) (u B) = 2*(eta A B).re := by simpa using hs
  have hmetric : (eta A B).re = if A = B then sign A else 0 := by
    unfold eta sign
    split_ifs <;> norm_num
  rw [hmetric] at hs'
  linarith

/-- The explicit Minkowski pairing is the finite sum with the four actual metric signs. -/
theorem minkowski_eq_sum (v w : Covector) :
    minkowski v w = ∑ a : Fin 4, sign a*v a*w a := by
  simp [minkowski, sign, Fin.sum_univ_succ]
  ring

/-- The derived real frame normalization has the signed-sum form used by Ricci-rotation contractions. -/
theorem row_orthonormal_sum {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (A B : Fin 4) :
    (∑ ν : Fin 4, sign ν * u A ν * u B ν) = if A = B then sign A else 0 := by
  rw [← minkowski_eq_sum]
  exact row_orthonormal hL hu A B

/-- The actual real inverse-frame matrix, with both diagonal metric signs multiplying the transposed forward coefficients. -/
def inverseCoefficients (u : Fin 4 → Covector) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun mu A => sign mu * sign A * u A mu

/-- Each actual diagonal Minkowski sign squares to one. -/
theorem sign_sq (a : Fin 4) : sign a * sign a = 1 := by
  unfold sign
  split_ifs <;> norm_num

private theorem right_inverse_coefficients {u : Fin 4 → Covector}
    (horth : ∀ A B, minkowski (u A) (u B) = if A = B then sign A else 0) :
    Matrix.of u * inverseCoefficients u = 1 := by
  ext A B
  rw [Matrix.mul_apply]
  calc
    _ = sign B * (∑ mu : Fin 4, sign mu * u A mu * u B mu) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mu _
      simp only [inverseCoefficients, Matrix.of_apply]
      ring
    _ = sign B * (if A = B then sign A else 0) := by rw [← minkowski_eq_sum, horth]
    _ = (1 : Matrix (Fin 4) (Fin 4) ℝ) A B := by
      by_cases h : A = B
      · subst B
        simp [sign_sq]
      · simp [h]

/-- The derived inverse-frame coefficients multiply the actual forward coefficient matrix to the identity. -/
theorem inverse_coefficients_mul {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    inverseCoefficients u * Matrix.of u = 1 :=
  mul_eq_one_comm.mp (right_inverse_coefficients (row_orthonormal hL hu))

/-- A real linear combination of frame rows expands as the corresponding real linear combination of their actual gamma matrices. -/
theorem gammaExpansion_sum_smul (r : Covector) (u : Fin 4 → Covector) :
    gammaExpansion (fun mu => ∑ A : Fin 4, r A*u A mu) =
      ∑ A : Fin 4, (r A : ℂ) • gammaExpansion (u A) := by
  have hvec : (fun mu => ∑ A : Fin 4, r A*u A mu) = ∑ A : Fin 4, r A • u A := by
    funext mu
    simp
  rw [hvec, ← gammaExpansionCLM_apply, map_sum]
  simp only [map_smul, gammaExpansionCLM_apply]
  apply Finset.sum_congr rfl
  intro A _
  exact (IsScalarTower.algebraMap_smul ℂ (r A) (gammaExpansion (u A))).symm

/-- Actual matrix conjugation distributes across the real gamma expansion. -/
theorem conjugate_gammaExpansion (L : Mat) (v : Covector) :
    conjugate L (gammaExpansion v) = ∑ A : Fin 4, (v A : ℂ) • conjugate L (gamma A) := by
  simp [conjugate, gammaExpansion, Matrix.mul_sum, Matrix.sum_mul]

/-- The actual inverse matrix conjugation has the uniquely reconstructed inverse-frame real gamma coefficients. -/
theorem inverse_expansion {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu : Fin 4) :
    L⁻¹ * gamma mu * L = gammaExpansion (fun A => inverseCoefficients u mu A) := by
  apply conjugate_injective hL
  have hunit := Matrix.mul_nonsing_inv L ((Matrix.isUnit_iff_isUnit_det L).mp hL)
  have hleft : conjugate L (L⁻¹ * gamma mu * L) = gamma mu := by
    calc
      _ = (L*L⁻¹)*gamma mu*(L*L⁻¹) := by unfold conjugate; noncomm_ring
      _ = gamma mu := by rw [hunit]; simp
  rw [hleft, conjugate_gammaExpansion]
  simp only [conjugate, hu]
  rw [← gammaExpansion_sum_smul]
  have hinv := inverse_coefficients_mul hL hu
  have hrow : (fun nu => ∑ A : Fin 4, inverseCoefficients u mu A * u A nu) =
      (fun nu => if mu = nu then 1 else 0) := by
    funext nu
    simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] using congrArg (fun M => M mu nu) hinv
  rw [hrow]
  simp [gammaExpansion]

/-- The reconstructed inverse-frame columns inherit actual Minkowski orthonormality from the Clifford-derived frame normalization. -/
theorem inverse_columns_orthonormal {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (A B : Fin 4) :
    minkowski (fun mu => inverseCoefficients u mu A) (fun mu => inverseCoefficients u mu B) =
      if A = B then sign A else 0 := by
  rw [minkowski_eq_sum]
  calc
    _ = (sign A*sign B) * (∑ mu : Fin 4, sign mu * u A mu * u B mu) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mu _
      unfold inverseCoefficients
      have hs := sign_sq mu
      calc
        _ = (sign mu*sign mu)*(sign A*sign B)*(sign mu * u A mu * u B mu) := by ring
        _ = _ := by rw [hs]; ring
    _ = (sign A*sign B) * (if A = B then sign A else 0) := by rw [row_orthonormal_sum hL hu]
    _ = _ := by
      by_cases h : A = B
      · subst B
        simp [sign_sq]
      · simp [h]

/-- The reconstructed temporal inverse-frame column has actual Minkowski norm one. -/
theorem inverse_velocity_normalized {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (fun mu => inverseCoefficients u mu 0) (fun mu => inverseCoefficients u mu 0) = 1 := by
  simpa [sign] using inverse_columns_orthonormal hL hu 0 0

/-- The reconstructed axial-three inverse-frame column has actual Minkowski norm minus one. -/
theorem inverse_spin_normalized {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (fun mu => inverseCoefficients u mu 3) (fun mu => inverseCoefficients u mu 3) = -1 := by
  simpa [sign] using inverse_columns_orthonormal hL hu 3 3

/-- The reconstructed temporal and axial-three inverse-frame columns are actually Minkowski orthogonal. -/
theorem inverse_velocity_spin_orthogonal {L : Mat} {u : Fin 4 → Covector} (hL : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) :
    minkowski (fun mu => inverseCoefficients u mu 0) (fun mu => inverseCoefficients u mu 3) = 0 := by
  simpa using inverse_columns_orthonormal hL hu 0 3

end FoliationQM.RealLorentzFrame
