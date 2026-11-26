module

public import FoliationQM.PolarConnectionContraction

/-!
# The gamma contraction of a Lorentz connection

Source: v13 `rem:gordon_osmotic_bridge`, in the amended form approved by the
author on 2026-11-24 (`docs/ERRATA.md`), and `lem:maurer_cartan`. The product
of a Dirac matrix with a bivector matrix is split into its vector and axial
parts. Summing against a connection with frame indices gives the trace of the
connection contracted with the Dirac matrices and its axial part contracted
with the lowered Dirac matrices times gamma5. A frame conjugation transports
the coordinate contraction of the transported generators to this frame form.

These are algebraic identities for a supplied frame and supplied connection
coefficients. No derivative, spinor or equation of motion enters here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CliffordSlashConnection
open DiracMatrices DiracAdjoint RealLorentzFrame CliffordGenerators CliffordCommutators
open PolarConnectionContraction MaurerCartanDifferential

/-- A Dirac matrix times a bivector matrix is a vector part with two metric
coefficients minus the oriented axial part. -/
theorem gamma_mul_sigma (A a b : Fin 4) :
    gamma A * sigma a b =
      Complex.I • (eta a A • gamma b - eta b A • gamma a) -
        ∑ d : Fin 4, epsilon A a b d • (gammaLower d * gamma5) := by
  have h1 := gamma_sigma_anticomm_reversed A a b
  have h2 := sigma_gamma_commutator a b A
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub] at h2
  have h3 : sigma a b * gamma A - gamma A * sigma a b =
      (2 * Complex.I) • (eta b A • gamma a - eta a A • gamma b) := by
    rw [← h2, smul_smul]
    have hc : 2 * Complex.I * (-Complex.I / 2) = 1 := by
      linear_combination (-1 : ℂ) * Complex.I_mul_I
    rw [hc, one_smul]
  have hsplit : gamma A * sigma a b =
      (1/2 : ℂ) • ((gamma A * sigma a b + sigma a b * gamma A) -
        (sigma a b * gamma A - gamma A * sigma a b)) := by module
  rw [hsplit, h1, h3]
  module

/-- The trace of a frame-indexed connection, taken on its first and last
index after antisymmetrizing the last two. -/
def frameTrace (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (b : Fin 4) : ℝ :=
  (1/2) * ∑ a, sign a * (Ω a b a - Ω a a b)

/-- The axial part of a frame-indexed connection, with an upper index. -/
def frameAxial (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (d : Fin 4) : ℝ :=
  (1/2) * ∑ c, ∑ a, ∑ b, epsilonReal d c a b * Ω c a b

/-- For a connection antisymmetric in its last two indices the trace is the
signed sum over the first and last index. -/
theorem frameTrace_of_antisymm {Ω : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hanti : ∀ A a b, Ω A a b = -Ω A b a) (b : Fin 4) :
    frameTrace Ω b = ∑ a, sign a * Ω a b a := by
  unfold frameTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hanti a a b]
  ring

private theorem term (w : ℂ) (A a b : Fin 4) :
    (-Complex.I * w / 4) • (gamma A * sigma a b) =
      (w / 4) • (eta a A • gamma b - eta b A • gamma a) +
        (Complex.I * w / 4) • ∑ d : Fin 4, epsilon A a b d • (gammaLower d * gamma5) := by
  rw [gamma_mul_sigma, smul_sub, smul_smul]
  have hc : -Complex.I * w / 4 * Complex.I = w / 4 := by
    linear_combination (-w / 4) * Complex.I_mul_I
  rw [hc]
  module

set_option maxHeartbeats 4000000 in
/-- The Dirac contraction of the generators of a frame-indexed connection is
minus half its trace contracted with the Dirac matrices, minus half of i times
its axial part contracted with the lowered Dirac matrices times gamma5. -/
theorem slash_generator (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ A, gamma A * generator (Ω A) =
      (-(1/2 : ℂ)) • ∑ b, (frameTrace Ω b : ℂ) • gamma b -
        (Complex.I / 2) • ∑ d, (frameAxial Ω d : ℂ) • (gammaLower d * gamma5) := by
  simp only [generator, Matrix.mul_sum, mul_smul_comm, term]
  simp only [frameTrace, frameAxial, Fin.sum_univ_four]
  norm_num [eta, epsilon, epsilonReal, sign]
  module

/-- The generator is linear in its coefficient array. -/
theorem generator_sum_smul (r : Fin 4 → ℝ) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    generator (fun a b => ∑ mu, r mu * omega mu a b) =
      ∑ mu, (r mu : ℂ) • generator (omega mu) := by
  simp only [generator, Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu _
  ring

/-- The connection coefficients with all three indices in the frame. -/
def frameConnection (u : Fin 4 → Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A a b : Fin 4) : ℝ := ∑ mu, inverseCoefficients u mu A * omega mu a b

/-- Antisymmetry in the generator indices passes to the frame connection. -/
theorem frameConnection_antisymm (u : Fin 4 → Covector) {omega : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) (A a b : Fin 4) :
    frameConnection u omega A a b = -frameConnection u omega A b a := by
  unfold frameConnection
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  rw [hanti mu a b]
  ring

/-- The coordinate Dirac contraction of the transported generators is the
frame conjugate of the frame contraction. -/
theorem slash_transported {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ mu, gamma mu * transportedGenerator L (omega mu) =
      L * (∑ A, gamma A * generator (frameConnection u omega A)) * L⁻¹ := by
  have hleft := Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hright := Matrix.mul_nonsing_inv L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hg (mu : Fin 4) : gamma mu =
      L * (∑ A, (inverseCoefficients u mu A : ℂ) • gamma A) * L⁻¹ := by
    have h := inverse_expansion hunit hu mu
    unfold gammaExpansion at h
    rw [← h]
    calc gamma mu = (L * L⁻¹) * gamma mu * (L * L⁻¹) := by rw [hright]; simp
      _ = _ := by noncomm_ring
  have hterm (mu : Fin 4) : gamma mu * transportedGenerator L (omega mu) =
      L * (∑ A, (inverseCoefficients u mu A : ℂ) • (gamma A * generator (omega mu))) * L⁻¹ := by
    conv_lhs => rw [hg mu]
    unfold transportedGenerator
    calc _ = L * (∑ A, (inverseCoefficients u mu A : ℂ) • gamma A) * (L⁻¹ * L) *
          generator (omega mu) * L⁻¹ := by noncomm_ring
      _ = _ := by
        rw [hleft, mul_one, mul_assoc L, Finset.sum_mul]
        simp only [smul_mul_assoc]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro A _
  have hgen := generator_sum_smul (fun mu => inverseCoefficients u mu A) omega
  unfold frameConnection
  rw [hgen, Finset.mul_sum]
  simp only [mul_smul_comm]

end FoliationQM.CliffordSlashConnection
