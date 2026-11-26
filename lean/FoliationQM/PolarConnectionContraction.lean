module

public import FoliationQM.PolarVectorGeometry
public import FoliationQM.CliffordGenerators
public import FoliationQM.CliffordCommutators
/-!
# Actual polar connection contraction and its three-term source expansion

Source: v13 `eq:canonical_P_L` and the connection term in the proof of
`eq:dirac_polar_lagrangian_main`. The transported generator is the actual
matrix L*(-i omega_ab sigma^ab/4)*L inverse. Its anticommutator with gamma
is evaluated on the actual forward polar spinor, using genuine chiral
cancellation, inverse-frame reconstruction and the proved rest-spinor
Clifford contraction.

The real frame premise is the actual upper-gamma conjugation expansion.
The physical source coefficients are its derived inverse-frame columns,
with the signature signs already included. The real Levi-Civita expression
is proved to cast to the existing complex epsilon. Antisymmetry combines
the six nonzero epsilon terms into the three stated source terms.

These are algebraic identities for the supplied frame and generator. No
phase-gradient interpretation, spinor reconstruction, equation of motion,
or derivative identity is assumed or established here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarConnectionContraction
open DiracMatrices DiracAdjoint ChiralMatrix PolarSpinorBilinears RealLorentzFrame
open CliffordGenerators CliffordCommutators MaurerCartanDifferential

/-- The actual frame-conjugated Lorentz generator with the source ordered double-sum normalization. -/
def transportedGenerator (L : Mat) (omega : Fin 4 → Fin 4 → ℝ) : Mat :=
  L * generator omega * L⁻¹

private theorem commute_chiral {K : Mat} (hK : Commute K gamma5) (beta : ℝ) :
    Commute K (chiral beta) := by
  change K*chiral beta=chiral beta*K
  simp only [chiral, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hK.eq]

private theorem chiral_connection_cancel (beta : ℝ) (mu : Fin 4) {K : Mat}
    (hK : Commute K gamma5) :
    chiral beta*(gamma mu*K+K*gamma mu)*chiral beta=gamma mu*K+K*gamma mu := by
  have hc := (commute_chiral hK beta).eq
  calc
    _ = (chiral beta*gamma mu)*(K*chiral beta)+
        (chiral beta*K)*(gamma mu*chiral beta) := by noncomm_ring
    _ = (chiral beta*gamma mu)*(chiral beta*K)+
        (K*chiral beta)*(gamma mu*chiral beta) := by rw [hc]
    _ = (chiral beta*gamma mu*chiral beta)*K+
        K*(chiral beta*gamma mu*chiral beta) := by noncomm_ring
    _ = _ := by rw [chiral_gamma_cancel]

private theorem generator_rest_anticomm (v : Fin 4 → ℝ) (omega : Fin 4 → Fin 4 → ℝ) :
    bilinear restSpinor (gammaExpansion v*generator omega+generator omega*gammaExpansion v) restSpinor =
      (-Complex.I/2)*∑A,∑a,∑b, epsilon A a b 3*(v A:ℂ)*(omega a b:ℂ) := by
  have hexp : gammaExpansion v*generator omega+generator omega*gammaExpansion v =
      ∑A,∑a,∑b, ((v A:ℂ)*(-Complex.I*(omega a b:ℂ)/4)) •
        (gamma A*sigma a b+sigma a b*gamma A) := by
    simp only [gammaExpansion, Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _
    simp only [generator, Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
  rw [hexp]
  simp only [bilinear_sum, bilinear_smul_matrix, rest_gamma_sigma_anticomm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The actual polar-spinor connection anticommutator has the source negative imaginary half-density epsilon contraction. -/
theorem polar_connection_anticommutator (rho beta : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hunit : IsUnit L) (hiso : diracAdjoint L*L=1)
    (h5 : Commute L gamma5) (hu : ∀A, L*gamma A*L⁻¹=gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → ℝ) (mu : Fin 4) :
    bilinear (polarSpinor rho beta L)
      (gamma mu*transportedGenerator L omega+transportedGenerator L omega*gamma mu)
      (polarSpinor rho beta L) =
      (-Complex.I*(rho:ℂ)/2)*∑A,∑a,∑b,
        epsilon A a b 3*(inverseCoefficients u mu A:ℂ)*(omega a b:ℂ) := by
  have hleft := Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hK : Commute (transportedGenerator L omega) gamma5 :=
    (h5.mul_left (generator_gamma5_commute omega)).mul_left (inverse_commute hunit h5)
  rw [polar_bilinear rho beta L _ hrho, chiral_connection_cancel beta mu hK,
    ← inverse_eq_diracAdjoint hiso]
  have ht : L⁻¹*(gamma mu*transportedGenerator L omega+
      transportedGenerator L omega*gamma mu)*L =
      (L⁻¹*gamma mu*L)*generator omega+generator omega*(L⁻¹*gamma mu*L) := by
    simp only [transportedGenerator, mul_add, add_mul]
    simp only [mul_assoc, hleft, mul_one]
    simp only [← mul_assoc, hleft, one_mul]
  rw [ht, inverse_expansion hunit hu, generator_rest_anticomm]
  ring


/-- The real oriented Levi-Civita coefficient uses signed differences after coercing every index to the real numbers. -/
def epsilonReal (a b c d : Fin 4) : ℝ :=
  (((b.val : ℝ) - a.val) * ((c.val : ℝ) - a.val) * ((d.val : ℝ) - a.val) *
    ((c.val : ℝ) - b.val) * ((d.val : ℝ) - b.val) * ((d.val : ℝ) - c.val)) / 12

/-- The real Levi-Civita coefficient casts faithfully to the previously verified complex epsilon. -/
theorem epsilonReal_cast (a b c d : Fin 4) : (epsilonReal a b c d : ℂ) = epsilon a b c d := by
  simp only [epsilonReal, epsilon, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat]

/-- The real canonical connection contraction uses the physical inverse-frame coefficients and the source hbar c over four factor. -/
def canonicalContraction (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  hbar*c/4 * ∑mu,∑A,∑a,∑b,
    epsilonReal A a b 3 * inverseCoefficients u mu A * omega mu a b

/-- Antisymmetry reduces the actual oriented epsilon contraction to twice its three surviving cyclic terms. -/
theorem epsilon_three_terms (v : Covector) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) :
    (∑A,∑a,∑b, epsilonReal A a b 3*v A*omega a b) =
      2*(v 0*omega 1 2+v 1*omega 2 0+v 2*omega 0 1) := by
  norm_num [epsilonReal, Fin.sum_univ_succ]
  rw [hanti 2 1, hanti 0 2, hanti 1 0]
  ring

/-- The real canonical contraction has exactly the source temporal rotation and two transverse boost terms. -/
theorem canonicalContraction_three_terms (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hanti : ∀mu a b, omega mu a b = -omega mu b a) :
    canonicalContraction hbar c u omega = hbar*c/2 * ∑mu,
      (inverseCoefficients u mu 0*omega mu 1 2 +
       inverseCoefficients u mu 1*omega mu 2 0 +
       inverseCoefficients u mu 2*omega mu 0 1) := by
  unfold canonicalContraction
  simp_rw [epsilon_three_terms (fun A => inverseCoefficients u _ A) _ (hanti _)]
  rw [← Finset.mul_sum]
  ring

/-- The actual symmetric Dirac kinetic prefactor converts the full polar connection contraction to density times its real canonical value. -/
theorem connection_kinetic_sum (rho beta hbar c : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hunit : IsUnit L) (hiso : diracAdjoint L*L=1)
    (h5 : Commute L gamma5) (hu : ∀A, L*gamma A*L⁻¹=gammaExpansion (u A))
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (Complex.I*(hbar:ℂ)*(c:ℂ)/2) * ∑mu,
      bilinear (polarSpinor rho beta L)
        (gamma mu*transportedGenerator L (omega mu)+transportedGenerator L (omega mu)*gamma mu)
        (polarSpinor rho beta L) = ((rho*canonicalContraction hbar c u omega : ℝ):ℂ) := by
  simp_rw [polar_connection_anticommutator rho beta hrho hunit hiso h5 hu]
  rw [← Finset.mul_sum]
  simp only [canonicalContraction]
  push_cast
  simp only [epsilonReal_cast]
  ring_nf
  norm_num
end FoliationQM.PolarConnectionContraction
