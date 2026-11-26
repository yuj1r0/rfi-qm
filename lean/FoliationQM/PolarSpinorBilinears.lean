module

public import FoliationQM.ChiralMatrix
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual bilinears of the forward polar spinor ansatz

Source: v13 `sec:spinor`, `prop:takabayasi`. The spinor below is the actual
matrix action of the full-angle chiral factor and a matrix `L` on the fixed
rest spinor. Its scalar formulas use explicit Dirac-isometry and gamma5
commutation hypotheses on `L`. The vector and axial formulas retain the
actual conjugated gamma matrices, and their coefficient projections require
an actual real gamma-matrix expansion.

These are forward algebraic identities for the stated ansatz. They do not
assert existence or uniqueness of a polar decomposition for an arbitrary
nonzero spinor, or classify all matrices in the spin group.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.PolarSpinorBilinears
open DiracMatrices DiracAdjoint ChiralMatrix Matrix

/-- The actual polar ansatz with real density, full chiral angle and matrix factor. -/
def polarSpinor (rho beta : ℝ) (L : Mat) : Spinor :=
  (Real.sqrt rho : ℂ) • ((chiral beta*L).mulVec restSpinor)

/-- Moving two actual matrix actions into the bilinear takes the left Dirac adjoint. -/
theorem bilinear_mulVec_both (psi chi : Spinor) (A B C : Mat) :
    bilinear (A.mulVec psi) B (C.mulVec chi) =
      bilinear psi (diracAdjoint A*B*C) chi := by
  rw [bilinear_mulVec_left, ← bilinear_mul_matrix]

/-- Two real square-root amplitudes contribute exactly the nonnegative density. -/
theorem bilinear_sqrt_smul (rho : ℝ) (hrho : 0 ≤ rho)
    (psi chi : Spinor) (A : Mat) :
    bilinear ((Real.sqrt rho : ℂ) • psi) A ((Real.sqrt rho : ℂ) • chi) =
      (rho : ℂ)*bilinear psi A chi := by
  rw [bilinear_smul_left, bilinear_smul_right]
  simp only [Complex.star_def, Complex.conj_ofReal, ← mul_assoc]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt hrho

/-- The gamma5 bilinear matrix is fixed by a commuting Dirac isometry. -/
theorem diracAdjoint_mul_gamma5_mul (L : Mat)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    diracAdjoint L*gamma5*L=gamma5 := by
  rw [mul_assoc, ← h5.eq, ← mul_assoc, hL, one_mul]

private theorem even_sandwich (L : Mat) (hL : diracAdjoint L*L=1)
    (h5 : Commute L gamma5) (a b : ℂ) :
    diracAdjoint L*(a • (1 : Mat)+b • gamma5)*L =
      a • (1 : Mat)+b • gamma5 := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hL,
    diracAdjoint_mul_gamma5_mul L hL h5]

/-- Every actual polar bilinear reduces to a conjugated chiral sandwich at the rest spinor. -/
theorem polar_bilinear (rho beta : ℝ) (L A : Mat) (hrho : 0 ≤ rho) :
    bilinear (polarSpinor rho beta L) A (polarSpinor rho beta L) =
      (rho : ℂ)*bilinear restSpinor
        (diracAdjoint L*(chiral beta*A*chiral beta)*L) restSpinor := by
  unfold polarSpinor
  rw [bilinear_sqrt_smul rho hrho, bilinear_mulVec_both,
    diracAdjoint_mul, chiral_diracAdjoint]
  congr 2
  noncomm_ring

/-- The actual gamma5 chiral sandwich has the complementary scalar and pseudoscalar coefficients. -/
theorem chiral_gamma5_sandwich (beta : ℝ) :
    chiral beta*gamma5*chiral beta =
      (Real.cos beta : ℂ) • gamma5 + (Complex.I*(Real.sin beta : ℂ)) • (1 : Mat) := by
  calc
    _ = (chiral beta*chiral beta)*gamma5 := by
      rw [mul_assoc, ← (chiral_gamma5_commute beta).eq, ← mul_assoc]
    _ = _ := by rw [chiral_squared]; simp [add_mul, gamma5_sq]

/-- The actual scalar bilinear of the polar ansatz is density times cosine of the full chiral angle. -/
theorem polar_scalar (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    bilinear (polarSpinor rho beta L) 1 (polarSpinor rho beta L) =
      (rho : ℂ)*(Real.cos beta : ℂ) := by
  rw [polar_bilinear rho beta L 1 hrho, mul_one, chiral_squared,
    even_sandwich L hL h5]
  simp [bilinear_add_matrix, bilinear_smul_matrix, rest_scalar, rest_pseudoscalar]

/-- The actual gamma5 bilinear of the polar ansatz has the source positive imaginary sine sign. -/
theorem polar_gamma5 (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    bilinear (polarSpinor rho beta L) gamma5 (polarSpinor rho beta L) =
      Complex.I*((rho : ℂ)*(Real.sin beta : ℂ)) := by
  rw [polar_bilinear rho beta L gamma5 hrho, chiral_gamma5_sandwich, add_comm,
    even_sandwich L hL h5]
  simp only [bilinear_add_matrix, bilinear_smul_matrix, rest_scalar,
    rest_pseudoscalar, mul_one, mul_zero, add_zero]
  ring

/-- The source signed pseudoscalar minus i times the gamma5 bilinear equals density times sine. -/
theorem polar_pseudoscalar (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    -Complex.I*bilinear (polarSpinor rho beta L) gamma5 (polarSpinor rho beta L) =
      (rho : ℂ)*(Real.sin beta : ℂ) := by
  rw [polar_gamma5 rho beta L hrho hL h5]
  simp [← mul_assoc]

/-- The real scalar invariant of the actual polar spinor is rho cos beta. -/
theorem polar_scalar_re (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    (bilinear (polarSpinor rho beta L) 1 (polarSpinor rho beta L)).re =
      rho*Real.cos beta := by
  rw [polar_scalar rho beta L hrho hL h5]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The real signed pseudoscalar invariant of the actual polar spinor is rho sin beta. -/
theorem polar_pseudoscalar_re (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    (-Complex.I*bilinear (polarSpinor rho beta L) gamma5 (polarSpinor rho beta L)).re =
      rho*Real.sin beta := by
  rw [polar_pseudoscalar rho beta L hrho hL h5]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The source positive-density domain gives both actual real polar invariants simultaneously. -/
theorem polar_invariants_of_pos (rho beta : ℝ) (L : Mat) (hrho : 0 < rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    (bilinear (polarSpinor rho beta L) 1 (polarSpinor rho beta L)).re = rho*Real.cos beta ∧
    (-Complex.I*bilinear (polarSpinor rho beta L) gamma5 (polarSpinor rho beta L)).re =
      rho*Real.sin beta :=
  ⟨polar_scalar_re rho beta L hrho.le hL h5,
    polar_pseudoscalar_re rho beta L hrho.le hL h5⟩

/-- Actual chiral factors cancel from every vector bilinear for any pair of spinors. -/
theorem chiral_vector_bilinear (beta : ℝ) (a : Fin 4) (psi chi : Spinor) :
    bilinear ((chiral beta).mulVec psi) (gamma a) ((chiral beta).mulVec chi) =
      bilinear psi (gamma a) chi := by
  rw [bilinear_mulVec_both, chiral_diracAdjoint, chiral_gamma_cancel]

/-- Actual chiral factors also cancel from every axial bilinear for any pair of spinors. -/
theorem chiral_axial_bilinear (beta : ℝ) (a : Fin 4) (psi chi : Spinor) :
    bilinear ((chiral beta).mulVec psi) (gamma a*gamma5) ((chiral beta).mulVec chi) =
      bilinear psi (gamma a*gamma5) chi := by
  rw [bilinear_mulVec_both, chiral_diracAdjoint, chiral_axial_cancel]

/-- The polar vector bilinear is density times the actual conjugated gamma bilinear at rest. -/
theorem polar_vector (rho beta : ℝ) (L : Mat) (a : Fin 4) (hrho : 0 ≤ rho) :
    bilinear (polarSpinor rho beta L) (gamma a) (polarSpinor rho beta L) =
      (rho : ℂ)*bilinear restSpinor (diracAdjoint L*gamma a*L) restSpinor := by
  rw [polar_bilinear rho beta L (gamma a) hrho, chiral_gamma_cancel]

/-- The polar axial bilinear is density times the actual conjugated axial matrix bilinear at rest. -/
theorem polar_axial (rho beta : ℝ) (L : Mat) (a : Fin 4) (hrho : 0 ≤ rho) :
    bilinear (polarSpinor rho beta L) (gamma a*gamma5) (polarSpinor rho beta L) =
      (rho : ℂ)*bilinear restSpinor (diracAdjoint L*(gamma a*gamma5)*L) restSpinor := by
  rw [polar_bilinear rho beta L (gamma a*gamma5) hrho, chiral_axial_cancel]

/-- Commuting with gamma5 gives the source axial formula using the same transported gamma matrix. -/
theorem polar_axial_transport (rho beta : ℝ) (L : Mat) (a : Fin 4)
    (hrho : 0 ≤ rho) (h5 : Commute L gamma5) :
    bilinear (polarSpinor rho beta L) (gamma a*gamma5) (polarSpinor rho beta L) =
      (rho : ℂ)*bilinear restSpinor ((diracAdjoint L*gamma a*L)*gamma5) restSpinor := by
  rw [polar_axial rho beta L a hrho]
  congr 2
  calc
    _ = diracAdjoint L*gamma a*(gamma5*L) := by noncomm_ring
    _ = _ := by rw [← h5.eq]; noncomm_ring

/-- The actual spinor bilinear commutes with the finite sum of gamma-expansion matrices. -/
theorem bilinear_sum (psi chi : Spinor) (A : Fin 4 → Mat) :
    bilinear psi (∑ a, A a) chi = ∑ a, bilinear psi (A a) chi := by
  simp only [bilinear, Matrix.mul_sum, Matrix.sum_mulVec, dotProduct_sum]

/-- A real gamma expansion has rest-vector projection equal to its temporal coefficient. -/
theorem rest_vector_projection (u : Fin 4 → ℝ) :
    bilinear restSpinor (∑ a, (u a : ℂ) • gamma a) restSpinor = (u 0 : ℂ) := by
  rw [bilinear_sum]
  simp only [bilinear_smul_matrix, rest_vector]
  simp

/-- A real gamma expansion has rest-axial projection equal to its third spatial coefficient. -/
theorem rest_axial_projection (u : Fin 4 → ℝ) :
    bilinear restSpinor ((∑ a, (u a : ℂ) • gamma a)*gamma5) restSpinor = (u 3 : ℂ) := by
  rw [Matrix.sum_mul, bilinear_sum]
  simp only [smul_mul_assoc, bilinear_smul_matrix, rest_axial]
  simp

/-- An actual real gamma expansion identifies the polar vector component with rho times its temporal coefficient. -/
theorem polar_vector_projection (rho beta : ℝ) (L : Mat) (a : Fin 4)
    (hrho : 0 ≤ rho) (u : Fin 4 → ℝ)
    (hu : diracAdjoint L*gamma a*L = ∑ b, (u b : ℂ) • gamma b) :
    bilinear (polarSpinor rho beta L) (gamma a) (polarSpinor rho beta L) =
      (rho : ℂ)*(u 0 : ℂ) := by
  rw [polar_vector rho beta L a hrho, hu, rest_vector_projection]

/-- An actual real gamma expansion identifies the polar axial component with rho times its third spatial coefficient. -/
theorem polar_axial_projection (rho beta : ℝ) (L : Mat) (a : Fin 4)
    (hrho : 0 ≤ rho) (h5 : Commute L gamma5) (u : Fin 4 → ℝ)
    (hu : diracAdjoint L*gamma a*L = ∑ b, (u b : ℂ) • gamma b) :
    bilinear (polarSpinor rho beta L) (gamma a*gamma5) (polarSpinor rho beta L) =
      (rho : ℂ)*(u 3 : ℂ) := by
  rw [polar_axial_transport rho beta L a hrho h5, hu, rest_axial_projection]

/-- Increasing the full chiral angle by two pi negates the actual polar spinor. -/
theorem polarSpinor_add_two_pi (rho beta : ℝ) (L : Mat) :
    polarSpinor rho (beta+2*Real.pi) L = -polarSpinor rho beta L := by
  simp [polarSpinor, chiral_add_two_pi, Matrix.neg_mulVec]

/-- The source simultaneous chiral-angle shift and matrix sign flip leaves the actual spinor unchanged. -/
theorem polarSpinor_shift_neg (rho beta : ℝ) (L : Mat) :
    polarSpinor rho (beta+2*Real.pi) (-L) = polarSpinor rho beta L := by
  simp [polarSpinor, chiral_add_two_pi]

/-- The actual polar spinor is four-pi periodic in its full chiral angle. -/
theorem polarSpinor_periodic (rho : ℝ) (L : Mat) :
    Function.Periodic (fun beta => polarSpinor rho beta L) (4*Real.pi) := by
  intro beta
  simp only [polarSpinor, chiral_periodic beta]

end FoliationQM.PolarSpinorBilinears
