module

public import FoliationQM.LatticeUnitaryTrajectory

/-!
# Hilbert norm of the regularization residual

The squared norm on the finite complex site space sums the local kinetic
residuals from v13 lines 215–229 without cancellation between sites. Its
rectangularly weighted version is obtained by scaling the norm by √h.
A common positive lower bound on the signed-amplitude magnitudes yields
an estimate proportional to ε² and the Euclidean norm of the radial stencil.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeResidualHilbertNorm

open LatticeSchrodingerResidual LatticeUnitaryPropagator LatticePolarStencil
open LatticeClockRegularization

/-- The source residual at all sites, viewed as a vector in the finite complex Hilbert space. -/
def residualState {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ) : Space n :=
  WithLp.toLp 2 (residual p h ε R φ)

/-- Euclidean norm of the full signed radial stencil. -/
def radialNorm {n : ℕ} (R φ : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (fun i => Complex.ofReal (radial R φ i))‖

/-- Square of the radial stencil norm is the sum of its real site squares. -/
theorem radialNorm_sq {n : ℕ} (R φ : Fin n → ℝ) :
    (radialNorm R φ)^2 = ∑ i, (radial R φ i)^2 := by
  rw [radialNorm, EuclideanSpace.norm_sq_eq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The exact full squared norm weights each site's radial stencil by the
fraction lost to regularization, with no lower bound required on any amplitude. -/
theorem norm_residualState_sq {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R φ : Fin n → ℝ) :
    ‖residualState p h ε R φ‖^2 =
      ∑ i, ((p.ellC*p.c/(2*h^2)) * defectFraction ε (R i) * radial R φ i)^2 := by
  rw [residualState, EuclideanSpace.norm_sq_eq]
  simp only [norm_residual, mul_pow, sq_abs]

/-- With the source's rectangular weights, multiplying the Hilbert norm by
√h gives the residual norm for the mesh measure. -/
theorem weighted_norm_residualState_sq {n : ℕ} (p : MassiveParameters) {h : ℝ}
    (hh : 0 ≤ h) (ε : ℝ) (R φ : Fin n → ℝ) :
    (Real.sqrt h * ‖residualState p h ε R φ‖)^2 =
      ∑ i, h * ((p.ellC*p.c/(2*h^2)) * defectFraction ε (R i) * radial R φ i)^2 := by
  rw [mul_pow, Real.sq_sqrt hh, norm_residualState_sq, Finset.mul_sum]

/-- On states whose site amplitudes have magnitudes at least δ > 0, the
residual is bounded by the radial norm times the physical coefficient and ε²/δ². -/
theorem norm_residualState_le {n : ℕ} (p : MassiveParameters) (h ε δ : ℝ)
    (R φ : Fin n → ℝ) (hδ : 0 < δ) (haway : ∀ i, δ ≤ |R i|) :
    ‖residualState p h ε R φ‖ ≤ (p.ellC*p.c/(2*h^2)) * (ε^2/δ^2) * radialNorm R φ := by
  let C := (p.ellC*p.c/(2*h^2)) * (ε^2/δ^2)
  have hC : 0 ≤ C := by
    have hl := ClockScales.ellC_pos p
    have hc := p.c_pos
    dsimp only [C]
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  change ‖residualState p h ε R φ‖^2 ≤ (C * radialNorm R φ)^2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, radialNorm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := pow_le_pow_left₀ (norm_nonneg _) (norm_residual_le_away p h ε δ R φ i hδ (haway i)) 2
  simpa only [residualState, PiLp.toLp_apply, C, mul_pow, sq_abs] using hi

end FoliationQM.LatticeResidualHilbertNorm
