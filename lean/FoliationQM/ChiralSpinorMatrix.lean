module
public import FoliationQM.SpinorMatrix

/-!
# Chiral action in the concrete spinor matrix model

Source: v13 `eq:takabayasi_polar` and `prop:takabayasi`.
The actual chiral Dirac action is scalar multiplication by the complex
half-angle phase in the real-linear two-by-two model. These identities
connect the explicit source polar spinor to constructive reconstruction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.ChiralSpinorMatrix
open DiracMatrices ChiralMatrix SpinorMatrix PolarSpinorBilinears
private theorem chiral_coordinates (c s : ℝ) (psi : Spinor) :
    toMatrix ((((c:ℂ) • (1:Mat) + (Complex.I*(s:ℂ)) • gamma5)).mulVec psi) =
      ((c:ℂ) + Complex.I*(s:ℂ)) • toMatrix psi := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, gamma5_explicit, dotProduct, Fin.sum_univ_succ,
      star_add, star_sub, star_mul] <;> ring
/-- The actual chiral action becomes multiplication by the complex half-angle phase. -/
theorem toMatrix_chiral (beta : ℝ) (psi : Spinor) :
    toMatrix ((chiral beta).mulVec psi) =
      Complex.exp (Complex.I*(beta:ℂ)/2) • toMatrix psi := by
  have he : Complex.exp (Complex.I*(beta:ℂ)/2) =
      (Real.cos (beta/2):ℂ) + Complex.I*(Real.sin (beta/2):ℂ) := by
    rw [show Complex.I*(beta:ℂ)/2 = ((beta/2:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    ring
  rw [he]
  exact chiral_coordinates _ _ _
/-- Real complex scalar multiplication commutes with the actual matrix encoding. -/
theorem toMatrix_ofReal_smul (r : ℝ) (psi : Spinor) : toMatrix ((r:ℂ) • psi) = (r:ℂ) • toMatrix psi := by
  change toMatrix ((algebraMap ℝ ℂ r) • psi) = (algebraMap ℝ ℂ r) • toMatrix psi
  rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
  exact toMatrix_real_smul r psi
/-- The actual source polar spinor encodes as its amplitude-phase scalar times the spin-frame matrix. -/
theorem toMatrix_polarSpinor (rho beta : ℝ) (L : Mat) :
    toMatrix (polarSpinor rho beta L) =
      ((Real.sqrt rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ) / 2)) •
        toMatrix (L.mulVec restSpinor) := by
  rw [polarSpinor, toMatrix_ofReal_smul, ← Matrix.mulVec_mulVec, toMatrix_chiral,
    smul_smul]

end FoliationQM.ChiralSpinorMatrix
