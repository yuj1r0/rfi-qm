module
public import FoliationQM.LorentzMatrixGroup
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Actual families with Lorentz Gram matrix

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
Four actual vectors whose pairings have Gram matrix (+---) are linearly
independent, without assuming symmetry or nondegeneracy of the ambient
bilinear form. Their actual linear combinations have the stated Minkowski
pairing. An independently supplied four-element seed basis supplies the
ambient dimension and turns the family into a genuine basis with exactly
its original vectors. No spanning, basis, orientation, future-cone or Spin
conclusion is assumed as a premise for the new family.
-/

@[expose] public section
noncomputable section
open Matrix Module
namespace FoliationQM.LorentzGramFamily
open LorentzMatrixGroup RealLorentzFrame

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : LinearMap.BilinForm ℝ V) (X : Fin 4 → V)
  (hGram : ∀ a b : Fin 4, g (X a) (X b) = eta a b)

include hGram

/-- An actual four-vector family with Gram matrix (+---) is linearly independent, without a symmetry or dimension hypothesis. -/
theorem linearIndependent : LinearIndependent ℝ X := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := g)
  · intro i j hij
    change g (X i) (X j) = 0
    rw [hGram]
    simp [eta, hij]
  · intro i
    rw [hGram]
    fin_cases i <;> norm_num [eta, sign]

/-- The actual finite linear combinations of an eta-Gram family have precisely the Minkowski pairing of their four real coefficient vectors. -/
theorem metric_sum (v w : Covector) :
    g (∑ a : Fin 4, v a • X a) (∑ b : Fin 4, w b • X b) = minkowski v w := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp [hGram, eta, sign, Fin.sum_univ_succ, minkowski]
  ring

/-- An independent actual four-element seed basis supplies the dimension needed to turn the eta-Gram family into a genuine basis, with no spanning or new-family basis premise. -/
def basisOfGram (seed : Module.Basis (Fin 4) ℝ V) : Module.Basis (Fin 4) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent g X hGram)
    (Module.finrank_eq_card_basis seed).symm

/-- The basis constructed from the metric Gram identity has exactly the original family vectors. -/
theorem basisOfGram_apply (seed : Module.Basis (Fin 4) ℝ V) (a : Fin 4) :
    basisOfGram g X hGram seed a = X a := by
  simp [basisOfGram, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The resulting actual basis has the required Lorentz Gram matrix in the original bilinear metric. -/
theorem basisOfGram_gram (seed : Module.Basis (Fin 4) ℝ V) :
    g.toMatrix (basisOfGram g X hGram seed) = eta := by
  ext a b
  simpa only [LinearMap.BilinForm.toMatrix_apply, basisOfGram_apply] using hGram a b

end FoliationQM.LorentzGramFamily
