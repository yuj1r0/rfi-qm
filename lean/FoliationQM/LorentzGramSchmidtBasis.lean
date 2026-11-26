module
public import FoliationQM.LorentzGramSchmidt
public import FoliationQM.LorentzGramFamily
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Orientation

/-!
# Actual basis and orientation of signed Lorentz Gram--Schmidt

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
The explicit normalized vectors have an upper triangular coordinate matrix
in the independent seed basis. Its diagonal entries are exactly the actual
normalization factors, so the determinant is their strictly positive
product on the genuine signed-pivot domain. The proved Gram identity gives
an actual output basis, and the positive determinant proves preservation
of the original exterior-form orientation. Neither the output basis nor
its determinant or orientation is supplied as an input.
-/

@[expose] public section
noncomputable section
open Matrix Module
namespace FoliationQM.LorentzGramSchmidtBasis
open LorentzGramSchmidt SignedMetricProjection LorentzMatrixGroup

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : LinearMap.BilinForm ℝ V) (seed : Basis (Fin 4) ℝ V)

private theorem coordinate_normalize (ε : ℝ) (v : V) (i : Fin 4) :
    seed.repr (normalize g ε v) i = scale g ε v * seed.repr v i := by
  simp [SignedMetricProjection.normalize]

private theorem coordinate_residual (ε : ℝ) (e v : V) (i : Fin 4) :
    seed.repr (residual g ε e v) i = seed.repr v i - (ε * g e v) * seed.repr e i := by
  rw [residual_apply]
  simp

private theorem coordinate_e0 (i : Fin 4) :
    seed.repr (e0 g seed) i = factor g seed 0 * (if (0 : Fin 4) = i then 1 else 0) := by
  change seed.repr (normalize g 1 (seed 0)) i =
    scale g 1 (seed 0) * (if (0 : Fin 4) = i then 1 else 0)
  rw [coordinate_normalize]
  simp only [Basis.repr_self, Finsupp.single_apply]

private theorem coordinate_e1 (i : Fin 4) (hi : 1 ≤ i) :
    seed.repr (e1 g seed) i = factor g seed 1 * (if (1 : Fin 4) = i then 1 else 0) := by
  change seed.repr (normalize g (-1) (residual g 1 (e0 g seed) (seed 1))) i =
    scale g (-1) (u1 g seed) * (if (1 : Fin 4) = i then 1 else 0)
  rw [coordinate_normalize, coordinate_residual, coordinate_e0]
  have hz : (0 : Fin 4) ≠ i := by omega
  simp only [hz, ite_false, mul_zero, sub_zero, Basis.repr_self, Finsupp.single_apply]
  rfl

private theorem coordinate_e2 (i : Fin 4) (hi : 2 ≤ i) :
    seed.repr (e2 g seed) i = factor g seed 2 * (if (2 : Fin 4) = i then 1 else 0) := by
  change seed.repr (normalize g (-1)
    (residual g (-1) (e1 g seed) (residual g 1 (e0 g seed) (seed 2)))) i =
    scale g (-1) (u2 g seed) * (if (2 : Fin 4) = i then 1 else 0)
  rw [coordinate_normalize, coordinate_residual, coordinate_residual,
    coordinate_e1 g seed i (by omega), coordinate_e0]
  have h0 : (0 : Fin 4) ≠ i := by omega
  have h1 : (1 : Fin 4) ≠ i := by omega
  simp only [h0, h1, ite_false, mul_zero, sub_zero, Basis.repr_self, Finsupp.single_apply]
  rfl

private theorem coordinate_e3 (i : Fin 4) (hi : 3 ≤ i) :
    seed.repr (e3 g seed) i = factor g seed 3 * (if (3 : Fin 4) = i then 1 else 0) := by
  change seed.repr (normalize g (-1) (residual g (-1) (e2 g seed)
    (residual g (-1) (e1 g seed) (residual g 1 (e0 g seed) (seed 3))))) i =
    scale g (-1) (u3 g seed) * (if (3 : Fin 4) = i then 1 else 0)
  rw [coordinate_normalize, coordinate_residual, coordinate_residual, coordinate_residual,
    coordinate_e2 g seed i (by omega), coordinate_e1 g seed i (by omega), coordinate_e0]
  have h0 : (0 : Fin 4) ≠ i := by omega
  have h1 : (1 : Fin 4) ≠ i := by omega
  have h2 : (2 : Fin 4) ≠ i := by omega
  simp only [h0, h1, h2, ite_false, mul_zero, sub_zero, Basis.repr_self, Finsupp.single_apply]
  rfl

/-- The actual matrix of normalized output vectors in the independent seed basis, defined before any output-basis conclusion. -/
def changeMatrix : Matrix (Fin 4) (Fin 4) ℝ := seed.toMatrix (frame g seed)

/-- Entries on or below the diagonal of the actual coordinate matrix are exactly its normalization factors times the corresponding Kronecker entry. -/
theorem change_entry_of_le (i j : Fin 4) (h : j ≤ i) :
    changeMatrix g seed i j = factor g seed j * (if j = i then 1 else 0) := by
  change seed.repr (frame g seed j) i = _
  fin_cases j
  · exact coordinate_e0 g seed i
  · exact coordinate_e1 g seed i h
  · exact coordinate_e2 g seed i h
  · exact coordinate_e3 g seed i h

/-- Every entry below the diagonal of the actual normalized-family coordinate matrix vanishes, without a pivot or symmetry premise. -/
theorem change_isUpperTriangular : (changeMatrix g seed).IsUpperTriangular := by
  intro i j h
  rw [change_entry_of_le g seed i j (le_of_lt h), ite_eq_right (show j ≠ i from ne_of_lt h), mul_zero]

/-- Each actual diagonal coordinate is the corresponding normalization factor computed from its signed metric residual. -/
theorem change_diagonal (i : Fin 4) : changeMatrix g seed i i = factor g seed i := by
  rw [change_entry_of_le g seed i i le_rfl, ite_eq_left rfl, mul_one]

/-- The determinant of the actual normalized-family coordinate matrix is precisely the product of its four computed normalization factors. -/
theorem change_det : (changeMatrix g seed).det = ∏ i : Fin 4, factor g seed i := by
  rw [Matrix.det_of_isUpperTriangular (change_isUpperTriangular g seed)]
  simp only [change_diagonal]

/-- The genuine signed-pivot inequalities make the actual normalization determinant strictly positive. -/
theorem change_det_pos (hGood : Good g seed) : 0 < (changeMatrix g seed).det := by
  rw [change_det]
  exact Finset.prod_pos (fun i _ => factor_pos g seed hGood i)

/-- The verified Gram identity and the independent seed dimension construct an actual basis whose vectors are the computed signed Gram--Schmidt outputs. -/
def normalizedBasis (hg : g.IsSymm) (hGood : Good g seed) : Basis (Fin 4) ℝ V :=
  LorentzGramFamily.basisOfGram g (frame g seed) (gram g seed hg hGood) seed

/-- The constructed actual output basis has exactly the original algorithm's vector at every index. -/
theorem normalizedBasis_apply (hg : g.IsSymm) (hGood : Good g seed) (i : Fin 4) :
    normalizedBasis g seed hg hGood i = frame g seed i :=
  LorentzGramFamily.basisOfGram_apply g (frame g seed) (gram g seed hg hGood) seed i

/-- The actual output basis has exactly the Lorentz Gram matrix in the original geometric bilinear metric. -/
theorem normalizedBasis_gram (hg : g.IsSymm) (hGood : Good g seed) :
    g.toMatrix (normalizedBasis g seed hg hGood) = eta :=
  LorentzGramFamily.basisOfGram_gram g (frame g seed) (gram g seed hg hGood) seed

/-- The genuine change matrix of the constructed output basis is the previously computed normalized-family matrix. -/
theorem normalizedBasis_toMatrix (hg : g.IsSymm) (hGood : Good g seed) :
    seed.toMatrix (normalizedBasis g seed hg hGood) = changeMatrix g seed := by
  ext i j
  simp only [Basis.toMatrix_apply, normalizedBasis_apply, changeMatrix]

/-- The actual output basis retains the independent seed basis's exterior-form orientation, as a consequence of the proved strictly positive determinant. -/
theorem orientation (hg : g.IsSymm) (hGood : Good g seed) :
    (normalizedBasis g seed hg hGood).orientation = seed.orientation := by
  apply Eq.symm
  apply (Basis.orientation_eq_iff_det_pos seed (normalizedBasis g seed hg hGood)).mpr
  rw [Basis.det_apply, normalizedBasis_toMatrix]
  exact change_det_pos g seed hGood

/-- At an already Lorentz-normalized seed, the actual constructed basis is exactly the supplied seed basis, including its ordering and vectors. -/
theorem normalizedBasis_eq_of_gram (hg : g.IsSymm)
    (hs : ∀ i j : Fin 4, g (seed i) (seed j) = eta i j) :
    normalizedBasis g seed hg (good_of_gram g seed hs) = seed := by
  apply DFunLike.ext
  intro i
  rw [normalizedBasis_apply, frame_eq_of_gram g seed hs]

end FoliationQM.LorentzGramSchmidtBasis
