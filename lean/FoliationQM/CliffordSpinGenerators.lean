module
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.Basic.Real.Basic

/-!
# Actual Clifford-spin elements from normalized vector pairs

Source scope: the abstract spin-group bridge supporting the concrete
Lorentz-frame representation in v13 `prop:takabayasi` and
`eq:tetrad_rotor_map`. These results apply to any real quadratic form.
Mathlib's Clifford star is reversion after grade involution; the actual
norm of a two-vector product is therefore the product of its two
quadratic values. Both equal positive and equal negative unit pairs
have norm one.

Membership is proved in Mathlib's existing spinGroup: explicit units
of nonisotropic embedded vectors lie in its generated Lipschitz
subgroup, their product is even, and both exact star-normalization
identities are established. The construction does not replace that
subgroup by a normalizer condition. It provides generic generators;
no representation faithfulness, surjectivity, connected-component,
or topological identification is asserted here.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.CliffordSpinGenerators
open CliffordAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private def vectorUnit (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    (CliffordAlgebra Q)ˣ where
  val := ι Q v
  inv := (Q v)⁻¹ • ι Q v
  val_inv := by
    rw [mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hv, one_smul]
  inv_val := by
    rw [smul_mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hv, one_smul]

private theorem vectorUnit_mem_lipschitz (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    vectorUnit Q v hv ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  exact ⟨v,rfl⟩

/-- The actual Clifford norm of a pair of vectors is the product of their quadratic values. -/
theorem pair_clifford_norm (Q : QuadraticForm ℝ V) (v w : V) :
    star (ι Q v * ι Q w) * (ι Q v * ι Q w) =
      algebraMap ℝ (CliffordAlgebra Q) (Q v * Q w) := by
  calc
    _ = ι Q w * (ι Q v * ι Q v) * ι Q w := by simp only [star_mul, star_ι, neg_mul_neg, mul_assoc]
    _ = Q v • (ι Q w * ι Q w) := by
      rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
        smul_mul_assoc]
    _ = algebraMap ℝ (CliffordAlgebra Q) (Q v * Q w) := by
      rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
        ← Algebra.algebraMap_eq_smul_one]

/-- A vector pair whose quadratic values multiply to one belongs to the actual
Mathlib spin group, including its generated-vector and strict normalization conditions. -/
theorem pair_mem_spinGroup (Q : QuadraticForm ℝ V) (v w : V)
    (h : Q v * Q w = 1) : ι Q v * ι Q w ∈ spinGroup Q := by
  have hv : Q v ≠ 0 := by intro he; rw [he, zero_mul] at h; exact zero_ne_one h
  have hw : Q w ≠ 0 := by intro he; rw [he, mul_zero] at h; exact zero_ne_one h
  refine ⟨⟨?_, ?_⟩, ι_mul_ι_mem_evenOdd_zero Q v w⟩
  · refine ⟨vectorUnit Q v hv * vectorUnit Q w hw, ?_, rfl⟩
    exact (lipschitzGroup Q).mul_mem
      (vectorUnit_mem_lipschitz Q v hv) (vectorUnit_mem_lipschitz Q w hw)
  · constructor
    · rw [pair_clifford_norm, h, map_one]
    · have he := pair_clifford_norm Q w v
      simpa [star_mul, mul_comm (Q w) (Q v), h] using he

/-- Two vectors of quadratic value one give an actual normalized even spin element. -/
theorem positive_pair_mem_spinGroup (Q : QuadraticForm ℝ V) (v w : V)
    (hv : Q v = 1) (hw : Q w = 1) : ι Q v * ι Q w ∈ spinGroup Q :=
  pair_mem_spinGroup Q v w (by rw [hv, hw, one_mul])

/-- Two vectors of quadratic value minus one give an actual normalized even spin element. -/
theorem negative_pair_mem_spinGroup (Q : QuadraticForm ℝ V) (v w : V)
    (hv : Q v = -1) (hw : Q w = -1) : ι Q v * ι Q w ∈ spinGroup Q :=
  pair_mem_spinGroup Q v w (by rw [hv, hw]; simp)

/-- The actual vector product bundled in the Mathlib spin group with all membership conditions proved. -/
def pair (Q : QuadraticForm ℝ V) (v w : V) (h : Q v * Q w = 1) : spinGroup Q :=
  ⟨ι Q v * ι Q w, pair_mem_spinGroup Q v w h⟩

/-- The bundled spin pair has exactly the original product of Clifford vector embeddings. -/
@[simp]
theorem pair_coe (Q : QuadraticForm ℝ V) (v w : V) (h : Q v * Q w = 1) :
    (pair Q v w h : CliffordAlgebra Q) = ι Q v * ι Q w := rfl

end FoliationQM.CliffordSpinGenerators
