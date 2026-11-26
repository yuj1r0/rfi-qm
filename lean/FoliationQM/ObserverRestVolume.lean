module

public import FoliationQM.GeometricLorentzFrame
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Local rest volume of an observer's spatial tangent parallelepiped

For v13 `eq:jacobian_density`, use an inertial observer's rest coordinates
with x⁰ = ct. Parallel projection along the particle velocity carries the
observer's spatial directions into the hyperplane orthogonal to that
velocity. The metric Gram determinant computes the induced rest volume.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverRestVolume

open Matrix GeometricLorentzFrame
open scoped BigOperators Matrix

/-- The three spatial unit vectors in the observer's rest coordinates. -/
def labBasis (i : Fin 3) : Covector := Pi.single i.succ 1

/-- Projection along the raised velocity U to the rest hyperplane of a normalized particle. -/
def project (c : ℝ) (U v : Covector) : Covector := v - (minkowski U v / c^2) • U

/-- Image of the i-th laboratory spatial direction under the rest projection. -/
def projected (c : ℝ) (U : Covector) (i : Fin 3) : Covector := project c U (labBasis i)

/-- Gram matrix for the positive spatial metric −η on a triple of raised tangent vectors. -/
def spatialGram (v : Fin 3 → Covector) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => -minkowski (v i) (v j)

/-- Induced rest-space Gram matrix of the three projected laboratory unit vectors. -/
def gram (c : ℝ) (U : Covector) : Matrix (Fin 3) (Fin 3) ℝ := spatialGram (projected c U)

private theorem sub_multiple (x y z : Covector) (a : ℝ) :
    minkowski x (y - a • z) = minkowski x y - a * minkowski x z := by
  simp [minkowski]
  ring

private theorem symmetry (x y : Covector) : minkowski x y = minkowski y x := by
  simp [minkowski, mul_comm]

/-- Each projected vector lies in the particle's rest hyperplane. -/
theorem project_orthogonal {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) (v : Covector) : minkowski U (project c U v) = 0 := by
  rw [project, sub_multiple, hU]
  field_simp [hc.ne']
  ring

/-- Every tangent of the particle's rest hyperplane comes from a unique simultaneous
laboratory tangent by projection along the particle trajectory. -/
theorem existsUnique_lab_preimage {c : ℝ} {U w : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) (hf : 0 < U 0) (hw : minkowski U w = 0) :
    ∃! v : Covector, v 0 = 0 ∧ project c U v = w := by
  let a := w 0 / U 0
  have ha : a * U 0 = w 0 := div_mul_cancel₀ _ hf.ne'
  refine ⟨w - a • U, ⟨?_, ?_⟩, ?_⟩
  · change w 0 - a * U 0 = 0
    rw [ha, sub_self]
  · rw [project, sub_multiple, hw, hU, zero_sub]
    have he : -(a*c^2)/c^2 = -a := by field_simp [hc.ne']
    rw [he, neg_smul]
    abel
  · rintro v ⟨hv, he⟩
    let b := minkowski U v / c^2
    have ht := congrFun he 0
    change v 0 - b * U 0 = w 0 at ht
    have hab : a = -b := (div_eq_iff hf.ne').mpr (by rw [← ht, hv]; ring)
    ext i
    have hi := congrFun he i
    change v i - b * U i = w i at hi
    change v i = w i - a * U i
    rw [hab, ← hi]
    ring

/-- The projection transports the laboratory inner products by the velocity-dependent correction. -/
theorem projected_pairing {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) (v w : Covector) :
    minkowski (project c U v) (project c U w) =
      minkowski v w - minkowski U v * minkowski U w / c^2 := by
  rw [show project c U v = v - (minkowski U v / c^2) • U from rfl,
    symmetry _ (project c U w), sub_multiple, symmetry (project c U w) U, project_orthogonal hc hU,
    mul_zero, sub_zero, symmetry (project c U w) v, project, sub_multiple, symmetry v U]
  ring

private theorem lab_pairing (v : Covector) (i : Fin 3) : minkowski v (labBasis i) = -v i.succ := by
  fin_cases i <;> simp [labBasis, minkowski]

/-- The spatial Gram entries are δᵢⱼ + Uⁱ Uʲ/c² in observer rest coordinates. -/
theorem gram_entry {c : ℝ} {U : Covector} (hc : 0 < c) (hU : minkowski U U = c^2)
    (i j : Fin 3) :
    gram c U i j = (if i = j then 1 else 0) + U i.succ * U j.succ / c^2 := by
  change -minkowski (project c U (labBasis i)) (project c U (labBasis j)) = _
  rw [projected_pairing hc hU, lab_pairing, lab_pairing, lab_pairing]
  simp [labBasis, Pi.single_apply, eq_comm, add_comm]

/-- The induced spatial Gram matrix is positive definite. -/
theorem gram_posDef {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) : (gram c U).PosDef := by
  let a : Fin 3 → ℝ := fun i => U i.succ / c
  have H : gram c U = 1 + vecMulVec a (star a) := by
    ext i j
    rw [gram_entry hc hU]
    simp [Matrix.one_apply, vecMulVec, a, div_mul_div_comm, pow_two]
  rw [H]
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_vecMulVec_self_star a)

/-- The projected spatial vectors form a linearly independent triple in the rest hyperplane. -/
theorem projected_independent {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) : LinearIndependent ℝ (projected c U) := by
  apply Fintype.linearIndependent_iff.mpr
  intro w hw i
  have hn : gram c U *ᵥ w = 0 := by
    ext j
    have hj := congrArg (minkowskiForm (projected c U j)) hw
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, minkowskiForm_apply] at hj
    change ∑ k, -minkowski (projected c U j) (projected c U k) * w k = 0
    simp only [neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
    simpa only [mul_comm] using hj
  have hw0 : w = 0 := by
    by_contra ne
    have hp := (gram_posDef hc hU).dotProduct_mulVec_pos ne
    simp [hn] at hp
  rw [hw0]
  rfl

/-- The actual Gram determinant of a projected laboratory unit cell is the squared boost factor. -/
theorem gram_det {c : ℝ} {U : Covector} (hc : 0 < c) (hU : minkowski U U = c^2) :
    (gram c U).det = (U 0 / c)^2 := by
  have he : (gram c U).det = 1 + ((U 1)^2 + (U 2)^2 + (U 3)^2) / c^2 := by
    rw [Matrix.det_fin_three]
    norm_num [gram_entry hc hU]
    ring
  rw [he, div_pow]
  field_simp [hc.ne']
  unfold minkowski at hU
  nlinarith

/-- The rest volume of the unit laboratory cell is γ = U⁰/c on the future branch. -/
theorem sqrt_gram_det {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) (hf : 0 < U 0) :
    Real.sqrt (gram c U).det = U 0 / c := by
  rw [gram_det hc hU, Real.sqrt_sq (div_pos hf hc).le]

/-- A triple of tangents with coefficient columns A relative to the supplied spatial vectors. -/
def combine (v : Fin 3 → Covector) (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : Covector :=
  ∑ j, A j i • v j

/-- Projection commutes with forming an arbitrary tangent edge from laboratory components. -/
theorem project_combine (c : ℝ) (U : Covector) (v : Fin 3 → Covector)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    project c U (combine v A i) = combine (fun j => project c U (v j)) A i := by
  ext k
  simp [project, combine, ← minkowskiForm_apply, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem gram_combine (v : Fin 3 → Covector) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    spatialGram (combine v A) = A.transpose * spatialGram v * A := by
  ext i j
  simp [spatialGram, combine, Matrix.mul_apply, Matrix.transpose_apply, ← minkowskiForm_apply,
    Fin.sum_univ_succ, smul_eq_mul]
  ring

/-- The laboratory volume |det A| is the square root of the Gram determinant
of the actual spacetime tangents in the observer's simultaneous hyperplane. -/
theorem lab_volume (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Real.sqrt (spatialGram (combine labBasis A)).det = |A.det| := by
  have hg : spatialGram labBasis = 1 := by
    ext i j
    change -minkowski (labBasis i) (labBasis j) = _
    rw [lab_pairing, neg_neg]
    simp [labBasis, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [gram_combine, hg, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose,
    ← pow_two, Real.sqrt_sq_eq_abs]

/-- Each laboratory parallelepiped has rest-space volume γ times its ordinary volume |det A|.
The identity includes singular triples. -/
theorem parallelepiped_volume {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c^2) (hf : 0 < U 0) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Real.sqrt (spatialGram (combine (projected c U) A)).det = U 0 / c * |A.det| := by
  rw [gram_combine, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  change Real.sqrt (A.det * (gram c U).det * A.det) = _
  rw [gram_det hc hU]
  rw [show A.det * (U 0/c)^2 * A.det = (U 0/c)^2 * A.det^2 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hf hc).le, Real.sqrt_sq_eq_abs]

end FoliationQM.ObserverRestVolume
