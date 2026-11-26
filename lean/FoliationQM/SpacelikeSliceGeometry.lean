module

public import FoliationQM.RNCVolumeDensity
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Actual normal and volume of a spacelike coordinate slice

The negative spatial restriction of the full metric is the induced Gram
matrix. Its positive definiteness and the negative metric determinant give
the positive temporal inverse coefficient through the actual cofactor.
The metric dual of normalized coordinate time has unit length, is orthogonal
to every slice tangent, and gives the exact geometric current density.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpacelikeSliceGeometry

open Matrix LorentzMatrixGroup RNCVolumeDensity
open scoped BigOperators

/-- The actual positive Gram matrix of the three coordinate slice tangents. -/
def spatialGram (G : Mat4) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(G.submatrix Fin.succ Fin.succ)

/-- The inclusion of a spatial tangent into the full coordinate tangent space. -/
def sliceEmbed (z : Fin 3 → ℝ) : Covector := Fin.cons 0 z

/-- The local volume density of the induced spatial Gram matrix. -/
def sliceVolumeFactor (G : Mat4) : ℝ := Real.sqrt (spatialGram G).det

/-- The normalized coordinate-time covector. -/
def normalCovector (G : Mat4) : Covector :=
  Pi.single 0 (Real.sqrt ((G⁻¹) 0 0))⁻¹

/-- Raising the normalized time covector uses the entire inverse metric. -/
def normalVector (G : Mat4) : Covector := G⁻¹.mulVec (normalCovector G)

/-- The temporal inverse entry is the actual spatial principal cofactor ratio. -/
theorem inv_time_cofactor (G : Mat4) :
    (G⁻¹) 0 0 = (G.submatrix Fin.succ Fin.succ).det / G.det := by
  have hz : (0 : Fin 4).succAbove = (Fin.succ : Fin 3 → Fin 4) := by
    funext i
    exact Fin.zero_succAbove i
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.val_zero, zero_add, pow_zero,
    one_mul]
  rw [hz]
  ring

/-- The odd spatial dimension reverses the determinant sign of the spatial restriction. -/
theorem spatialGram_det (G : Mat4) :
    (spatialGram G).det = -(G.submatrix Fin.succ Fin.succ).det := by
  simp only [spatialGram, Matrix.det_neg, Fintype.card_fin]
  ring

variable {G : Mat4}

/-- A spacelike spatial Gram matrix and negative full determinant force a positive temporal inverse coefficient. -/
theorem inverse_time_pos (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    0 < (G⁻¹) 0 0 := by
  have hs : (G.submatrix Fin.succ Fin.succ).det < 0 := by
    have hp := hsp.det_pos
    rw [spatialGram_det] at hp
    linarith
  rw [inv_time_cofactor]
  exact div_pos_of_neg_of_neg hs hd

/-- The spatial Gram determinant equals the negative metric determinant times its temporal inverse coefficient. -/
theorem spatialGram_det_eq (hd : G.det < 0) :
    (spatialGram G).det = (-G.det) * (G⁻¹) 0 0 := by
  rw [spatialGram_det, inv_time_cofactor]
  field_simp [hd.ne]

/-- The induced spatial volume density is strictly positive on a spacelike slice. -/
theorem slice_volume_pos (hsp : (spatialGram G).PosDef) :
    0 < sliceVolumeFactor G := Real.sqrt_pos.mpr hsp.det_pos

/-- Dividing the actual induced volume by the normalizing inverse-metric factor gives the full coordinate volume. -/
theorem slice_volume_div_normal (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    sliceVolumeFactor G / Real.sqrt ((G⁻¹) 0 0) = volumeFactor G := by
  rw [sliceVolumeFactor, spatialGram_det_eq hd,
    Real.sqrt_mul (neg_nonneg.mpr hd.le),
    mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (inverse_time_pos hd hsp)).ne']
  rfl

/-- The induced Gram pairing is exactly the negative full-metric pairing of spatial tangents. -/
theorem spatialGram_pairing (G : Mat4) (z w : Fin 3 → ℝ) :
    -(G.toBilin' (sliceEmbed z) (sliceEmbed w)) = (spatialGram G).toBilin' z w := by
  simp only [Matrix.toBilin'_apply, sliceEmbed, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    spatialGram, Matrix.neg_apply, Matrix.submatrix_apply, mul_neg,
    neg_mul, Finset.sum_neg_distrib]

/-- The coordinate slice inclusion preserves nonzero vectors. -/
theorem sliceEmbed_ne_zero {z : Fin 3 → ℝ} (hz : z ≠ 0) : sliceEmbed z ≠ 0 := by
  intro h
  apply hz
  funext i
  exact congrFun h i.succ

/-- Every nonzero actual spatial tangent has strictly negative full-metric square. -/
theorem slice_square_neg (hsp : (spatialGram G).PosDef)
    {z : Fin 3 → ℝ} (hz : z ≠ 0) : G.toBilin' (sliceEmbed z) (sliceEmbed z) < 0 := by
  have hp : 0 < (spatialGram G).toBilin' z z := by
    simpa only [Matrix.toBilin'_apply', star_trivial] using hsp.dotProduct_mulVec_pos hz
  rw [← spatialGram_pairing] at hp
  linarith

/-- A tangent with zero temporal component is its actual spatial-coordinate inclusion. -/
theorem eq_sliceEmbed_tail {v : Covector} (hv : v 0 = 0) :
    v = sliceEmbed (Fin.tail v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · rfl

/-- Every nonzero vector tangent to the coordinate slice has strictly negative metric square. -/
theorem tangent_square_neg (hsp : (spatialGram G).PosDef)
    {v : Covector} (hv : v 0 = 0) (hvne : v ≠ 0) : G.toBilin' v v < 0 := by
  have ht : Fin.tail v ≠ 0 := by
    intro hz
    apply hvne
    rw [eq_sliceEmbed_tail hv, hz]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [eq_sliceEmbed_tail hv]
  exact slice_square_neg hsp ht

/-- The actual metric bilinear form is nondegenerate on the negative-determinant domain. -/
theorem metric_nondegenerate (hd : G.det < 0) : G.toBilin'.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' G hd.ne

/-- Lowering the raised normal recovers exactly the normalized time covector. -/
theorem lower_normal (hu : IsUnit G.det) :
    G.mulVec (normalVector G) = normalCovector G := by
  rw [normalVector, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hu,
    Matrix.one_mulVec]

/-- Pairing against the raised normal is the actual normalized temporal covector evaluation. -/
theorem normal_lowering (hu : IsUnit G.det) (u : Covector) :
    G.toBilin' u (normalVector G) = u 0 / Real.sqrt ((G⁻¹) 0 0) := by
  rw [Matrix.toBilin'_apply', lower_normal hu, normalCovector, dotProduct_single]
  rfl

/-- Every raised normal component retains its full inverse-metric shift coefficient. -/
theorem normalVector_apply (G : Mat4) (i : Fin 4) :
    normalVector G i = (G⁻¹) i 0 / Real.sqrt ((G⁻¹) 0 0) := by
  rw [normalVector, Matrix.mulVec, normalCovector, dotProduct_single]
  rfl

/-- The raised normal has the positive square root as its temporal component. -/
theorem normal_time (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    normalVector G 0 = Real.sqrt ((G⁻¹) 0 0) := by
  rw [normalVector_apply]
  apply (div_eq_iff (Real.sqrt_pos.mpr (inverse_time_pos hd hsp)).ne').mpr
  simpa only [pow_two] using (Real.sq_sqrt (inverse_time_pos hd hsp).le).symm

/-- The temporal component of the raised slice normal is strictly positive. -/
theorem normal_time_pos (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    0 < normalVector G 0 := by
  rw [normal_time hd hsp]
  exact Real.sqrt_pos.mpr (inverse_time_pos hd hsp)

/-- The actual raised normal has unit positive metric square. -/
theorem normal_unit (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    G.toBilin' (normalVector G) (normalVector G) = 1 := by
  rw [normal_lowering (isUnit_iff_ne_zero.mpr hd.ne), normal_time hd hsp,
    div_self (Real.sqrt_pos.mpr (inverse_time_pos hd hsp)).ne']

/-- The normalized covector has unit square for the inverse metric. -/
theorem covector_unit (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    (G⁻¹).toBilin' (normalCovector G) (normalCovector G) = 1 := by
  rw [Matrix.toBilin'_apply']
  change normalCovector G ⬝ᵥ normalVector G = 1
  rw [normalCovector, single_dotProduct, normal_time hd hsp,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (inverse_time_pos hd hsp)).ne']

/-- Every actual coordinate-slice tangent is orthogonal to the raised normal. -/
theorem normal_orthogonal (hu : IsUnit G.det) {v : Covector} (hv : v 0 = 0) :
    G.toBilin' v (normalVector G) = 0 := by
  rw [normal_lowering hu, hv, zero_div]

/-- Symmetry gives orthogonality in the opposite bilinear slot as well. -/
theorem normal_orthogonal_left (hu : IsUnit G.det) (hs : G.IsSymm)
    {v : Covector} (hv : v 0 = 0) : G.toBilin' (normalVector G) v = 0 := by
  rw [(Matrix.isSymm_toBilin'_iff_isSymm.mpr hs).eq, normal_orthogonal hu hv]

/-- The normalized time functional uniquely determines its metric-dual normal. -/
theorem normal_unique (hu : IsUnit G.det) {v : Covector}
    (hv : ∀ u, G.toBilin' u v = u 0 / Real.sqrt ((G⁻¹) 0 0)) :
    v = normalVector G := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr (G.isUnit_iff_isUnit_det.mpr hu)
  ext i
  have he := (hv (Pi.single i 1)).trans (normal_lowering hu (Pi.single i 1)).symm
  simpa only [Matrix.toBilin'_apply', single_one_dotProduct] using he

/-- The actual normal covector-current pairing is the normalized temporal current component. -/
theorem normal_pairing (G : Mat4) (J : Covector) :
    normalCovector G ⬝ᵥ J = J 0 / Real.sqrt ((G⁻¹) 0 0) := by
  rw [normalCovector, single_dotProduct]
  simp only [div_eq_mul_inv, mul_comm]

/-- The geometric slice flux times the induced Gram volume is exactly the densitized coordinate current. -/
theorem flux_density_eq (c : ℝ) (G : Mat4) (J : Covector)
    (hd : G.det < 0) (hsp : (spatialGram G).PosDef) :
    ((normalCovector G ⬝ᵥ J) / c) * sliceVolumeFactor G =
      volumeFactor G * J 0 / c := by
  rw [normal_pairing]
  calc
    _ = (sliceVolumeFactor G / Real.sqrt ((G⁻¹) 0 0)) * J 0 / c := by ring
    _ = _ := by rw [slice_volume_div_normal hd hsp]

end FoliationQM.SpacelikeSliceGeometry
