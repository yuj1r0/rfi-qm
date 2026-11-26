module
public import FoliationQM.LorentzMatrixGroup

/-!
# Intrinsic future-cone orientation of independent Lorentz matrices

Source: the proper future Lorentz-frame interpretation of v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. Every real matrix considered
here is specified by the independent metric equation in signature (+---),
without a spin representative or a supplied frame expansion.

An explicit three-coordinate Cauchy--Schwarz inequality proves positivity
of the actual Minkowski pairing on future timelike vectors. The metric
row and column identities then give time normalization and show that
actual future-cone preservation is equivalent to a positive time-time
entry, and equivalently to that entry being at least one. The reverse
cone implication is derived from the actual action on the negative vector,
not supplied as an additional orientation premise. Spatial length uses
coordinate squares throughout, without a function-space norm convention.

These are intrinsic Lorentz-cone criteria. Existence of spin lifts,
classification of the full representation image, and a spin covering
remain separate results.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzFutureCone

private theorem spatial_cauchy (u v : Covector) :
    (u 1*v 1+u 2*v 2+u 3*v 3)^2 ≤
      (u 1^2+u 2^2+u 3^2)*(v 1^2+v 2^2+v 3^2) := by
  nlinarith only [sq_nonneg (u 1*v 2-u 2*v 1),
    sq_nonneg (u 1*v 3-u 3*v 1), sq_nonneg (u 2*v 3-u 3*v 2)]

/-- The explicit Minkowski pairing of two future timelike vectors is positive. -/
theorem minkowski_pos_of_future {u v : Covector}
    (hu0 : 0 < u 0) (hu : 0 < minkowski u u)
    (hv0 : 0 < v 0) (hv : 0 < minkowski v v) :
    0 < minkowski u v := by
  have hus : u 1^2+u 2^2+u 3^2 < u 0^2 := by
    dsimp [minkowski] at hu
    nlinarith only [hu]
  have hvs : v 1^2+v 2^2+v 3^2 < v 0^2 := by
    dsimp [minkowski] at hv
    nlinarith only [hv]
  have hvn : 0 ≤ v 1^2+v 2^2+v 3^2 := by positivity
  have hmul : (u 1^2+u 2^2+u 3^2)*(v 1^2+v 2^2+v 3^2) <
      (u 0*v 0)^2 := by
    calc
      _ ≤ u 0^2 * (v 1^2+v 2^2+v 3^2) :=
        mul_le_mul_of_nonneg_right hus.le hvn
      _ < u 0^2 * v 0^2 := mul_lt_mul_of_pos_left hvs (sq_pos_of_pos hu0)
      _ = _ := by ring
  have hd := lt_of_le_of_lt (spatial_cauchy u v) hmul
  have hlt := (abs_lt_of_sq_lt_sq' hd (mul_pos hu0 hv0).le).2
  dsimp [minkowski]
  linarith only [hlt]

/-- A timelike vector has a nonzero temporal coordinate. -/
theorem time_ne_zero_of_timelike {v : Covector} (hv : 0 < minkowski v v) :
    v 0 ≠ 0 := by
  intro h
  dsimp [minkowski] at hv
  rw [h] at hv
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

/-- A future unit timelike vector has temporal coordinate at least one. -/
theorem time_ge_one_of_normalized {v : Covector}
    (hv : minkowski v v = 1) (hv0 : 0 < v 0) : 1 ≤ v 0 := by
  dsimp [minkowski] at hv
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

open LorentzMatrixGroup Matrix

/-- The temporal row of an independently metric-preserving matrix has unit timelike Minkowski norm. -/
theorem time_row_normalized (M : Mat4) (hm : M.transpose * eta * M = eta) :
    minkowski (M 0) (M 0) = 1 := by
  have he := congrArg (fun N : Mat4 => N 0 0) (metric_rows_of_metric M hm)
  simpa [Matrix.mul_apply, Matrix.transpose_apply, eta, RealLorentzFrame.sign,
    Fin.sum_univ_succ, minkowski, sub_eq_add_neg, add_assoc] using he

/-- The temporal column of an independently metric-preserving matrix has unit timelike Minkowski norm. -/
theorem time_column_normalized (M : Mat4) (hm : M.transpose * eta * M = eta) :
    minkowski (fun i => M i 0) (fun i => M i 0) = 1 := by
  have he := congrArg (fun N : Mat4 => N 0 0) hm
  simpa [Matrix.mul_apply, Matrix.transpose_apply, eta, RealLorentzFrame.sign,
    Fin.sum_univ_succ, minkowski, sub_eq_add_neg, add_assoc] using he

/-- An independently metric-preserving real matrix has temporal entry of squared magnitude at least one. -/
theorem time_sq_ge_one (M : Mat4) (hm : M.transpose * eta * M = eta) :
    1 ≤ M 0 0 ^ 2 := by
  have he := time_row_normalized M hm
  dsimp [minkowski] at he
  nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 0 2), sq_nonneg (M 0 3)]

/-- Positive temporal orientation of an independent Lorentz matrix is equivalent to a temporal entry at least one. -/
theorem time_pos_iff_ge_one (M : Mat4) (hm : M.transpose * eta * M = eta) :
    0 < M 0 0 ↔ 1 ≤ M 0 0 := by
  constructor
  · exact time_ge_one_of_normalized (time_row_normalized M hm)
  · exact lt_of_lt_of_le zero_lt_one

private theorem time_image_pos (M : Mat4) (hm : M.transpose * eta * M = eta)
    (h00 : 0 < M 0 0) {v : Covector} (hv : futureCone v) : 0 < (M *ᵥ v) 0 := by
  let w : Covector := ![M 0 0, -M 0 1, -M 0 2, -M 0 3]
  have hw : minkowski w w = 1 := by
    have he := time_row_normalized M hm
    simpa [w, minkowski] using he
  have hp := minkowski_pos_of_future (u:=w) (v:=v) h00 (by rw [hw]; norm_num) hv.1 hv.2
  simpa [w, minkowski, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using hp

/-- A positive temporal entry makes an independently metric-preserving matrix carry the actual future timelike cone into itself. -/
theorem futureCone_map_of_time_pos (M : Mat4) (hm : M.transpose * eta * M = eta)
    (h00 : 0 < M 0 0) {v : Covector} (hv : futureCone v) : futureCone (M *ᵥ v) := by
  refine ⟨time_image_pos M hm h00 hv, ?_⟩
  rw [minkowski_mulVec_of_metric M hm]
  exact hv.2

/-- Positive temporal orientation gives both directions of the actual future-cone equivalence; the reverse direction follows from timelikeness and the image of the negative vector. -/
theorem futureCone_map_iff_of_time_pos (M : Mat4) (hm : M.transpose * eta * M = eta)
    (h00 : 0 < M 0 0) (v : Covector) : futureCone (M *ᵥ v) ↔ futureCone v := by
  constructor
  · intro hv
    have hq : 0 < minkowski v v := by
      rw [← minkowski_mulVec_of_metric M hm v v]
      exact hv.2
    refine ⟨?_, hq⟩
    by_contra hn
    have hvneg : v 0 < 0 := lt_of_le_of_ne (le_of_not_gt hn) (time_ne_zero_of_timelike hq)
    have hneg : futureCone (-v) := by
      refine ⟨neg_pos.mpr hvneg, ?_⟩
      simpa [minkowski] using hq
    have himage := (futureCone_map_of_time_pos M hm h00 hneg).1
    rw [Matrix.mulVec_neg] at himage
    change 0 < -(M *ᵥ v) 0 at himage
    exact (not_lt_of_ge hv.1.le) (neg_pos.mp himage)
  · exact futureCone_map_of_time_pos M hm h00

/-- Preservation of the independently defined future timelike cone is exactly positive time orientation for an independently metric-preserving real matrix. -/
theorem preserves_futureCone_iff_time_pos (M : Mat4) (hm : M.transpose * eta * M = eta) :
    preservesFutureCone M ↔ 0 < M 0 0 := by
  constructor
  · intro h
    have he : futureCone (![1,0,0,0] : Covector) := by norm_num [futureCone, minkowski]
    have hp := ((h (![1,0,0,0] : Covector)).mpr he).1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hp
  · intro h
    exact futureCone_map_iff_of_time_pos M hm h

/-- The same intrinsic future-cone criterion is the closed temporal inequality at least one, derived from Lorentz normalization. -/
theorem preserves_futureCone_iff_time_ge_one (M : Mat4) (hm : M.transpose * eta * M = eta) :
    preservesFutureCone M ↔ 1 ≤ M 0 0 :=
  (preserves_futureCone_iff_time_pos M hm).trans (time_pos_iff_ge_one M hm)

end FoliationQM.LorentzFutureCone
