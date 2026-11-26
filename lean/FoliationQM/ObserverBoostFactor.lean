module

public import FoliationQM.LorentzCoordinates
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Laboratory drift and the observer Lorentz factor

For v13 `eq:jacobian_density`, a future four-velocity U of squared
Minkowski length c² has laboratory velocity c Uⁱ/U⁰. The boost factor
of this subluminal drift is U⁰/c. More generally the contraction with
any future unit normal gives a factor at least one.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverBoostFactor

open LorentzCoordinates

/-- The laboratory three-velocity extracted from the raised four-velocity in x⁰ = ct coordinates. -/
def drift (c : ℝ) (U : Covector) : Spatial := fun i => c * U i.succ / U 0

private theorem spatial_square {c : ℝ} {U : Covector} (hU : minkowski U U = c ^ 2) :
    speedSq (fun i : Fin 3 => U i.succ) = U 0 ^ 2 - c ^ 2 := by
  rw [← hU, speedSq_eq_sum]
  change U 1 ^ 2 + U 2 ^ 2 + U 3 ^ 2 = U 0 ^ 2 - minkowski U U
  unfold minkowski
  ring

private theorem drift_radicand {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) :
    1 - speedSq (drift c U) / c ^ 2 = (c / U 0) ^ 2 := by
  have he : speedSq (drift c U) = (c/U 0)^2 * speedSq (fun i : Fin 3 => U i.succ) := by
    simp only [speedSq_eq_sum, drift]
    ring
  rw [he, spatial_square hU]
  field_simp [hc.ne', hf.ne']
  ring

/-- The actual extracted laboratory drift is strictly subluminal for a future normalized velocity. -/
theorem speedSq_drift_lt {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) : speedSq (drift c U) < c ^ 2 := by
  have h := drift_radicand hc hU hf
  apply (div_lt_one (sq_pos_of_pos hc)).mp
  linarith [sq_pos_of_pos (div_pos hc hf)]

/-- The Lorentz factor of the laboratory velocity is the time component of the raised velocity divided by c. -/
theorem gamma_drift {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) : gamma c (drift c U) = U 0 / c := by
  rw [gamma, drift_radicand hc hU hf, Real.sqrt_sq (div_nonneg hc.le hf.le), inv_div]

/-- The coordinate observer sees a boost factor at least one. -/
theorem gamma_ge_one {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) : 1 ≤ U 0 / c :=
  (one_le_gamma hc (speedSq_drift_lt hc hU hf)).trans_eq (gamma_drift hc hU hf)

/-- Reconstructing the standard laboratory four-velocity from the extracted drift gives the original raised vector. -/
theorem fourVelocity_drift {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) : fourVelocity c (drift c U) = U := by
  rw [fourVelocity, gamma_drift hc hU hf]
  ext i
  fin_cases i <;> simp [assemble, drift, hc.ne', hf.ne']

/-- The observer factor is one precisely when all three raised spatial components vanish. -/
theorem gamma_eq_one_iff {c : ℝ} {U : Covector} (hc : 0 < c)
    (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) : U 0 / c = 1 ↔ ∀ i : Fin 3, U i.succ = 0 := by
  constructor
  · intro h
    have ht := (div_eq_one_iff_eq hc.ne').mp h
    have hs := spatial_square hU
    rw [ht, sub_self, speedSq_eq_zero_iff] at hs
    exact fun i => congrFun hs i
  · intro h
    have he : drift c U = 0 := funext (fun i => by simp [drift, h i])
    rw [← gamma_drift hc hU hf, he, gamma_zero]

/-- For any future unit observer normal, the normalized physical contraction is at least one. -/
theorem normal_gamma_ge_one {c : ℝ} {n U : Covector} (hc : 0 < c)
    (hn : minkowski n n = 1) (hnf : 0 < n 0) (hU : minkowski U U = c ^ 2) (hf : 0 < U 0) :
    1 ≤ minkowski n U / c := by
  let a : Spatial := fun i => n i.succ
  let b : Spatial := fun i => U i.succ
  have hn' : minkowski n n = (1 : ℝ)^2 := by simpa using hn
  have hna : 1 ≤ n 0 := by simpa using gamma_ge_one one_pos hn' hnf
  have hub : c ≤ U 0 := (one_le_div hc).mp (gamma_ge_one hc hU hf)
  have hnon : 0 ≤ n 0*U 0 - c := by nlinarith [mul_nonneg (sub_nonneg.mpr hna) hf.le]
  have hcs : spatialDot a b ^ 2 ≤ speedSq a * speedSq b := by
    simpa [spatialDot, speedSq_eq_sum, Fin.sum_univ_three] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have ha : speedSq a = n 0 ^ 2 - 1 := by simpa [a] using spatial_square hn'
  have hb : speedSq b = U 0 ^ 2 - c ^ 2 := spatial_square hU
  rw [ha, hb] at hcs
  have hs : spatialDot a b ^ 2 ≤ (n 0 * U 0 - c)^2 := by
    nlinarith only [hcs, sq_nonneg (U 0 - c*n 0)]
  have hab : |spatialDot a b| ≤ n 0 * U 0 - c :=
    (sq_le_sq₀ (abs_nonneg _) hnon).mp (by simpa only [sq_abs] using hs)
  have he : minkowski n U = n 0 * U 0 - spatialDot a b := by
    change minkowski n U = _ - (n 1*U 1 + n 2*U 2 + n 3*U 3)
    unfold minkowski
    ring
  rw [one_le_div hc, he]
  linarith [le_abs_self (spatialDot a b)]

end FoliationQM.ObserverBoostFactor
