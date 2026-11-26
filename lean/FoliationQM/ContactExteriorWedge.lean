module

public import FoliationQM.ContactExteriorBasics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The actual exterior contact-volume calculation

Source: v13 `thm:contact_period`. The coordinates are ordered
x0, x1, p1, x2, p2, x3, p3, with lower momentum components and alpha = -p_mu dx^mu.
Every product below is multiplication in the genuine exterior algebra of chart
covectors. The cube is proved using alternating degree-one generators, then the
coefficient is calculated by alternating multilinearity. The volume element is
nonzero by the determinant evaluation in `ContactExteriorBasics`.

The unrestricted coefficient identity is algebraic, using Lean's total division.
The on-shell and nonvanishing results explicitly impose the nonzero or positive
p0 hypotheses needed for the mass-shell chart. This module establishes the
exterior-algebra calculation; the actual differential-form pullback is connected
in the separate mass-shell differential-form bridge.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ContactExteriorWedge

open ExteriorAlgebra ContactExteriorBasics

private theorem decomposable_sq_zero (a b : Covectors) : ((ι ℝ a : Forms) * ι ℝ b) ^ 2 = 0 := by
  have hab : (ι ℝ b : Forms) * ι ℝ a = -(ι ℝ a * ι ℝ b) :=
    eq_neg_of_add_eq_zero_left (ι_add_mul_swap b a)
  calc
    _ = ι ℝ a * (ι ℝ b * ι ℝ a) * ι ℝ b := by noncomm_ring
    _ = -((ι ℝ a * ι ℝ a) * (ι ℝ b * ι ℝ b)) := by rw [hab]; noncomm_ring
    _ = 0 := by rw [ι_sq_zero, zero_mul, neg_zero]

private theorem decomposable_commute (a b c d : Covectors) :
    Commute ((ι ℝ a : Forms) * ι ℝ b) ((ι ℝ c : Forms) * ι ℝ d) := by
  have h := ιMulti_mul_ιMulti_anticomm (R := ℝ) ![a, b] ![c, d]
  change _ * _ = _ * _
  have hu : (-1 : ℤˣ) ^ 4 = 1 := by decide
  simpa [ιMulti_succ_apply, hu] using h

private theorem cube_of_square_zero_commute (a b c : Forms)
    (ha : a ^ 2 = 0) (hb : b ^ 2 = 0) (hc : c ^ 2 = 0)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) :
    (a + b + c) ^ 3 = (6 : ℝ) • (a * b * c) := by
  have hba (x : Forms) : b * (a * x) = a * (b * x) := hab.symm.left_comm x
  have hca (x : Forms) : c * (a * x) = a * (c * x) := hac.symm.left_comm x
  have hcb (x : Forms) : c * (b * x) = b * (c * x) := hbc.symm.left_comm x
  have haa (x : Forms) : a * (a * x) = 0 := by rw [← mul_assoc, ← pow_two, ha, zero_mul]
  have hbb (x : Forms) : b * (b * x) = 0 := by rw [← mul_assoc, ← pow_two, hb, zero_mul]
  have hcc (x : Forms) : c * (c * x) = 0 := by rw [← mul_assoc, ← pow_two, hc, zero_mul]
  have haa0 : a * a = 0 := by simpa [pow_two] using ha
  have hbb0 : b * b = 0 := by simpa [pow_two] using hb
  have hcc0 : c * c = 0 := by simpa [pow_two] using hc
  have hab0 : b * a = a * b := hab.symm.eq
  have hac0 : c * a = a * c := hac.symm.eq
  have hbc0 : c * b = b * c := hbc.symm.eq
  norm_num [show (6 : ℝ) • (a * b * c) = (6 : ℕ) • (a * b * c) from by norm_cast]
  noncomm_ring [hba, hca, hcb, haa, hbb, hcc, haa0, hbb0, hcc0, hab0, hac0, hbc0]

private theorem alternating_shear (v : Fin 7 → Covectors) (i j : Fin 7) (hij : i ≠ j) (r : ℝ) :
    ιMulti ℝ 7 (Function.update v i (v i + r • v j)) = ιMulti ℝ 7 v := by
  rw [(ιMulti ℝ 7).map_update_add, (ιMulti ℝ 7).map_update_smul,
    (ιMulti ℝ 7).map_update_self _ hij, smul_zero, add_zero,
    Function.update_eq_self]

private def shiftedCovectors (q1 q2 q3 : ℝ) : Fin 7 → Covectors :=
  ![coordinate 0, coordinate 1 + q1 • coordinate 0, coordinate 2,
    coordinate 3 + q2 • coordinate 0, coordinate 4,
    coordinate 5 + q3 • coordinate 0, coordinate 6]

private theorem shifted_volume (q1 q2 q3 : ℝ) : ιMulti ℝ 7 (shiftedCovectors q1 q2 q3) = volume := by
  let v1 := Function.update coordinate 1 (coordinate 1 + q1 • coordinate 0)
  let v2 := Function.update v1 3 (coordinate 3 + q2 • coordinate 0)
  let v3 := Function.update v2 5 (coordinate 5 + q3 • coordinate 0)
  have h1 : ιMulti ℝ 7 v1 = ιMulti ℝ 7 coordinate := alternating_shear coordinate 1 0 (by decide) q1
  have h2 : ιMulti ℝ 7 v2 = ιMulti ℝ 7 v1 := by
    simpa [v2, v1] using alternating_shear v1 3 0 (by decide) q2
  have h3 : ιMulti ℝ 7 v3 = ιMulti ℝ 7 v2 := by
    simpa [v3, v2, v1] using alternating_shear v2 5 0 (by decide) q3
  have hv : shiftedCovectors q1 q2 q3 = v3 := by
    ext i x
    fin_cases i <;> simp [shiftedCovectors, v3, v2, v1]
  rw [hv, h3, h2, h1, ← volume_eq_ιMulti]

private theorem alternating_head_combination (u a b c d e f : Covectors) (k r1 r2 r3 : ℝ) :
    ιMulti ℝ 7 ![k • u + r1 • a + r2 • c + r3 • e, a, b, c, d, e, f] =
      k • ιMulti ℝ 7 ![u, a, b, c, d, e, f] := by
  have h1 : ιMulti ℝ 7 ![a, a, b, c, d, e, f] = 0 :=
    (ιMulti ℝ 7).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have h2 : ιMulti ℝ 7 ![c, a, b, c, d, e, f] = 0 :=
    (ιMulti ℝ 7).map_eq_zero_of_eq _ (i := 0) (j := 3) rfl (by decide)
  have h3 : ιMulti ℝ 7 ![e, a, b, c, d, e, f] = 0 :=
    (ιMulti ℝ 7).map_eq_zero_of_eq _ (i := 0) (j := 5) rfl (by decide)
  simp only [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul,
    h1, h2, h3, smul_zero, add_zero]

private def shiftedOne (p0 p1 : ℝ) : Covectors := coordinate 1 + (p1 / p0) • coordinate 0
private def shiftedTwo (p0 p2 : ℝ) : Covectors := coordinate 3 + (p2 / p0) • coordinate 0
private def shiftedThree (p0 p3 : ℝ) : Covectors := coordinate 5 + (p3 / p0) • coordinate 0

private def alphaCovector (p0 p1 p2 p3 : ℝ) : Covectors :=
  (-p0) • coordinate 0 + (-p1) • coordinate 1 +
    (-p2) • coordinate 3 + (-p3) • coordinate 5

private theorem alphaCovector_eq (p0 p1 p2 p3 : ℝ) : alphaCovector p0 p1 p2 p3 =
    (-p0 + (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) / p0) • coordinate 0 +
      (-p1) • shiftedOne p0 p1 + (-p2) • shiftedTwo p0 p2 + (-p3) • shiftedThree p0 p3 := by
  ext x
  simp [alphaCovector, shiftedOne, shiftedTwo, shiftedThree]
  ring

private theorem alpha_shifted_product (p0 p1 p2 p3 : ℝ) :
    ι ℝ (alphaCovector p0 p1 p2 p3) *
      ((ι ℝ (shiftedOne p0 p1) * e 2) * (ι ℝ (shiftedTwo p0 p2) * e 4) *
        (ι ℝ (shiftedThree p0 p3) * e 6)) =
      (-p0 + (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) / p0) • volume := by
  calc
    _ = ιMulti ℝ 7 ![alphaCovector p0 p1 p2 p3, shiftedOne p0 p1, coordinate 2,
        shiftedTwo p0 p2, coordinate 4, shiftedThree p0 p3, coordinate 6] := by
      simp [e, ιMulti_succ_apply, mul_assoc]
    _ = (-p0 + (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) / p0) •
        ιMulti ℝ 7 ![coordinate 0, shiftedOne p0 p1, coordinate 2,
          shiftedTwo p0 p2, coordinate 4, shiftedThree p0 p3, coordinate 6] := by
      rw [alphaCovector_eq]
      exact alternating_head_combination _ _ _ _ _ _ _ _ _ _ _
    _ = _ := by
      change _ • ιMulti ℝ 7 (shiftedCovectors (p1 / p0) (p2 / p0) (p3 / p0)) = _
      rw [shifted_volume]

/-- The Liouville one-form in the ordered mass-shell chart, embedded in its actual exterior algebra. -/
def alphaExterior (p0 p1 p2 p3 : ℝ) : Forms :=
  (-p0) • e 0 + (-p1) • e 1 + (-p2) • e 3 + (-p3) • e 5

/-- The actual exterior two-form with the coefficients of the pulled-back Liouville differential. -/
def omegaExterior (p0 p1 p2 p3 : ℝ) : Forms :=
  (p1 / p0) • (e 0 * e 2) + (p2 / p0) • (e 0 * e 4) +
    (p3 / p0) • (e 0 * e 6) + e 1 * e 2 + e 3 * e 4 + e 5 * e 6

private theorem alphaExterior_eq_generator (p0 p1 p2 p3 : ℝ) :
    alphaExterior p0 p1 p2 p3 = ι ℝ (alphaCovector p0 p1 p2 p3) := by
  simp [alphaExterior, alphaCovector, e]

private theorem omegaExterior_eq_shifted (p0 p1 p2 p3 : ℝ) :
    omegaExterior p0 p1 p2 p3 =
      (ι ℝ (shiftedOne p0 p1) * e 2) + (ι ℝ (shiftedTwo p0 p2) * e 4) +
        (ι ℝ (shiftedThree p0 p3) * e 6) := by
  simp only [omegaExterior, shiftedOne, shiftedTwo, shiftedThree, map_add, map_smul,
    add_mul, smul_mul_assoc]
  change _ = (e 1 * e 2 + (p1 / p0) • (e 0 * e 2)) +
    (e 3 * e 4 + (p2 / p0) • (e 0 * e 4)) +
    (e 5 * e 6 + (p3 / p0) • (e 0 * e 6))
  abel

/-- The genuine seventh-degree exterior product for v13 `thm:contact_period`, before imposing the mass shell. -/
theorem alpha_mul_omega_cube (p0 p1 p2 p3 : ℝ) :
    alphaExterior p0 p1 p2 p3 * omegaExterior p0 p1 p2 p3 ^ 3 =
      (-6 * (p0 - (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) / p0)) • volume := by
  have hcub := cube_of_square_zero_commute (ι ℝ (shiftedOne p0 p1) * e 2)
    (ι ℝ (shiftedTwo p0 p2) * e 4) (ι ℝ (shiftedThree p0 p3) * e 6)
    (decomposable_sq_zero _ _) (decomposable_sq_zero _ _) (decomposable_sq_zero _ _)
    (decomposable_commute _ _ _ _) (decomposable_commute _ _ _ _) (decomposable_commute _ _ _ _)
  rw [omegaExterior_eq_shifted, hcub,
    alphaExterior_eq_generator, mul_smul_comm, alpha_shifted_product, smul_smul]
  congr 1
  ring

/-- On a mass-shell chart with nonzero p₀, the actual contact-volume coefficient is -6 m²c²/p₀ (v13 `thm:contact_period`). -/
theorem alpha_mul_omega_cube_on_shell (p0 p1 p2 p3 m c : ℝ)
    (hp0 : p0 ≠ 0) (hshell : p0 ^ 2 - p1 ^ 2 - p2 ^ 2 - p3 ^ 2 = m ^ 2 * c ^ 2) :
    alphaExterior p0 p1 p2 p3 * omegaExterior p0 p1 p2 p3 ^ 3 =
      (-6 * m ^ 2 * c ^ 2 / p0) • volume := by
  rw [alpha_mul_omega_cube]
  congr 1
  field_simp
  nlinarith [hshell]

/-- With positive c and p₀, the actual exterior contact volume is nonzero exactly when the mass is nonzero. -/
theorem contact_volume_ne_zero_iff (p0 p1 p2 p3 m c : ℝ)
    (hp0 : 0 < p0) (hc : 0 < c)
    (hshell : p0 ^ 2 - p1 ^ 2 - p2 ^ 2 - p3 ^ 2 = m ^ 2 * c ^ 2) :
    alphaExterior p0 p1 p2 p3 * omegaExterior p0 p1 p2 p3 ^ 3 ≠ 0 ↔ m ≠ 0 := by
  rw [alpha_mul_omega_cube_on_shell _ _ _ _ _ _ (ne_of_gt hp0) hshell]
  simp [smul_eq_zero, volume_ne_zero, ne_of_gt hc, ne_of_gt hp0]

/-- The massless shell has zero actual exterior contact volume, as asserted in v13 `thm:contact_period`. -/
theorem massless_contact_volume_zero (p0 p1 p2 p3 : ℝ) (hp0 : p0 ≠ 0)
    (hshell : p0 ^ 2 - p1 ^ 2 - p2 ^ 2 - p3 ^ 2 = 0) :
    alphaExterior p0 p1 p2 p3 * omegaExterior p0 p1 p2 p3 ^ 3 = 0 := by
  have h := alpha_mul_omega_cube_on_shell p0 p1 p2 p3 0 1 hp0 (by simpa using hshell)
  simpa using h

end FoliationQM.ContactExteriorWedge
