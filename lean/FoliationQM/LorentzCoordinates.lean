module

public import FoliationQM.DressedVelocity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Explicit laboratory Lorentz coordinates and the simultaneity form

Sources: v13 `lem:simultaneity` and the kinematic input of `prop:debroglie`.
Spatial length uses the explicit positive Euclidean coordinate quadratic form,
not the norm of a function space. Time is represented by x0 = c t, and the
Minkowski contraction has signature (+---). All results are pointwise; a
Hamilton--Jacobi section and a global time function are separate constructions.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LorentzCoordinates

/-- The three real laboratory spatial coordinates. -/
abbrev Spatial := Fin 3 → ℝ

/-- The explicit positive Euclidean spatial bilinear form. -/
def spatialDot (v w : Spatial) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- Squared Euclidean speed, with no use of the function-space norm. -/
def speedSq (v : Spatial) : ℝ := spatialDot v v

/-- Euclidean speed is the positive square root of the coordinate square sum. -/
def euclideanSpeed (v : Spatial) : ℝ := Real.sqrt (speedSq v)

/-- Assemble one time component and three spatial components. -/
def assemble (t : ℝ) (v : Spatial) : Covector := ![t, v 0, v 1, v 2]

/-- Lower or raise a Minkowski index in the fixed diagonal convention. -/
def lower (u : Covector) : Covector := ![u 0, -u 1, -u 2, -u 3]

/-- Ordinary contraction of a lowered covector with an upper vector. -/
def pairing (p u : Covector) : ℝ :=
  p 0 * u 0 + p 1 * u 1 + p 2 * u 2 + p 3 * u 3

/-- The actual Lorentz factor on its subluminal domain. -/
def gamma (c : ℝ) (v : Spatial) : ℝ := (Real.sqrt (1 - speedSq v / c ^ 2))⁻¹

/-- The upper four-velocity of the laboratory boost. -/
def fourVelocity (c : ℝ) (v : Spatial) : Covector :=
  assemble (gamma c v * c) (fun i => gamma c v * v i)

/-- A laboratory tangent displacement uses x0 = c t. -/
def displacement (c dt : ℝ) (dx : Spatial) : Covector := assemble (c * dt) dx

/-- The physical proper-time synchronization form evaluated on a tangent. -/
def properTime (c : ℝ) (v : Spatial) (dx : Covector) : ℝ :=
  minkowski (fourVelocity c v) dx / c ^ 2

/-- The Euclidean spatial form is symmetric. -/
theorem spatialDot_comm (v w : Spatial) : spatialDot v w = spatialDot w v := by
  unfold spatialDot
  ring

/-- Scalar multiplication in the second spatial argument factors out. -/
theorem spatialDot_smul_right (v w : Spatial) (a : ℝ) :
    spatialDot v (a • w) = a * spatialDot v w := by
  simp only [spatialDot, Pi.smul_apply, smul_eq_mul]
  ring

/-- The explicit spatial squared speed is the sum of three coordinate squares. -/
theorem speedSq_eq_sum (v : Spatial) : speedSq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp only [speedSq, spatialDot, pow_two]

/-- Squared Euclidean speed is nonnegative. -/
theorem speedSq_nonneg (v : Spatial) : 0 ≤ speedSq v := by
  rw [speedSq_eq_sum]
  positivity

/-- Zero Euclidean speed characterizes the zero spatial vector. -/
theorem speedSq_eq_zero_iff (v : Spatial) : speedSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [speedSq_eq_sum] at h
    have h0 : v 0 ^ 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
    have h2 : v 2 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hv0 := sq_eq_zero_iff.mp h0
    have hv1 := sq_eq_zero_iff.mp h1
    have hv2 := sq_eq_zero_iff.mp h2
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2]
  · rintro rfl
    simp [speedSq, spatialDot]

/-- The explicit Euclidean speed squares to the coordinate square sum. -/
theorem euclideanSpeed_sq (v : Spatial) : euclideanSpeed v ^ 2 = speedSq v :=
  Real.sq_sqrt (speedSq_nonneg v)

/-- The squared-speed subluminal condition is exactly the Euclidean-speed condition. -/
theorem euclideanSpeed_lt_iff {c : ℝ} (hc : 0 < c) (v : Spatial) :
    euclideanSpeed v < c ↔ speedSq v < c ^ 2 :=
  Real.sqrt_lt' hc

/-- Lowering and ordinary contraction reproduce the explicit Minkowski form. -/
theorem pairing_lower (u w : Covector) : pairing (lower u) w = minkowski u w := by
  change u 0 * w 0 + (-u 1) * w 1 + (-u 2) * w 2 + (-u 3) * w 3 =
    u 0 * w 0 - u 1 * w 1 - u 2 * w 2 - u 3 * w 3
  ring

/-- Applying the fixed index-lowering operation twice is the identity. -/
theorem lower_lower (u : Covector) : lower (lower u) = u := by
  funext i
  fin_cases i <;> simp [lower]

/-- The Minkowski contraction splits into time product minus Euclidean spatial dot product. -/
theorem minkowski_assemble (t s : ℝ) (v w : Spatial) :
    minkowski (assemble t v) (assemble s w) = t * s - spatialDot v w := by
  change t * s - v 0 * w 0 - v 1 * w 1 - v 2 * w 2 =
    t * s - (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)
  ring

/-- Subluminality makes the square-root argument of the actual Lorentz factor positive. -/
theorem one_sub_speed_ratio_pos {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : 0 < 1 - speedSq v / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  exact sub_pos.mpr ((div_lt_one hc2).mpr hv)

/-- The actual Lorentz factor is strictly positive on the physical subluminal domain. -/
theorem gamma_pos {c : ℝ} {v : Spatial} (hc : 0 < c) (hv : speedSq v < c ^ 2) :
    0 < gamma c v :=
  inv_pos.mpr (Real.sqrt_pos.mpr (one_sub_speed_ratio_pos hc hv))

/-- Squaring the actual Lorentz factor gives the reciprocal source expression. -/
theorem gamma_sq {c : ℝ} {v : Spatial} (hc : 0 < c) (hv : speedSq v < c ^ 2) :
    gamma c v ^ 2 = (1 - speedSq v / c ^ 2)⁻¹ := by
  rw [gamma, inv_pow, Real.sq_sqrt (one_sub_speed_ratio_pos hc hv).le]

/-- The squared Lorentz factor cancels the positive subluminal factor. -/
theorem gamma_sq_mul {c : ℝ} {v : Spatial} (hc : 0 < c) (hv : speedSq v < c ^ 2) :
    gamma c v ^ 2 * (1 - speedSq v / c ^ 2) = 1 := by
  rw [gamma_sq hc hv]
  exact inv_mul_cancel₀ (one_sub_speed_ratio_pos hc hv).ne'

/-- The equivalent dimensional Lorentz normalization identity. -/
theorem gamma_sq_mul_difference {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : gamma c v ^ 2 * (c ^ 2 - speedSq v) = c ^ 2 := by
  have h := gamma_sq_mul hc hv
  have hc0 : c ≠ 0 := hc.ne'
  field_simp at h
  nlinarith

/-- The physical Lorentz factor is at least one. -/
theorem one_le_gamma {c : ℝ} {v : Spatial} (hc : 0 < c) (hv : speedSq v < c ^ 2) :
    1 ≤ gamma c v := by
  have h := gamma_sq_mul hc hv
  have hg := gamma_pos hc hv
  have hn : 0 ≤ speedSq v / c ^ 2 := div_nonneg (speedSq_nonneg v) (sq_nonneg c)
  nlinarith [mul_nonneg (sq_nonneg (gamma c v)) hn]

/-- A rest laboratory velocity has Lorentz factor one. -/
theorem gamma_zero (c : ℝ) : gamma c 0 = 1 := by
  simp [gamma, speedSq, spatialDot]

/-- The actual boosted four-velocity has the source Minkowski normalization. -/
theorem fourVelocity_normalized {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : minkowski (fourVelocity c v) (fourVelocity c v) = c ^ 2 := by
  have h := gamma_sq_mul_difference hc hv
  simp only [fourVelocity, minkowski_assemble, spatialDot, speedSq] at h ⊢
  nlinarith

/-- The time component of the physical boosted four-velocity is future directed. -/
theorem fourVelocity_future {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : 0 < fourVelocity c v 0 := by
  exact mul_pos (gamma_pos hc hv) hc

/-- The proper-time form evaluates to one on the normalized physical four-velocity. -/
theorem properTime_fourVelocity {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : properTime c v (fourVelocity c v) = 1 := by
  rw [properTime, fourVelocity_normalized hc hv]
  exact div_self (pow_ne_zero 2 hc.ne')

/-- The actual Minkowski contraction of velocity and laboratory displacement. -/
theorem velocity_displacement_contraction (c dt : ℝ) (v dx : Spatial) :
    minkowski (fourVelocity c v) (displacement c dt dx) =
      gamma c v * (c ^ 2 * dt - spatialDot v dx) := by
  simp only [fourVelocity, displacement, minkowski_assemble, spatialDot]
  ring

/-- The physical proper-time form has the source laboratory expression. -/
theorem properTime_displacement {c : ℝ} (hc : 0 < c) (v : Spatial) (dt : ℝ) (dx : Spatial) :
    properTime c v (displacement c dt dx) =
      gamma c v * (dt - spatialDot v dx / c ^ 2) := by
  rw [properTime, velocity_displacement_contraction]
  field_simp

/-- The rest-velocity specialization recovers laboratory time for every spatial displacement. -/
theorem properTime_rest {c : ℝ} (hc : 0 < c) (dt : ℝ) (dx : Spatial) :
    properTime c 0 (displacement c dt dx) = dt := by
  rw [properTime_displacement hc, gamma_zero]
  simp [spatialDot]

/-- Along a particle's tangent worldline, proper time is laboratory time divided by gamma. -/
theorem properTime_worldline {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) (dt : ℝ) :
    properTime c v (displacement c dt (dt • v)) = dt / gamma c v := by
  rw [properTime_displacement hc, spatialDot_smul_right]
  have h := gamma_sq_mul hc hv
  have hg := (gamma_pos hc hv).ne'
  rw [eq_div_iff hg]
  change gamma c v * (dt - dt * speedSq v / c ^ 2) * gamma c v = dt
  calc
    _ = dt * (gamma c v ^ 2 * (1 - speedSq v / c ^ 2)) := by ring
    _ = dt := by rw [h, mul_one]

/-- Positive laboratory time along the forward worldline gives positive proper time. -/
theorem properTime_worldline_pos {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) {dt : ℝ} (hdt : 0 < dt) :
    0 < properTime c v (displacement c dt (dt • v)) := by
  rw [properTime_worldline hc hv]
  exact div_pos hdt (gamma_pos hc hv)

/-- The equal-time restriction is precisely the source simultaneity shift. -/
theorem properTime_equal_time {c : ℝ} (hc : 0 < c) (v dx : Spatial) :
    properTime c v (displacement c 0 dx) = -gamma c v * spatialDot v dx / c ^ 2 := by
  rw [properTime_displacement hc]
  ring

/-- A subluminal equal-time shift vanishes exactly on spatial directions orthogonal to velocity. -/
theorem properTime_equal_time_eq_zero_iff {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) (dx : Spatial) :
    properTime c v (displacement c 0 dx) = 0 ↔ spatialDot v dx = 0 := by
  rw [properTime_equal_time hc]
  simp [(gamma_pos hc hv).ne', hc.ne']

/-- The source nonzero-shift qualification is exact, not merely a sufficient direction. -/
theorem properTime_equal_time_ne_zero_iff {c : ℝ} {v : Spatial} (hc : 0 < c)
    (hv : speedSq v < c ^ 2) (dx : Spatial) :
    properTime c v (displacement c 0 dx) ≠ 0 ↔ spatialDot v dx ≠ 0 :=
  not_congr (properTime_equal_time_eq_zero_iff hc hv dx)

/-- Given the actual eikonal action covector minus mass times lowered velocity,
its phase-clock form equals the proper-time form pointwise. -/
theorem clock_from_lowered_velocity {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (v : Spatial) (dx : Covector) :
    -pairing (fun i => -m * lower (fourVelocity c v) i) dx / (m * c ^ 2) =
      properTime c v dx := by
  have he : pairing (fun i => -m * lower (fourVelocity c v) i) dx =
      -m * pairing (lower (fourVelocity c v)) dx := by
    unfold pairing
    ring
  rw [he, pairing_lower, properTime]
  field_simp

end FoliationQM.LorentzCoordinates
