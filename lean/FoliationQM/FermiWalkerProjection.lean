module
public import FoliationQM.RealLorentzFrame

/-!
# Actual Minkowski projection and tetrad-gradient algebra

Source: v13 `eq:mc_velocity_spin_identity` and the preceding velocity and
Fermi--Walker spin-gradient calculations. Both projection formulas act on
actual four-component real vectors using the explicit (+---) Minkowski
bilinear form. Their equivalence keeps the nonzero physical speed c as an
explicit hypothesis wherever c squared is cancelled.

For any orthonormal Lorentz tetrad, the displayed time and spin jets are
actual linear combinations of its vectors. Projection, perpendicularity,
mixed pairings, and squared norms are derived from that orthonormality.
No derivative or jet-norm identity is a premise. Identification of these
linear combinations with actual field derivatives is handled separately.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FermiWalkerProjection
open RealLorentzFrame

/-- The actual Minkowski projection perpendicular to a physical velocity of squared norm c squared. -/
def projection (c : ℝ) (u z : Covector) : Covector :=
  z - (minkowski u z / c^2) • u

/-- The actual Minkowski projection perpendicular to a unit timelike vector. -/
def normalizedProjection (v z : Covector) : Covector := z - minkowski v z • v

private theorem pair_add_left (x y z : Covector) :
    minkowski (x+y) z = minkowski x z + minkowski y z := by simp [minkowski]; ring

private theorem pair_add_right (x y z : Covector) :
    minkowski x (y+z) = minkowski x y + minkowski x z := by simp [minkowski]; ring

private theorem pair_sub_left (x y z : Covector) :
    minkowski (x-y) z = minkowski x z - minkowski y z := by simp [minkowski]; ring

private theorem pair_sub_right (x y z : Covector) :
    minkowski x (y-z) = minkowski x y - minkowski x z := by simp [minkowski]; ring

private theorem pair_smul_left (r : ℝ) (x y : Covector) :
    minkowski (r • x) y = r * minkowski x y := by simp [minkowski]; ring

private theorem pair_smul_right (r : ℝ) (x y : Covector) :
    minkowski x (r • y) = r * minkowski x y := by simp [minkowski]; ring

private theorem pair_comm (x y : Covector) : minkowski x y = minkowski y x := by
  unfold minkowski
  ring

/-- The physical c-scaled formula is exactly the normalized projection whenever c is nonzero. -/
theorem projection_scaled (c : ℝ) (hc : c ≠ 0) (v z : Covector) :
    projection c (c • v) z = normalizedProjection v z := by
  unfold projection normalizedProjection
  rw [pair_smul_left, smul_smul]
  congr 2
  field_simp

/-- A normalized Minkowski projection is perpendicular to its unit timelike vector. -/
theorem normalizedProjection_perp (v z : Covector) (hv : minkowski v v = 1) :
    minkowski v (normalizedProjection v z) = 0 := by
  simp only [normalizedProjection, pair_sub_right, pair_smul_right, hv, mul_one, sub_self]

/-- The physical projection is perpendicular to a velocity with squared Minkowski norm c squared. -/
theorem projection_perp (c : ℝ) (hc : c ≠ 0) (u z : Covector)
    (hu : minkowski u u = c^2) : minkowski u (projection c u z) = 0 := by
  simp only [projection, pair_sub_right, pair_smul_right, hu]
  field_simp
  ring

/-- Projecting twice onto the unit-time orthogonal space gives the same actual vector. -/
theorem normalizedProjection_idempotent (v z : Covector) (hv : minkowski v v = 1) :
    normalizedProjection v (normalizedProjection v z) = normalizedProjection v z := by
  rw [normalizedProjection, normalizedProjection_perp v z hv, zero_smul, sub_zero]

/-- The actual projected mixed pairing removes the product of the two time components. -/
theorem normalizedProjection_mixed (v z w : Covector) (hv : minkowski v v = 1) :
    minkowski (normalizedProjection v z) (normalizedProjection v w) =
      minkowski z w - minkowski v z * minkowski v w := by
  simp only [normalizedProjection, pair_sub_left, pair_sub_right,
    pair_smul_left, pair_smul_right, hv, pair_comm z v]
  ring

/-- The actual projected squared norm removes the square of the time component. -/
theorem normalizedProjection_squared (v z : Covector) (hv : minkowski v v = 1) :
    minkowski (normalizedProjection v z) (normalizedProjection v z) =
      minkowski z z - (minkowski v z)^2 := by
  rw [normalizedProjection_mixed v z z hv]
  ring

/-- The actual physical projected mixed norm agrees with the normalized formula after cancelling c. -/
theorem projection_scaled_mixed (c : ℝ) (hc : c ≠ 0) (v z w : Covector)
    (hv : minkowski v v = 1) :
    minkowski (projection c (c • v) z) (projection c (c • v) w) =
      minkowski z w - minkowski v z * minkowski v w := by
  rw [projection_scaled c hc, projection_scaled c hc, normalizedProjection_mixed v z w hv]

/-- The time-frame jet is the actual sum of its three spatial boost components. -/
def timeJet (V : Fin 4 → Covector) (b1 b2 b3 : ℝ) : Covector :=
  b1 • V 1 + b2 • V 2 + b3 • V 3

/-- The spin-frame jet has one temporal boost component and two transverse rotation components. -/
def spinJet (V : Fin 4 → Covector) (b3 r13 r23 : ℝ) : Covector :=
  b3 • V 0 - r13 • V 1 - r23 • V 2

/-- The spatial part of the actual spin-frame jet after removing its temporal component. -/
def projectedSpinJet (V : Fin 4 → Covector) (r13 r23 : ℝ) : Covector :=
  (-r13) • V 1 + (-r23) • V 2

variable (V : Fin 4 → Covector)
variable (hV : ∀ A B, minkowski (V A) (V B) = if A=B then sign A else 0)
include hV

/-- The temporal component of the spin jet is exactly its third boost coefficient. -/
theorem time_spinJet (b3 r13 r23 : ℝ) :
    minkowski (V 0) (spinJet V b3 r13 r23) = b3 := by
  simp [spinJet, pair_sub_right, pair_smul_right, hV, sign]

/-- The actual normalized projection removes the temporal boost term from the spin jet. -/
theorem normalizedProjection_spinJet (b3 r13 r23 : ℝ) :
    normalizedProjection (V 0) (spinJet V b3 r13 r23) = projectedSpinJet V r13 r23 := by
  rw [normalizedProjection, time_spinJet V hV]
  unfold spinJet projectedSpinJet
  module

/-- The physical Fermi--Walker projection has the same explicit transverse rotation components for every nonzero c. -/
theorem projection_spinJet (c : ℝ) (hc : c ≠ 0) (b3 r13 r23 : ℝ) :
    projection c (c • V 0) (spinJet V b3 r13 r23) = projectedSpinJet V r13 r23 := by
  rw [projection_scaled c hc, normalizedProjection_spinJet V hV]

/-- Two time-frame jets have the negative Euclidean pairing of their three boost coefficients. -/
theorem timeJet_mixed (b1 b2 b3 d1 d2 d3 : ℝ) :
    minkowski (timeJet V b1 b2 b3) (timeJet V d1 d2 d3) =
      -(b1*d1+b2*d2+b3*d3) := by
  simp only [timeJet, pair_add_left, pair_add_right, pair_smul_left, pair_smul_right, hV]
  norm_num [sign]
  ring

/-- The actual time-frame jet squared norm is the negative sum of the three squared boost coefficients. -/
theorem timeJet_squared (b1 b2 b3 : ℝ) :
    minkowski (timeJet V b1 b2 b3) (timeJet V b1 b2 b3) = -(b1^2+b2^2+b3^2) := by
  rw [timeJet_mixed V hV]
  ring

/-- Two full spin-frame jets have one positive boost product and two negative transverse rotation products. -/
theorem spinJet_mixed (b3 r13 r23 d3 q13 q23 : ℝ) :
    minkowski (spinJet V b3 r13 r23) (spinJet V d3 q13 q23) =
      b3*d3-r13*q13-r23*q23 := by
  simp only [spinJet, pair_sub_left, pair_sub_right, pair_smul_left, pair_smul_right, hV]
  norm_num [sign]
  ring

/-- Two projected spin jets have the negative pairing of the two transverse rotation coefficients. -/
theorem projectedSpinJet_mixed (r13 r23 q13 q23 : ℝ) :
    minkowski (projectedSpinJet V r13 r23) (projectedSpinJet V q13 q23) =
      -(r13*q13+r23*q23) := by
  simp only [projectedSpinJet, pair_add_left, pair_add_right, pair_smul_left, pair_smul_right, hV]
  norm_num [sign]
  ring

/-- The actual projected spin-jet squared norm is minus the sum of its two squared rotation coefficients. -/
theorem projectedSpinJet_squared (r13 r23 : ℝ) :
    minkowski (projectedSpinJet V r13 r23) (projectedSpinJet V r13 r23) = -(r13^2+r23^2) := by
  rw [projectedSpinJet_mixed V hV]
  ring

/-- The time-frame jet is orthogonal to the timelike frame vector. -/
theorem timeJet_perp_time (b1 b2 b3 : ℝ) : minkowski (V 0) (timeJet V b1 b2 b3) = 0 := by
  simp [timeJet, pair_add_right, pair_smul_right, hV]

/-- The projected spin jet is orthogonal to the timelike frame vector. -/
theorem projectedSpinJet_perp_time (r13 r23 : ℝ) :
    minkowski (V 0) (projectedSpinJet V r13 r23) = 0 := by
  simp only [projectedSpinJet, pair_add_right, pair_smul_right, hV]
  norm_num [sign]

/-- The projected spin jet is also orthogonal to the spin-frame vector. -/
theorem projectedSpinJet_perp_spin (r13 r23 : ℝ) :
    minkowski (V 3) (projectedSpinJet V r13 r23) = 0 := by
  simp only [projectedSpinJet, pair_add_right, pair_smul_right, hV]
  norm_num [sign]

/-- The time-frame and projected spin-frame jets have the exact boost-rotation mixed pairing. -/
theorem timeJet_projectedSpinJet_mixed (b1 b2 b3 r13 r23 : ℝ) :
    minkowski (timeJet V b1 b2 b3) (projectedSpinJet V r13 r23) = b1*r13+b2*r23 := by
  simp only [timeJet, projectedSpinJet, pair_add_left, pair_add_right,
    pair_smul_left, pair_smul_right, hV]
  norm_num [sign]
  ring

/-- The actual physical velocity-jet pairing divided by c squared is exactly the dimensionless time-frame pairing. -/
theorem physical_velocityJet_mixed (c : ℝ) (hc : c ≠ 0) (b1 b2 b3 d1 d2 d3 : ℝ) :
    minkowski (c • timeJet V b1 b2 b3) (c • timeJet V d1 d2 d3) / c^2 =
      -(b1*d1+b2*d2+b3*d3) := by
  rw [pair_smul_left, pair_smul_right, timeJet_mixed V hV]
  field_simp

/-- Two physical Fermi--Walker projected spin jets have the exact negative transverse rotation pairing. -/
theorem projection_spinJet_mixed (c : ℝ) (hc : c ≠ 0)
    (b3 r13 r23 d3 q13 q23 : ℝ) :
    minkowski (projection c (c • V 0) (spinJet V b3 r13 r23))
      (projection c (c • V 0) (spinJet V d3 q13 q23)) = -(r13*q13+r23*q23) := by
  rw [projection_spinJet V hV c hc, projection_spinJet V hV c hc,
    projectedSpinJet_mixed V hV]

/-- The physical Fermi--Walker projected spin-jet squared norm contains precisely the two negative squared transverse rotation coefficients. -/
theorem projection_spinJet_squared (c : ℝ) (hc : c ≠ 0) (b3 r13 r23 : ℝ) :
    minkowski (projection c (c • V 0) (spinJet V b3 r13 r23))
      (projection c (c • V 0) (spinJet V b3 r13 r23)) = -(r13^2+r23^2) := by
  rw [projection_spinJet V hV c hc, projectedSpinJet_squared V hV]

/-- The actual physical velocity-jet squared norm divided by c squared is the negative sum of the three squared boost coefficients. -/
theorem physical_velocityJet_squared (c : ℝ) (hc : c ≠ 0) (b1 b2 b3 : ℝ) :
    minkowski (c • timeJet V b1 b2 b3) (c • timeJet V b1 b2 b3) / c^2 =
      -(b1^2+b2^2+b3^2) := by
  rw [physical_velocityJet_mixed V hV c hc]
  ring

/-- The normalized Fermi--Walker projected spin-jet squared norm is exactly the two negative squared transverse rotation coefficients. -/
theorem normalizedProjection_spinJet_squared (b3 r13 r23 : ℝ) :
    minkowski (normalizedProjection (V 0) (spinJet V b3 r13 r23))
      (normalizedProjection (V 0) (spinJet V b3 r13 r23)) = -(r13^2+r23^2) := by
  rw [normalizedProjection_spinJet V hV, projectedSpinJet_squared V hV]

end FoliationQM.FermiWalkerProjection
