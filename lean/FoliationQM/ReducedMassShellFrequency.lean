module

public import FoliationQM.GaussianKGMode

/-!
# Reduced massive dispersion and its Schrödinger comparison

Source: v13 `cor:schrodinger`, component kinds C and D. Subtracting the
physical rest frequency from the actual positive mass-shell branch gives
exact dispersion and rationalization identities. The resulting frequency
gap has a global inverse-square bound in c using the explicit sum of three
spatial squares. No bounded spectrum or small-frequency premise is imposed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ReducedMassShellFrequency

open LorentzCoordinates GaussianKGMode

/-- The actual positive mass-shell frequency in physical time after removing the rest carrier. -/
def reducedFrequency (p : MassiveParameters) (k : Spatial) : ℝ :=
  p.c * rate (p.m * p.c / p.hbar) k - p.omega0

/-- The physical Schrödinger angular frequency for the same spatial wave vector. -/
def schrodingerFrequency (p : MassiveParameters) (k : Spatial) : ℝ :=
  p.hbar * speedSq k / (2 * p.m)

/-- The reduced frequency satisfies the exact massive dispersion identity with the actual spatial square sum. -/
theorem dispersion_identity (p : MassiveParameters) (k : Spatial) :
    reducedFrequency p k * (2 * p.omega0 + reducedFrequency p k) = p.c ^ 2 * speedSq k := by
  calc
    _ = p.c ^ 2 * (rate (p.m * p.c / p.hbar) k ^ 2 - (p.m * p.c / p.hbar) ^ 2) := by
      unfold reducedFrequency MassiveParameters.omega0
      ring
    _ = p.c ^ 2 * speedSq k := by rw [rate_sq]; ring

/-- Rationalization has a genuinely positive denominator and preserves the same actual reduced frequency. -/
theorem rationalized_frequency (p : MassiveParameters) (k : Spatial) :
    0 < p.c * rate (p.m * p.c / p.hbar) k + p.omega0 ∧
      reducedFrequency p k = p.c ^ 2 * speedSq k /
        (p.c * rate (p.m * p.c / p.hbar) k + p.omega0) := by
  have hω : 0 < p.omega0 :=
    div_pos (mul_pos p.m_pos (sq_pos_of_pos p.c_pos)) p.hbar_pos
  have hd : 0 < p.c * rate (p.m * p.c / p.hbar) k + p.omega0 :=
    add_pos_of_nonneg_of_pos (mul_nonneg p.c_pos.le (Real.sqrt_nonneg _)) hω
  refine ⟨hd, (eq_div_iff hd.ne').mpr ?_⟩
  calc
    _ = reducedFrequency p k * (2 * p.omega0 + reducedFrequency p k) := by
      unfold reducedFrequency
      ring
    _ = p.c ^ 2 * speedSq k := dispersion_identity p k

/-- The exact Schrödinger frequency gap is a positive inverse-square coefficient times the reduced frequency squared. -/
theorem gap_identity (p : MassiveParameters) (k : Spatial) :
    schrodingerFrequency p k - reducedFrequency p k =
      p.hbar / (2 * p.m * p.c ^ 2) * reducedFrequency p k ^ 2 := by
  let a : ℝ := p.hbar / (2 * p.m * p.c ^ 2)
  have hrest : a * (2 * p.omega0) = 1 := by
    dsimp [a, MassiveParameters.omega0]
    field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne']
  have hspatial : a * (p.c ^ 2 * speedSq k) = schrodingerFrequency p k := by
    dsimp [a, schrodingerFrequency]
    field_simp [p.m_pos.ne', p.c_pos.ne']
  have hform : a * (reducedFrequency p k * (2 * p.omega0 + reducedFrequency p k)) =
      reducedFrequency p k + a * reducedFrequency p k ^ 2 := by
    calc
      _ = (a * (2 * p.omega0)) * reducedFrequency p k + a * reducedFrequency p k ^ 2 := by ring
      _ = _ := by rw [hrest, one_mul]
  have h := congrArg (fun t : ℝ => a * t) (dispersion_identity p k)
  rw [hform, hspatial] at h
  change schrodingerFrequency p k - reducedFrequency p k = a * reducedFrequency p k ^ 2
  linarith only [h]

/-- The reduced frequency lies between zero and its Schrödinger limit, with the explicit global quartic spatial error bound. -/
theorem frequency_comparison (p : MassiveParameters) (k : Spatial) :
    0 ≤ reducedFrequency p k ∧ reducedFrequency p k ≤ schrodingerFrequency p k ∧
      schrodingerFrequency p k - reducedFrequency p k ≤
        p.hbar ^ 3 * speedSq k ^ 2 / (8 * p.m ^ 3 * p.c ^ 2) := by
  have hr := rationalized_frequency p k
  have hw : 0 ≤ reducedFrequency p k := by
    rw [hr.2]
    exact div_nonneg (mul_nonneg (sq_nonneg p.c) (speedSq_nonneg k)) hr.1.le
  have ha : 0 ≤ p.hbar / (2 * p.m * p.c ^ 2) :=
    (div_pos p.hbar_pos (mul_pos (mul_pos (by norm_num) p.m_pos)
      (sq_pos_of_pos p.c_pos))).le
  have hle : reducedFrequency p k ≤ schrodingerFrequency p k := by
    apply sub_nonneg.mp
    rw [gap_identity]
    exact mul_nonneg ha (sq_nonneg _)
  refine ⟨hw, hle, ?_⟩
  calc
    _ = p.hbar / (2 * p.m * p.c ^ 2) * reducedFrequency p k ^ 2 := gap_identity p k
    _ ≤ p.hbar / (2 * p.m * p.c ^ 2) * schrodingerFrequency p k ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw hle 2) ha
    _ = p.hbar ^ 3 * speedSq k ^ 2 / (8 * p.m ^ 3 * p.c ^ 2) := by
      unfold schrodingerFrequency
      field_simp [p.m_pos.ne', p.c_pos.ne']
      ring

/-- Both actual spatial frequency functions are continuous, including at the zero wave vector. -/
theorem continuous_frequencies (p : MassiveParameters) :
    Continuous (reducedFrequency p) ∧ Continuous (schrodingerFrequency p) := by
  constructor
  · unfold reducedFrequency GaussianKGMode.rate speedSq spatialDot
    fun_prop
  · unfold schrodingerFrequency speedSq spatialDot
    fun_prop

end FoliationQM.ReducedMassShellFrequency
