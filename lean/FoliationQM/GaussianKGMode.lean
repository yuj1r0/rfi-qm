module

public import FoliationQM.LorentzCoordinates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Temporal Fourier evolution of free massive Klein–Gordon Cauchy data

For the free-packet clause of v13 `eq:dilatation_coercivity_bound` (lines
762–767), a Gaussian spatial profile prescribes only the first Cauchy datum.
In the normal coordinate s = ct a Fourier mode of wave vector k solves
u'' + (μ² + |k|²)u = 0, where μ is the inverse reduced Compton length.
The independently prescribed initial slope appears explicitly below.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianKGMode
open LorentzCoordinates

/-- Positive massive temporal frequency with respect to the normal coordinate ct. -/
def rate (μ : ℝ) (k : Spatial) : ℝ := Real.sqrt (μ ^ 2 + speedSq k)

/-- The temporal evolution of a real mode with initial value A and normal derivative B. -/
def evolution (μ : ℝ) (k : Spatial) (A B s : ℝ) : ℝ :=
  A * Real.cos (rate μ k * s) + (B / rate μ k) * Real.sin (rate μ k * s)

/-- Normal velocity of the real mode, including both Cauchy data. -/
def velocity (μ : ℝ) (k : Spatial) (A B s : ℝ) : ℝ :=
  -(A * rate μ k) * Real.sin (rate μ k * s) + B * Real.cos (rate μ k * s)

/-- The massive dispersion relation for the normal frequency on the three-dimensional spectrum. -/
theorem rate_sq (μ : ℝ) (k : Spatial) : rate μ k ^ 2 = μ ^ 2 + speedSq k :=
  Real.sq_sqrt (add_nonneg (sq_nonneg μ) (speedSq_nonneg k))

/-- The inverse Compton length gives a uniform positive lower bound on the frequency. -/
theorem mass_le_rate {μ : ℝ} (hμ : 0 < μ) (k : Spatial) : μ ≤ rate μ k := by
  calc
    μ = Real.sqrt (μ^2) := (Real.sqrt_sq hμ.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (speedSq_nonneg k))

private theorem rate_ne {μ : ℝ} (hμ : 0 < μ) (k : Spatial) : rate μ k ≠ 0 :=
  (hμ.trans_le (mass_le_rate hμ k)).ne'

/-- At normal time zero the solution and its normal velocity recover the two input data. -/
theorem cauchy_values (μ : ℝ) (k : Spatial) (A B : ℝ) :
    evolution μ k A B 0 = A ∧ velocity μ k A B 0 = B := by
  simp [evolution, velocity]

/-- The normal derivative of the explicit oscillator is the prescribed velocity field. -/
theorem hasDerivAt_evolution {μ : ℝ} (hμ : 0 < μ) (k : Spatial) (A B s : ℝ) :
    HasDerivAt (evolution μ k A B) (velocity μ k A B s) s := by
  have hl : HasDerivAt (fun t : ℝ => rate μ k * t) (rate μ k) s := by
    simpa using (hasDerivAt_id s).const_mul (rate μ k)
  convert (hl.cos.const_mul A).add (hl.sin.const_mul (B / rate μ k)) using 1
  · rfl
  dsimp [velocity]
  field_simp [rate_ne hμ k]


/-- Differentiating the velocity gives the restoring term with the massive spatial symbol. -/
theorem hasDerivAt_velocity {μ : ℝ} (hμ : 0 < μ) (k : Spatial) (A B s : ℝ) :
    HasDerivAt (velocity μ k A B) (-(μ^2 + speedSq k) * evolution μ k A B s) s := by
  have hl : HasDerivAt (fun t : ℝ => rate μ k * t) (rate μ k) s := by
    simpa using (hasDerivAt_id s).const_mul (rate μ k)
  convert (hl.sin.const_mul (-(A * rate μ k))).add (hl.cos.const_mul B) using 1
  · rfl
  rw [← rate_sq]
  dsimp [evolution]
  field_simp [rate_ne hμ k]
  ring

/-- Every frequency evolves by the free Klein–Gordon oscillator with actual second derivative. -/
theorem mode_equation {μ : ℝ} (hμ : 0 < μ) (k : Spatial) (A B s : ℝ) :
    deriv (deriv (evolution μ k A B)) s +
      (μ^2 + speedSq k) * evolution μ k A B s = 0 := by
  rw [show deriv (evolution μ k A B) = velocity μ k A B from
    funext fun t => (hasDerivAt_evolution hμ k A B t).deriv,
    (hasDerivAt_velocity hμ k A B s).deriv]
  ring

/-- The evolved multiplier is uniformly bounded in time and wave vector by its initial
amplitude plus the size of its initial normal derivative divided by the mass scale. -/
theorem abs_evolution_le {μ : ℝ} (hμ : 0 < μ) (k : Spatial) (A B s : ℝ) :
    |evolution μ k A B s| ≤ |A| + |B| / μ := by
  have hr := mass_le_rate hμ k
  calc
    _ ≤ |A * Real.cos (rate μ k * s)| + |(B / rate μ k) * Real.sin (rate μ k * s)| :=
      abs_add_le _ _
    _ ≤ |A| * 1 + (|B| / μ) * 1 := by
      simp only [abs_mul, abs_div, abs_of_pos (hμ.trans_le hr)]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_le.mpr
        ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg A))
        (mul_le_mul (div_le_div_of_nonneg_left (abs_nonneg B) hμ hr)
          (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
          (abs_nonneg _) (div_nonneg (abs_nonneg B) hμ.le))
    _ = _ := by simp

/-- Physical angular frequency of the positive-frequency branch on a fixed spectral axis. -/
def axisFrequency (μ c k : ℝ) : ℝ := c * Real.sqrt (μ^2 + k^2)

/-- The actual derivative of the positive-frequency dispersion gives the modal group velocity. -/
theorem hasDerivAt_axisFrequency {μ : ℝ} (hμ : 0 < μ) (c k : ℝ) :
    HasDerivAt (axisFrequency μ c) (c * k / Real.sqrt (μ^2 + k^2)) k := by
  have h : HasDerivAt (fun t : ℝ => μ^2 + t^2) (2*k) k := by
    simpa using ((hasDerivAt_id k).pow 2).const_add (μ^2)
  have hp : 0 < μ^2 + k^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hμ) (sq_nonneg _)
  convert (h.sqrt hp.ne').const_mul c using 1
  · rfl
  ring

/-- The absolute modal group velocity is strictly below light speed at each finite frequency. -/
theorem groupSpeed_lt {μ c : ℝ} (hμ : 0 < μ) (hc : 0 < c) (k : ℝ) :
    |deriv (axisFrequency μ c) k| < c := by
  have hp : 0 < μ^2 + k^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hμ) (sq_nonneg _)
  have hk : |k| < Real.sqrt (μ^2 + k^2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (lt_add_of_pos_left _ (sq_pos_of_pos hμ))
  rw [(hasDerivAt_axisFrequency hμ c k).deriv, abs_div, abs_mul, abs_of_pos hc,
    abs_of_pos (Real.sqrt_pos_of_pos hp), div_lt_iff₀ (Real.sqrt_pos_of_pos hp)]
  exact mul_lt_mul_of_pos_left hk hc

/-- No strict subluminal constant bounds all positive-frequency modal group speeds
on the unbounded spectrum. The observer-slice velocity in the ADM theorem is a field observable. -/
theorem no_uniform_modal_gap {μ c V : ℝ} (hμ : 0 < μ) (hc : 0 < c) (hV : 0 ≤ V)
    (hVc : V < c) : ∃ k : ℝ, V < deriv (axisFrequency μ c) k := by
  let k := μ * c / (c-V)
  have hk : 0 < k := div_pos (mul_pos hμ hc) (sub_pos.mpr hVc)
  have he : k * (c-V) = μ*c := by
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hVc.ne')
  have hr : Real.sqrt (μ^2 + k^2) ≤ μ+k := (Real.sqrt_le_left (add_pos hμ hk).le).mpr
    (by nlinarith [mul_nonneg hμ.le hk.le])
  refine ⟨k, ?_⟩
  rw [(hasDerivAt_axisFrequency hμ c k).deriv, lt_div_iff₀ (Real.sqrt_pos_of_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hμ) (sq_nonneg _)))]
  exact (mul_le_mul_of_nonneg_left hr hV).trans_lt (by nlinarith [mul_pos hμ (sub_pos.mpr hVc)])

end FoliationQM.GaussianKGMode
