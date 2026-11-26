module

public import FoliationQM.LiouvilleDifferential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FinCases

/-!
# The actual positive-energy mass-shell chart

Source: v13 `thm:contact_period`, the seven shell coordinates used in the
Liouville contact-volume calculation. The order is
`(x⁰,x¹,p₁,x²,p₂,x³,p₃)`. The chart is obtained by the actual positive square
root, and its displayed differential is proved to be its Frechet derivative.
At every positive-energy point its derivative parametrizes exactly the
linearized-shell tangent space. Massive shells have a global homeomorphism;
all pointwise differential statements also apply at positive-energy massless
points.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.MassShellChart
open ContactReeb
/-- The seven interleaved position and spatial-momentum coordinates. -/
abbrev Space := Fin 7 → ℝ
/-- The mass-shell positive-energy radicand in interleaved coordinates. -/
def energySquared (m c : ℝ) (q : Space) : ℝ := m^2*c^2 + q 2^2 + q 4^2 + q 6^2
/-- The actual positive square-root solution for the temporal momentum. -/
def energy (m c : ℝ) (q : Space) : ℝ := Real.sqrt (energySquared m c q)
/-- Extract the four spacetime coordinates from the interleaved shell coordinates. -/
def position (q : Space) : Covector := ![q 0, q 1, q 3, q 5]
/-- Parametrize the positive-energy shell by its actual square-root graph. -/
def chart (m c : ℝ) (q : Space) : Ambient :=
  (position q, ![energy m c q, q 2, q 4, q 6])
/-- Extract the seven free coordinates from flat cotangent space. -/
def inverse (z : Ambient) : Space := ![z.1 0,z.1 1,z.2 1,z.1 2,z.2 2,z.1 3,z.2 3]

/-- The mass-shell radicand is nonnegative for every real mass and speed. -/
theorem energySquared_nonneg (m c : ℝ) (q : Space) : 0 ≤ energySquared m c q := by
  unfold energySquared
  positivity

/-- The square of the actual energy equals its defining radicand. -/
theorem energy_sq (m c : ℝ) (q : Space) : energy m c q ^ 2 = energySquared m c q :=
  Real.sq_sqrt (energySquared_nonneg m c q)

/-- Positive mass and speed give positive energy at every chart point. -/
theorem energy_pos {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (q : Space) : 0 < energy m c q := by
  apply Real.sqrt_pos.mpr
  unfold energySquared
  have h : 0 < m^2*c^2 := by positivity
  nlinarith [sq_nonneg (q 2),sq_nonneg (q 4),sq_nonneg (q 6)]

/-- Extracting the free coordinates from the shell chart recovers the input. -/
theorem inverse_chart (m c : ℝ) (q : Space) : inverse (chart m c q) = q := by
  funext i
  fin_cases i <;> rfl

/-- At positive energy the chart satisfies the mass-shell equation and time orientation. -/
theorem chart_onShell {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    OnShell m c (chart m c q).2 := by
  constructor
  · have hs := energy_sq m c q
    simp only [energySquared] at hs
    change energy m c q * energy m c q - q 2 * q 2 - q 4 * q 4 - q 6 * q 6 = _
    nlinarith
  · exact hE

/-- On the future shell the square-root reconstruction equals the temporal momentum. -/
theorem energy_inverse {m c : ℝ} {z : Ambient} (hs : OnShell m c z.2) :
    energy m c (inverse z) = z.2 0 := by
  have he : energySquared m c (inverse z) = z.2 0 ^ 2 := by
    have he := hs.1
    dsimp [minkowski] at he
    change m^2*c^2 + z.2 1^2 + z.2 2^2 + z.2 3^2 = z.2 0^2
    nlinarith
  rw [energy, he, Real.sqrt_sq hs.2.le]

/-- The chart recovers every point of the future mass shell from its free coordinates. -/
theorem chart_inverse {m c : ℝ} {z : Ambient} (hs : OnShell m c z.2) :
    chart m c (inverse z) = z := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact energy_inverse hs
    all_goals rfl

/-- The energy radicand is infinitely differentiable. -/
theorem contDiff_energySquared (m c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (energySquared m c) := by
  unfold energySquared
  fun_prop

/-- The actual square-root energy is smooth at every positive-energy point. -/
theorem contDiffAt_energy {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (energy m c) q :=
  (contDiff_energySquared m c).contDiffAt.sqrt (Real.sqrt_pos.mp hE).ne'

/-- The energy is globally smooth for positive mass and speed. -/
theorem contDiff_energy {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    ContDiff ℝ (⊤ : ℕ∞) (energy m c) :=
  contDiff_iff_contDiffAt.mpr (fun q => contDiffAt_energy (energy_pos hm hc q))

/-- The position-coordinate extraction is smooth. -/
theorem contDiff_position : ContDiff ℝ (⊤ : ℕ∞) position := by
  unfold position
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj 0 : Space →L[ℝ] ℝ).contDiff
  · exact (ContinuousLinearMap.proj 1 : Space →L[ℝ] ℝ).contDiff
  · exact (ContinuousLinearMap.proj 3 : Space →L[ℝ] ℝ).contDiff
  · exact (ContinuousLinearMap.proj 5 : Space →L[ℝ] ℝ).contDiff

/-- The mass-shell chart is smooth at every positive-energy point. -/
theorem contDiffAt_chart {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (chart m c) q := by
  apply contDiff_position.contDiffAt.prodMk
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_energy hE
  · exact (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ).contDiff.contDiffAt
  · exact (ContinuousLinearMap.proj 4 : Space →L[ℝ] ℝ).contDiff.contDiffAt
  · exact (ContinuousLinearMap.proj 6 : Space →L[ℝ] ℝ).contDiff.contDiffAt

/-- The mass-shell chart is globally smooth for positive mass and speed. -/
theorem contDiff_chart {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    ContDiff ℝ (⊤ : ℕ∞) (chart m c) :=
  contDiff_iff_contDiffAt.mpr (fun q => contDiffAt_chart (energy_pos hm hc q))

/-- The continuous linear map appearing in the derivative of the square-root energy. -/
def energyDerivative (m c : ℝ) (q : Space) : Space →L[ℝ] ℝ :=
  (energy m c q)⁻¹ • (q 2 • ContinuousLinearMap.proj 2 +
    q 4 • ContinuousLinearMap.proj 4 + q 6 • ContinuousLinearMap.proj 6)

/-- Evaluate the displayed energy derivative on a coordinate vector. -/
theorem energyDerivative_apply (m c : ℝ) (q v : Space) :
    energyDerivative m c q v = (q 2*v 2 + q 4*v 4 + q 6*v 6) / energy m c q := by
  simp [energyDerivative]
  ring

/-- The displayed energy derivative is the actual Frechet derivative. -/
theorem hasFDerivAt_energy {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    HasFDerivAt (energy m c) (energyDerivative m c q) q := by
  have h2 := ((ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ).hasFDerivAt (x := q)).pow 2
  have h4 := ((ContinuousLinearMap.proj 4 : Space →L[ℝ] ℝ).hasFDerivAt (x := q)).pow 2
  have h6 := ((ContinuousLinearMap.proj 6 : Space →L[ℝ] ℝ).hasFDerivAt (x := q)).pow 2
  have hS := ((h2.const_add (m^2*c^2)).add h4).add h6
  have hr := hS.sqrt (Real.sqrt_pos.mp hE).ne'
  change HasFDerivAt (energy m c) _ q at hr
  have heq : energyDerivative m c q = (1 / (2 * energy m c q)) •
      ((2 • q 2 ^ (2-1)) • (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ) +
      (2 • q 4 ^ (2-1)) • ContinuousLinearMap.proj 4 +
      (2 • q 6 ^ (2-1)) • ContinuousLinearMap.proj 6) := by
    ext v
    simp [energyDerivative, energy, energySquared]
    ring
  rw [heq]
  exact hr

/-- Position-coordinate extraction as a continuous linear map. -/
def positionLinear : Space →L[ℝ] Covector :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 3, ContinuousLinearMap.proj 5]
/-- The continuous linear position map agrees with coordinate extraction. -/
theorem positionLinear_apply (v : Space) : positionLinear v = position v := by
  funext i
  fin_cases i <;> rfl

/-- The displayed continuous linear derivative of the mass-shell graph. -/
def chartDerivative (m c : ℝ) (q : Space) : Space →L[ℝ] Ambient :=
  positionLinear.prod (ContinuousLinearMap.pi ![energyDerivative m c q,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 4, ContinuousLinearMap.proj 6])

/-- Evaluate the chart derivative in the seven interleaved coordinates. -/
theorem chartDerivative_apply (m c : ℝ) (q v : Space) :
    chartDerivative m c q v = (position v,
      ![(q 2*v 2 + q 4*v 4 + q 6*v 6) / energy m c q, v 2, v 4, v 6]) := by
  rw [chartDerivative]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact energyDerivative_apply m c q v
    all_goals rfl

/-- The displayed chart derivative is its actual Frechet derivative. -/
theorem hasFDerivAt_chart {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    HasFDerivAt (chart m c) (chartDerivative m c q) q := by
  have hp : HasFDerivAt position positionLinear q := by
    have heq : (positionLinear : Space → Covector) = position := funext positionLinear_apply
    rw [← heq]
    exact positionLinear.hasFDerivAt
  apply hp.prodMk
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_energy hE
  · exact (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ).hasFDerivAt
  · exact (ContinuousLinearMap.proj 4 : Space →L[ℝ] ℝ).hasFDerivAt
  · exact (ContinuousLinearMap.proj 6 : Space →L[ℝ] ℝ).hasFDerivAt

/-- Identify Mathlib's Frechet derivative with the explicit shell derivative. -/
theorem fderiv_chart {m c : ℝ} {q : Space} (hE : 0 < energy m c q) :
    fderiv ℝ (chart m c) q = chartDerivative m c q := (hasFDerivAt_chart hE).fderiv

/-- Free-coordinate extraction is a left inverse of the chart derivative. -/
theorem inverse_chartDerivative (m c : ℝ) (q v : Space) :
    inverse (chartDerivative m c q v) = v := by
  rw [chartDerivative_apply]
  funext i
  fin_cases i <;> rfl

/-- The explicit chart derivative is injective. -/
theorem chartDerivative_injective (m c : ℝ) (q : Space) :
    Function.Injective (chartDerivative m c q) := by
  intro v w hvw
  have h := congrArg inverse hvw
  simpa only [inverse_chartDerivative] using h

/-- At positive energy every chart derivative vector is tangent to the mass shell. -/
theorem chartDerivative_tangent {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (v : Space) : Tangent (chart m c q).2 (chartDerivative m c q v) := by
  rw [chartDerivative_apply]
  change energy m c q * ((q 2*v 2+q 4*v 4+q 6*v 6)/energy m c q) -
    q 2*v 2-q 4*v 4-q 6*v 6=0
  field_simp
  nlinarith [hE.ne']

/-- Every linearized-shell tangent vector is recovered by the chart derivative. -/
theorem chartDerivative_inverse {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    {w : Ambient} (hw : Tangent (chart m c q).2 w) :
    chartDerivative m c q (inverse w) = w := by
  rw [chartDerivative_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · change (q 2*w.2 1+q 4*w.2 2+q 6*w.2 3)/energy m c q=w.2 0
      apply (div_eq_iff hE.ne').mpr
      change energy m c q*w.2 0-q 2*w.2 1-q 4*w.2 2-q 6*w.2 3=0 at hw
      linarith
    all_goals rfl

/-- The range of the actual chart derivative is exactly the linearized-shell tangent space. -/
theorem mem_range_fderiv_chart_iff {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (w : Ambient) : (∃v, fderiv ℝ (chart m c) q v=w) ↔ Tangent (chart m c q).2 w := by
  rw [fderiv_chart hE]
  constructor
  · rintro ⟨v,rfl⟩
    exact chartDerivative_tangent hE v
  · intro hw
    exact ⟨inverse w,chartDerivative_inverse hE hw⟩

/-- The free-coordinate inverse is an ambient smooth map. -/
theorem contDiff_inverse : ContDiff ℝ (⊤ : ℕ∞) inverse := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.1 0)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.1 1)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.2 1)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.1 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.2 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.1 3)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient => z.2 3)
    fun_prop

/-- For positive mass and speed the chart is a homeomorphism onto the full future shell. -/
def homeomorph {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    Space ≃ₜ {z : Ambient // OnShell m c z.2} where
  toFun q := ⟨chart m c q,chart_onShell (energy_pos hm hc q)⟩
  invFun z := inverse z.val
  left_inv q := inverse_chart m c q
  right_inv z := Subtype.ext (chart_inverse z.property)
  continuous_toFun := (contDiff_chart hm hc).continuous.subtype_mk _
  continuous_invFun := contDiff_inverse.continuous.comp continuous_subtype_val

end FoliationQM.MassShellChart
