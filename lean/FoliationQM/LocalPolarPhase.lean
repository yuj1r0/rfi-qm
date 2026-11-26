module

public import FoliationQM.WaveScoreAlgebra
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Actual local polar actions and their derivatives

Sources: v13 `eq:p_var_decomp` and `thm:uncertainty`, component kinds C and D.
The action is a genuine normalized-log function with a fixed basepoint.
Its algebraic polar identity holds at every value, including nodes, while
regularity is proved on an actual nonzero neighborhood of that basepoint.
No globally regular principal argument or global nonvanishing is assumed.
The AE specialization uses one actual derivative event, preserving the
uniform pointwise derivative statement on the local interval.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LocalPolarPhase
open MeasureTheory Filter WaveScoreAlgebra
open scoped Topology

/-- The basepoint is fixed in the actual normalized-log action being differentiated. -/
def action (hbar : ℝ) (u : ℝ → ℂ) (x0 x : ℝ) : ℝ :=
  hbar * (Complex.arg (u x0) + (Complex.log (u x / u x0)).im)

/-- The actual action gives the literal polar value identity, including zero wave values. -/
theorem polar_identity (hbar : ℝ) (u : ℝ → ℂ) (x0 : ℝ)
    (hh : hbar ≠ 0) (hbase : u x0 ≠ 0) (x : ℝ) :
    u x = (Real.sqrt (density (u x)) : ℂ) *
      Complex.exp (Complex.I * ((action hbar u x0 x / hbar : ℝ) : ℂ)) := by
  have hm : u x0 * (u x / u x0) = u x := mul_div_cancel₀ (u x) hbase
  have hn : ‖u x‖ = ‖u x0‖ * ‖u x / u x0‖ := by rw [← norm_mul, hm]
  rw [action, mul_div_cancel_left₀ _ hh, density, Real.sqrt_sq (norm_nonneg _),
    Complex.log_im, hn, Complex.ofReal_mul, Complex.ofReal_add, mul_add,
    Complex.exp_add, mul_comm Complex.I (Complex.arg (u x0) : ℂ),
    mul_comm Complex.I (Complex.arg (u x / u x0) : ℂ)]
  calc
    u x = ((‖u x0‖ : ℂ) * Complex.exp ((Complex.arg (u x0) : ℂ) * Complex.I)) *
        ((‖u x / u x0‖ : ℂ) *
          Complex.exp ((Complex.arg (u x / u x0) : ℂ) * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
      exact hm.symm
    _ = _ := by ring

/-- On the actual logarithm branch, differentiating the fixed-basepoint action gives bulk momentum. -/
theorem hasDerivAt_action (hbar : ℝ) {u : ℝ → ℂ} {x0 x : ℝ} {z : ℂ}
    (hbase : u x0 ≠ 0) (hd : HasDerivAt u z x)
    (hbranch : u x / u x0 ∈ Complex.slitPlane) :
    HasDerivAt (action hbar u x0) (bulk hbar (u x) z) x := by
  have hlog := (hd.div_const (u x0)).clog_real hbranch
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hlog
  unfold action
  rw [bulk, phaseRate_eq_im_div]
  simpa only [Function.comp_apply, Complex.imCLM_apply, div_div_div_cancel_right₀ hbase] using!
    (him.const_add (Complex.arg (u x0))).const_mul hbar

/-- Every nonzero basepoint has an actual AC polar action on a nonzero closed neighborhood,
with a uniform implication for every genuine wave derivative on that interval. -/
theorem exists_local_action {u : ℝ → ℂ} (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (x0 : ℝ) (hbase : u x0 ≠ 0) (hbar : ℝ) (hh : hbar ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      AbsolutelyContinuousOnInterval (action hbar u x0) (x0 - r) (x0 + r) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), u y ≠ 0) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r),
        u y = (Real.sqrt (density (u y)) : ℂ) *
          Complex.exp (Complex.I * ((action hbar u x0 y / hbar : ℝ) : ℂ))) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), ∀ z : ℂ,
        HasDerivAt u z y → HasDerivAt (action hbar u x0) (bulk hbar (u y) z) y) := by
  let q : ℝ → ℂ := fun y => u y / u x0
  have hq : Continuous q := hc.div_const (u x0)
  have hq0 : q x0 = 1 := by simp [q, hbase]
  have hlog : ContDiffAt ℂ 1 Complex.log (1 : ℂ) :=
    Complex.contDiffAt_log Complex.one_mem_slitPlane
  obtain ⟨K, t, ht, hLip⟩ := hlog.exists_lipschitzOnWith
  have hpre : {y : ℝ | q y ∈ t ∩ Complex.slitPlane} ∈ 𝓝 x0 := by
    have he : t ∩ Complex.slitPlane ∈ 𝓝 (q x0) := by
      rw [hq0]
      exact inter_mem ht (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
    exact hq.continuousAt.eventually he
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  have hsub : ∀ y ∈ Set.uIcc (x0 - r) (x0 + r), q y ∈ t ∩ Complex.slitPlane := by
    intro y hy
    apply hball
    simpa only [Real.closedBall_eq_Icc, Set.uIcc_of_le (by linarith : x0 - r ≤ x0 + r)]
      using hy
  have hqAC : AbsolutelyContinuousOnInterval q (x0 - r) (x0 + r) := by
    convert (hAC (x0 - r) (x0 + r)).const_smul (u x0)⁻¹ using 1
    funext y
    simp only [q, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hlogAC := hLip.comp_absolutelyContinuousOnInterval
    (fun y hy => (hsub y hy).1) hqAC
  have himAC := Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hlogAC
  have hcAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => Complex.arg (u x0))
      (x0 - r) (x0 + r) :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => Complex.arg (u x0))).contDiffOn.absolutelyContinuousOnInterval
  have ha := (hcAC.add himAC).const_mul hbar
  change AbsolutelyContinuousOnInterval (action hbar u x0) (x0 - r) (x0 + r) at ha
  refine ⟨r, hr, ha, ?_, ?_, ?_⟩
  · intro y hy hz
    apply Complex.slitPlane_ne_zero (hsub y hy).2
    simp only [q, hz, zero_div]
  · intro y _
    exact polar_identity hbar u x0 hh hbase y
  · intro y hy z hd
    exact hasDerivAt_action hbar hbase hd (hsub y hy).2

/-- One actual AE wave-derivative event specializes each genuine local action,
while retaining its uniform pointwise derivative and polar neighborhood data. -/
theorem exists_local_action_ae {u g : ℝ → ℂ} (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ y ∂volume, HasDerivAt u (g y) y)
    (x0 : ℝ) (hbase : u x0 ≠ 0) (hbar : ℝ) (hh : hbar ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      AbsolutelyContinuousOnInterval (action hbar u x0) (x0 - r) (x0 + r) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), u y ≠ 0) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r),
        u y = (Real.sqrt (density (u y)) : ℂ) *
          Complex.exp (Complex.I * ((action hbar u x0 y / hbar : ℝ) : ℂ))) ∧
      (∀ y ∈ Set.uIcc (x0 - r) (x0 + r), ∀ z : ℂ,
        HasDerivAt u z y → HasDerivAt (action hbar u x0) (bulk hbar (u y) z) y) ∧
      (∀ᵐ y ∂volume, y ∈ Set.uIcc (x0 - r) (x0 + r) →
        HasDerivAt (action hbar u x0) (bulk hbar (u y) (g y)) y) := by
  obtain ⟨r, hr, ha, hn, hp, hder⟩ := exists_local_action hc hAC x0 hbase hbar hh
  refine ⟨r, hr, ha, hn, hp, hder, ?_⟩
  filter_upwards [hd] with y hy
  intro hmem
  exact hder y hmem (g y) hy

end FoliationQM.LocalPolarPhase
