module

public import FoliationQM.ActionDensity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Smooth local inverse of the scalar polar map

Source: v13 `thm:kahler`, the local scalar change of variables on positive
density. At a nonzero anchor `a`, the chart uses the logarithm of `z / a`.
The chart domain is the inverse image of the complex slit plane and contains
`a`. This construction proves a genuine local real phase, with the same
regularity as the complex field. It does not posit a global real phase across
winding or nodal sets, and it does not by itself identify variation spaces.
-/
@[expose] public section

namespace FoliationQM.PolarLocalInverse

open ActionDensity PolarDifferential MasterMetricAndCone
open scoped Topology

/-- The logarithmic branch domain anchored at `a`. -/
def chartDomain (a : ℂ) : Set ℂ := {z | z / a ∈ Complex.slitPlane}

/-- A local real action phase, normalized to the principal argument at `a`. -/
noncomputable def localAction (p : MassiveParameters) (a z : ℂ) : ℝ :=
  p.hbar * (a.arg + (Complex.log (z / a)).im)

/-- The branch domain is open, including for the totalized zero anchor. -/
theorem isOpen_chartDomain (a : ℂ) : IsOpen (chartDomain a) :=
  Complex.isOpen_slitPlane.preimage (continuous_id.div_const a)

/-- Every nonzero anchor lies in its logarithmic branch domain. -/
theorem anchor_mem_chartDomain {a : ℂ} (ha : a ≠ 0) : a ∈ chartDomain a := by
  simp [chartDomain, div_self ha]

/-- Points in a logarithmic branch domain have strictly positive density. -/
theorem normSq_pos_of_mem_chartDomain {a z : ℂ} (hz : z ∈ chartDomain a) :
    0 < Complex.normSq z := by
  apply Complex.normSq_pos.mpr
  intro hzero
  have h := Complex.slitPlane_ne_zero hz
  exact h (by simp [hzero])

/-- Principal logarithmic phase reconstructs the actual complex value. This
identity holds even at zero; smoothness of the phase requires the slit plane. -/
theorem norm_mul_phase_log (z : ℂ) :
    (‖z‖ : ℂ) * phase (Complex.log z).im = z := by
  simp [phase, Complex.log_im]

/-- The anchored inverse chart reconstructs the complex value exactly. -/
theorem localAction_reconstruction (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0)
    (z : ℂ) :
    (Real.sqrt (Complex.normSq z) : ℂ) * phase (localAction p a z / p.hbar) = z := by
  have hnorm : ‖z‖ = ‖a‖ * ‖z / a‖ := by
    rw [← norm_mul, mul_div_cancel₀ _ ha]
  have hh := ne_of_gt p.hbar_pos
  rw [localAction, mul_div_cancel_left₀ _ hh, ← Complex.norm_def, hnorm]
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul]
  calc
    _ = ((‖a‖ : ℂ) * Complex.exp (a.arg * Complex.I)) *
        ((‖z / a‖ : ℂ) * Complex.exp ((Complex.log (z / a)).im * Complex.I)) := by ring
    _ = a * (z / a) := by rw [Complex.norm_mul_exp_arg_mul_I, ← phase,
      norm_mul_phase_log]
    _ = z := mul_div_cancel₀ _ ha

/-- In the branch domain the inverse action phase is genuinely `C^n`. -/
theorem contDiffAt_localAction (p : MassiveParameters) {a z : ℂ}
    (hz : z ∈ chartDomain a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (localAction p a) z := by
  have hlog : ContDiffAt ℝ n (fun w : ℂ => Complex.log (w / a)) z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ |>.comp z
      (contDiffAt_id.div_const a)
  exact contDiffAt_const.mul (contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp z hlog))

/-- Squared modulus is smooth over the real scalar field, including at zero. -/
theorem contDiff_normSq (n : WithTop ℕ∞) : ContDiff ℝ n Complex.normSq := by
  change ContDiff ℝ n (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

/-- The recovered action phase lies in the open branch interval relative to
its anchor, so no two representatives differing by a full turn occur there. -/
theorem localAction_mem_branch (p : MassiveParameters) {a z : ℂ}
    (hz : z ∈ chartDomain a) :
    localAction p a z / p.hbar - a.arg ∈ Set.Ioo (-Real.pi) Real.pi := by
  have hh := ne_of_gt p.hbar_pos
  simp only [localAction, mul_div_cancel_left₀ _ hh, add_sub_cancel_left,
    Complex.log_im, Set.mem_Ioo]
  exact ⟨Complex.neg_pi_lt_arg _,
    lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.slitPlane_arg_ne_pi hz)⟩

/-- The logarithmic coordinate is a left inverse on the open phase interval
centered at the anchor's argument. Combined with reconstruction, this is a
two-sided local inverse, rather than merely a chosen preimage. -/
theorem localAction_polar (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0)
    {ρ S : ℝ} (hρ : 0 < ρ)
    (hS : S / p.hbar - a.arg ∈ Set.Ioo (-Real.pi) Real.pi) :
    localAction p a ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) = S := by
  let z : ℂ := (Real.sqrt ρ : ℂ) * phase (S / p.hbar)
  have hh := ne_of_gt p.hbar_pos
  have hR : (Real.sqrt ρ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hρ))
  have hborn : Complex.normSq z = ρ :=
    polarField_normSq (fun _ : Unit => ρ) (fun _ => S / p.hbar) () hρ.le
  have hrecon := localAction_reconstruction p ha z
  rw [hborn] at hrecon
  have hphase : phase (localAction p a z / p.hbar) = phase (S / p.hbar) :=
    mul_left_cancel₀ hR hrecon
  have hshift :
      Complex.exp (((localAction p a z / p.hbar - a.arg : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((S / p.hbar - a.arg : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    exact congrArg (fun w : ℂ => w / Complex.exp (a.arg * Complex.I)) hphase
  have hlo : -Real.pi < localAction p a z / p.hbar - a.arg := by
    simpa only [localAction, mul_div_cancel_left₀ _ hh, add_sub_cancel_left] using
      Complex.neg_pi_lt_log_im (z / a)
  have hhi : localAction p a z / p.hbar - a.arg ≤ Real.pi := by
    simpa only [localAction, mul_div_cancel_left₀ _ hh, add_sub_cancel_left] using
      Complex.log_im_le_pi (z / a)
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hlo) (by simpa using hhi)
    (by simpa using hS.1) (by simpa using hS.2.le) hshift
  have him := congrArg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at him
  have hquot : localAction p a z / p.hbar = S / p.hbar := by linarith
  exact (div_left_inj' hh).mp hquot

/-- Positive-density polar points with action phase in the selected branch
map into the logarithmic chart domain. -/
theorem polar_mem_chartDomain (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0)
    {ρ S : ℝ} (hρ : 0 < ρ)
    (hS : S / p.hbar - a.arg ∈ Set.Ioo (-Real.pi) Real.pi) :
    (Real.sqrt ρ : ℂ) * phase (S / p.hbar) ∈ chartDomain a := by
  let z : ℂ := (Real.sqrt ρ : ℂ) * phase (S / p.hbar)
  change z / a ∈ Complex.slitPlane
  have hphase : (z / a).arg = S / p.hbar - a.arg := by
    have h := congrArg (fun t : ℝ => t / p.hbar - a.arg)
      (localAction_polar p ha hρ hS)
    simpa only [localAction, mul_div_cancel_left₀ _ (ne_of_gt p.hbar_pos),
      add_sub_cancel_left, Complex.log_im] using h
  refine Complex.mem_slitPlane_iff_arg.mpr ⟨?_, div_ne_zero ?_ ha⟩
  · rw [hphase]
    exact ne_of_lt hS.2
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hρ)))
      (Complex.exp_ne_zero _)

/-- The scalar polar map is injective when restricted to positive density
and a single open phase branch. Periodic global representatives are not
identified by this statement. -/
theorem polar_injOn_branch (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0) :
    Set.InjOn (fun q : ℝ × ℝ => (Real.sqrt q.1 : ℂ) * phase (q.2 / p.hbar))
      {q | 0 < q.1 ∧ q.2 / p.hbar - a.arg ∈ Set.Ioo (-Real.pi) Real.pi} := by
  intro q hq r hr heq
  apply Prod.ext
  · have hn := congrArg Complex.normSq heq
    have hqnorm := polarField_normSq (fun _ : Unit => q.1)
      (fun _ => q.2 / p.hbar) () hq.1.le
    have hrnorm := polarField_normSq (fun _ : Unit => r.1)
      (fun _ => r.2 / p.hbar) () hr.1.le
    exact hqnorm.symm.trans (hn.trans hrnorm)
  · have h := congrArg (localAction p a) heq
    simpa only [localAction_polar p ha hq.1 hq.2,
      localAction_polar p ha hr.1 hr.2] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A `C^n` complex field has a `C^n` real polar reconstruction on an explicit
open neighborhood of each nonzero point in its original open domain. The
density is exactly squared modulus and the action phase is the anchored log. -/
theorem exists_local_polar_reconstruction (p : MassiveParameters)
    {n : WithTop ℕ∞} {ψ : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ n ψ U) (hx : x ∈ U) (hne : ψ x ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ n (fun y => Complex.normSq (ψ y)) V ∧
      ContDiffOn ℝ n (fun y => localAction p (ψ x) (ψ y)) V ∧
      ∀ y ∈ V, 0 < Complex.normSq (ψ y) ∧
        actionField p (fun w => Complex.normSq (ψ w))
          (fun w => localAction p (ψ x) (ψ w)) y = ψ y := by
  let V := U ∩ ψ ⁻¹' chartDomain (ψ x)
  have hVU : V ⊆ U := Set.inter_subset_left
  refine ⟨V, hψ.continuousOn.isOpen_inter_preimage hU (isOpen_chartDomain _),
    ⟨hx, anchor_mem_chartDomain hne⟩, hVU, ?_, ?_, ?_⟩
  · intro y hy
    exact (contDiff_normSq n).contDiffAt.comp_contDiffWithinAt y
      ((hψ y hy.1).mono hVU)
  · intro y hy
    exact (contDiffAt_localAction p hy.2 n).comp_contDiffWithinAt y
      ((hψ y hy.1).mono hVU)
  · intro y hy
    refine ⟨normSq_pos_of_mem_chartDomain hy.2, ?_⟩
    exact localAction_reconstruction p hne (ψ y)

end FoliationQM.PolarLocalInverse
