module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Genuine weak derivatives extracted from the source Sobolev class

Sources: v13 thm:uncertainty, eq:cramer_rao and eq:p_var_decomp,
component kinds C and D. The weak derivative is defined by actual compact
smooth test integrals over a Banach target. The standard pinned Bessel H¹
condition supplies an L² distributional derivative and hence this relation.
No absolutely continuous representative, boundary identity or uncertainty
bound is assumed or asserted here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevWeakDerivative
open MeasureTheory
open scoped ENNReal ContDiff SchwartzMap LineDeriv

/-- The actual distributional weak derivative, with finite local integrals.
Completeness is an explicit parameter: the Bochner integral on an incomplete
target must not silently make the test relation vacuous. -/
structure HasWeakDerivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f g : ℝ → F) : Prop where
  locallyIntegrable_left : LocallyIntegrable f volume
  locallyIntegrable_right : LocallyIntegrable g volume
  integral_test : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, φ x • g x = -(∫ x, deriv φ x • f x)

section Banach
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f g f' g' : ℝ → F}

/-- The derivative pairing with a compact smooth test is genuinely integrable. -/
theorem HasWeakDerivative.integrable_test_smul (h : HasWeakDerivative f g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => φ x • g x) volume :=
  h.locallyIntegrable_right.integrable_smul_left_of_hasCompactSupport hφ.continuous hs

/-- The differentiated test pairing is genuinely integrable as well. -/
theorem HasWeakDerivative.integrable_deriv_test_smul (h : HasWeakDerivative f g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => deriv φ x • f x) volume :=
  h.locallyIntegrable_left.integrable_smul_left_of_hasCompactSupport
    (hφ.continuous_deriv (by simp)) hs.deriv

/-- Changing either representative on a null set preserves its weak derivative. -/
theorem HasWeakDerivative.congr_ae (h : HasWeakDerivative f g)
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') : HasWeakDerivative f' g' := by
  refine ⟨h.locallyIntegrable_left.congr hf, h.locallyIntegrable_right.congr hg, ?_⟩
  intro φ hφ hs
  calc
    ∫ x, φ x • g' x = ∫ x, φ x • g x := integral_congr_ae (by
      filter_upwards [hg] with x hx
      rw [hx])
    _ = -(∫ x, deriv φ x • f x) := h.integral_test φ hφ hs
    _ = -(∫ x, deriv φ x • f' x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]

/-- The weak derivative is unique almost everywhere, by the actual test-function lemma. -/
theorem HasWeakDerivative.unique_ae (h : HasWeakDerivative f g)
    (h' : HasWeakDerivative f g') : g =ᵐ[volume] g' := by
  apply ae_eq_of_integral_contDiff_smul_eq h.locallyIntegrable_right
    h'.locallyIntegrable_right
  intro φ hφ hs
  exact (h.integral_test φ hφ hs).trans (h'.integral_test φ hφ hs).symm

end Banach

/-- The actual tempered-distribution derivative equality implies the compact-test relation. -/
theorem of_distributional_eq (f g : Lp ℂ 2 (volume : Measure ℝ))
    (h : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    HasWeakDerivative f g := by
  refine ⟨(Lp.memLp f).locallyIntegrable (by norm_num),
    (Lp.memLp g).locallyIntegrable (by norm_num), ?_⟩
  intro φ hφ hs
  have hc : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hsc : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) (by simp)
  let Φ : 𝓢(ℝ, ℂ) := hsc.toSchwartzMap hc
  have hd : ∀ x, (∂_{(1 : ℝ)} Φ) x = ((deriv φ x : ℝ) : ℂ) := by
    intro x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
    exact ((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  calc
    ∫ x, φ x • g x = ∫ x, Φ x • g x := by
      apply integral_congr_ae
      filter_upwards with x
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) (φ x) (g x)
    _ = (g : 𝓢'(ℝ, ℂ)) Φ := (Lp.toTemperedDistribution_apply g Φ).symm
    _ = (∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ))) Φ := congrArg (fun T : 𝓢'(ℝ, ℂ) => T Φ) h.symm
    _ = ∫ x, (-∂_{(1 : ℝ)} Φ) x • f x := by
      rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply]
    _ = ∫ x, -(deriv φ x • f x) := by
      apply integral_congr_ae
      filter_upwards with x
      change -((∂_{(1 : ℝ)} Φ) x) • f x = -(deriv φ x • f x)
      rw [hd, neg_smul]
      exact congrArg Neg.neg
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (deriv φ x) (f x)).symm
    _ = -(∫ x, deriv φ x • f x) := integral_neg _

/-- Actual Bessel H¹ membership gives an actual L² weak derivative, without a regularity certificate. -/
theorem exists_of_memSobolev (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ))) :
    ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧ HasWeakDerivative f g := by
  have hzero : TemperedDistribution.MemSobolev 0 2
      (∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ))) := by
    simpa using hf.lineDerivOp (m := (1 : ℝ))
  obtain ⟨g, hg⟩ := TemperedDistribution.memSobolev_zero_iff.mp hzero
  exact ⟨g, hg, of_distributional_eq f g hg⟩

end FoliationQM.SobolevWeakDerivative
