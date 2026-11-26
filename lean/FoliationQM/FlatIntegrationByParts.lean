module

public import FoliationQM.ActionVariation
public import FoliationQM.Madelung
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
Flat spacetime integration by parts for compactly supported variations.
Sources: v13 `thm:kahler` and `eq:master_variational_equivalence`.
These results specialize the boundary step to the flat whole-space setting;
they do not cover curved metrics, open-domain boundary terms, or phase charts.
The measure is Lebesgue volume on the four coordinates (ct,x,y,z).
Compact support eliminates the boundary contribution. The field itself need
not have compact support or finite total action.
-/
@[expose] public section

namespace FoliationQM.FlatIntegrationByParts

open MeasureTheory PolarSecondDifferential ActionVariation
open scoped ComplexConjugate

/-- A constant directional derivative of a twice continuously differentiable
field is continuously differentiable. -/
theorem contDiff_directionalDerivative {f : Covector → ℂ}
    (hf : ContDiff ℝ 2 f) (v : Covector) :
    ContDiff ℝ 1 (directionalDerivative f v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- The flat wave operator of a C² field is continuous. -/
theorem continuous_box {f : Covector → ℂ} (hf : ContDiff ℝ 2 f)
    (e : Fin 4 → Covector) : Continuous (box f e) := by
  have h (μ : Fin 4) : Continuous (secondDirectionalDerivative f (e μ)) :=
    ((contDiff_directionalDerivative hf (e μ)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const
  exact ((h 0).sub (h 1)).sub (h 2) |>.sub (h 3)

/-- Continuous products with a compactly supported conjugated factor are
integrable over flat spacetime. -/
theorem integrable_conj_mul {f g : Covector → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport f) :
    Integrable (fun x => conj (f x) * g x) := by
  have hs : HasCompactSupport (fun x => conj (f x)) :=
    hc.comp_left (map_zero _)
  exact (hf.star.mul hg).integrable_of_hasCompactSupport hs.mul_right

/-- The coordinate kinetic product of a compactly supported C¹ variation
and a C² field is integrable. -/
theorem integrable_derivative_pair {f g : Covector → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) (v : Covector) :
    Integrable (fun x => conj (directionalDerivative f v x) *
      directionalDerivative g v x) := by
  exact integrable_conj_mul
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (contDiff_directionalDerivative hg v).continuous (hc.fderiv_apply ℝ v)

/-- Actual directional integration by parts, with all integrability facts
derived from compact support and the stated regularity. -/
theorem integral_derivative_pair_eq {f g : Covector → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) (v : Covector) :
    (∫ x, conj (directionalDerivative f v x) * directionalDerivative g v x) =
      -(∫ x, conj (f x) * secondDirectionalDerivative g v x) := by
  have hfc : ContDiff ℝ 1 (fun x => conj (f x)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp hf
  have hgc := contDiff_directionalDerivative hg v
  have hder (x : Covector) :
      fderiv ℝ (fun y => conj (f y)) x v = conj (directionalDerivative f v x) :=
    ActionDensity.fderiv_conj_apply (hf.differentiable (by norm_num) x) v
  have hleft : Integrable (fun x =>
      fderiv ℝ (fun y => conj (f y)) x v * directionalDerivative g v x) := by
    simp_rw [hder]
    exact integrable_derivative_pair hf hg hc v
  have hright : Integrable (fun x =>
      conj (f x) * fderiv ℝ (directionalDerivative g v) x v) :=
    integrable_conj_mul hf.continuous
      ((hgc.continuous_fderiv (by norm_num)).clm_apply continuous_const) hc
  have hproduct : Integrable (fun x => conj (f x) * directionalDerivative g v x) :=
    integrable_conj_mul hf.continuous hgc.continuous hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hleft hright hproduct
    (fun x _ => hfc.differentiable (by norm_num) x)
    (fun x _ => hgc.differentiable (by norm_num) x)
  simp_rw [hder] at h
  change (∫ x, conj (f x) * secondDirectionalDerivative g v x) =
    -(∫ x, conj (directionalDerivative f v x) * directionalDerivative g v x) at h
  exact (neg_neg _).symm.trans (congrArg Neg.neg h.symm)

/-- The dimensional flat Klein--Gordon operator obtained from the source action. -/
noncomputable def kgOperator (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (x : Covector) : ℂ :=
  (p.hbar : ℂ) ^ 2 * box ψ e x + (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 * ψ x

/-- The action's Klein--Gordon operator is continuous for C² fields. -/
theorem continuous_kgOperator (p : MassiveParameters) {ψ : Covector → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (e : Fin 4 → Covector) :
    Continuous (kgOperator p ψ e) :=
  ((continuous_box hψ e).const_mul _).add (hψ.continuous.const_mul _)

/-- A compactly supported C¹ variation has integrable pairing with a C² field. -/
theorem integrable_fieldPairing (p : MassiveParameters) {η ψ : Covector → ℂ}
    (hη : ContDiff ℝ 1 η) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport η) (e : Fin 4 → Covector) :
    Integrable (fieldPairing p η ψ e) := by
  have hk (μ : Fin 4) := integrable_derivative_pair hη hψ hc (e μ)
  have hm := integrable_conj_mul hη.continuous hψ.continuous hc
  convert (((hk 0).sub (hk 1)).sub (hk 2) |>.sub (hk 3)).const_mul
      ((p.hbar : ℂ) ^ 2) |>.sub (hm.const_mul ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2)) using 1
  ext x
  simp only [fieldPairing, pairing, kineticPairing, Pi.sub_apply]
  ring

/-- The compactly supported test pairing with the actual KG operator is integrable. -/
theorem integrable_test_kgOperator (p : MassiveParameters) {η ψ : Covector → ℂ}
    (hη : ContDiff ℝ 1 η) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport η) (e : Fin 4 → Covector) :
    Integrable (fun x => conj (η x) * kgOperator p ψ e x) :=
  integrable_conj_mul hη.continuous (continuous_kgOperator p hψ e) hc

/-- Four-dimensional flat integration by parts identifies the polarized action
with the weak Klein--Gordon operator. Compact support supplies the boundary
condition and all product integrability requirements. -/
theorem integral_fieldPairing_eq (p : MassiveParameters) {η ψ : Covector → ℂ}
    (hη : ContDiff ℝ 1 η) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport η) (e : Fin 4 → Covector) :
    (∫ x, fieldPairing p η ψ e x) =
      -(∫ x, conj (η x) * kgOperator p ψ e x) := by
  let k (μ : Fin 4) (x : Covector) :=
    conj (directionalDerivative η (e μ) x) * directionalDerivative ψ (e μ) x
  let b (μ : Fin 4) (x : Covector) :=
    conj (η x) * secondDirectionalDerivative ψ (e μ) x
  let m (x : Covector) := conj (η x) * ψ x
  have hk (μ : Fin 4) : Integrable (k μ) := integrable_derivative_pair hη hψ hc (e μ)
  have hb (μ : Fin 4) : Integrable (b μ) := integrable_conj_mul hη.continuous
    (((contDiff_directionalDerivative hψ (e μ)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const) hc
  have hm : Integrable m := integrable_conj_mul hη.continuous hψ.continuous hc
  have hibp (μ : Fin 4) : (∫ x, k μ x) = -(∫ x, b μ x) :=
    integral_derivative_pair_eq hη hψ hc (e μ)
  have hp : fieldPairing p η ψ e = fun x =>
      (p.hbar : ℂ) ^ 2 * (k 0 x - k 1 x - k 2 x - k 3 x) -
        ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2) * m x := by
    funext x
    simp only [fieldPairing, pairing, kineticPairing, k, m]
    ring
  have ho : (fun x => conj (η x) * kgOperator p ψ e x) = fun x =>
      (p.hbar : ℂ) ^ 2 * (b 0 x - b 1 x - b 2 x - b 3 x) +
        ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2) * m x := by
    funext x
    simp only [kgOperator, box, b, m]
    ring
  have hks : Integrable (fun x => k 0 x - k 1 x - k 2 x - k 3 x) :=
    ((hk 0).sub (hk 1) |>.sub (hk 2) |>.sub (hk 3))
  have hbs : Integrable (fun x => b 0 x - b 1 x - b 2 x - b 3 x) :=
    ((hb 0).sub (hb 1) |>.sub (hb 2) |>.sub (hb 3))
  rw [hp, ho]
  dsimp only
  rw [integral_sub (hks.const_mul _) (hm.const_mul _),
    integral_add (hbs.const_mul _) (hm.const_mul _)]
  simp only [integral_const_mul]
  rw [integral_sub (f := fun x => k 0 x - k 1 x - k 2 x) (g := k 3)
      ((hk 0).sub (hk 1) |>.sub (hk 2)) (hk 3),
    integral_sub (f := fun x => k 0 x - k 1 x) (g := k 2) ((hk 0).sub (hk 1)) (hk 2),
    integral_sub (hk 0) (hk 1),
    integral_sub (f := fun x => b 0 x - b 1 x - b 2 x) (g := b 3)
      ((hb 0).sub (hb 1) |>.sub (hb 2)) (hb 3),
    integral_sub (f := fun x => b 0 x - b 1 x) (g := b 2) ((hb 0).sub (hb 1)) (hb 2),
    integral_sub (hb 0) (hb 1)]
  rw [hibp 0, hibp 1, hibp 2, hibp 3]
  ring

end FoliationQM.FlatIntegrationByParts
