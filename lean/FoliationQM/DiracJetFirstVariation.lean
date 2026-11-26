module
public import FoliationQM.DiracPolarizedDensity
public import FoliationQM.DiracCurrent
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Real Fréchet first variation of the Dirac density on full jets

For the local action calculation in v13 `thm:dirac_lift` and
`eq:dirac_lagrangian_sym`, the two projections of a jet record its
spinor and four first derivatives. Differentiability of the actual
matrix contractions and exact polarization on affine lines determine
the full Fréchet derivative and its value along arbitrary jet curves.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracJetFirstVariation
open DiracMatrices DiracAdjoint DiracDensity DiracPolarizedDensity

/-- Independent spinor value and four spinor derivative slots, with their real normed space structure. -/
abbrev Jet := Spinor × (Fin 4 → Spinor)

/-- The real symmetric Dirac density as a function on the full jet space. -/
def value (hbar c m : ℝ) (z : Jet) : ℝ := densityRe hbar c m z.1 z.2

variable (hbar c m : ℝ)

/-- The real density on the full jet space is Fréchet differentiable at every jet. -/
theorem differentiable_value : Differentiable ℝ (value hbar c m) := by
  intro z
  have hv : DifferentiableAt ℝ (fun y : Jet => y.1) z := differentiableAt_fst
  have hj (μ : Fin 4) : DifferentiableAt ℝ (fun y : Jet => y.2 μ) z :=
    ((ContinuousLinearMap.proj μ : (Fin 4 → Spinor) →L[ℝ] Spinor).comp
      (ContinuousLinearMap.snd ℝ Spinor (Fin 4 → Spinor))).differentiableAt
  have hk : DifferentiableAt ℝ (fun y : Jet => ∑ μ, directionalPair y.1 (y.2 μ) μ) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) fun μ _ =>
      (DiracCurrent.differentiableAt_bilinear hv (hj μ) (gamma μ)).sub
        (DiracCurrent.differentiableAt_bilinear (hj μ) hv (gamma μ))
  exact Complex.reCLM.differentiableAt.comp z
    ((hk.const_mul (Complex.I * (hbar : ℂ) * (c : ℂ) / 2)).sub
      ((DiracCurrent.differentiableAt_bilinear hv hv 1).const_mul ((m : ℂ) * (c : ℂ) ^ 2)))

/-- The linear coefficient of polarization is the derivative on the entire jet line at zero. -/
theorem hasLineDerivAt_value (z v : Jet) : HasLineDerivAt ℝ (value hbar c m)
    (2 * (mixed hbar c m v.1 v.2 z.1 z.2).re) z v := by
  change HasDerivAt (fun t : ℝ => densityRe hbar c m (z.1 + t • v.1) (z.2 + t • v.2)) _ 0
  simp_rw [densityRe_affine]
  simp only [pow_two]
  convert ((hasDerivAt_const (0 : ℝ) (densityRe hbar c m z.1 z.2)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (2 * (mixed hbar c m v.1 v.2 z.1 z.2).re))).add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (densityRe hbar c m v.1 v.2)) using 1
  · funext t
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  · simp

/-- The real Fréchet derivative applied to an arbitrary full jet direction. -/
theorem fderiv_value_apply (z v : Jet) :
    fderiv ℝ (value hbar c m) z v = 2 * (mixed hbar c m v.1 v.2 z.1 z.2).re :=
  ((differentiable_value hbar c m z).lineDeriv_eq_fderiv (v := v)).symm.trans
    (hasLineDerivAt_value hbar c m z v).lineDeriv

/-- Any differentiable real-parameter curve of jets has the polarized first variation
at its current jet and velocity. -/
theorem hasDerivAt_curve (γ : ℝ → Jet) {s : ℝ} {v : Jet} (hγ : HasDerivAt γ v s) :
    HasDerivAt (fun t => value hbar c m (γ t)) (2 * (mixed hbar c m v.1 v.2 (γ s).1 (γ s).2).re) s := by
  rw [← fderiv_value_apply hbar c m (γ s) v]
  exact (differentiable_value hbar c m (γ s)).hasFDerivAt.comp_hasDerivAt s hγ


end FoliationQM.DiracJetFirstVariation
