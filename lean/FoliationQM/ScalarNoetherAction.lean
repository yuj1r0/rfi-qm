module

public import FoliationQM.ScalarNoetherSymmetry
public import FoliationQM.DiracActionSupport

/-!
# First variation of the scalar action under a localized phase rotation

The physical current in v13 `eq:noether_current` is the coefficient of the
derivative of the phase parameter in the Klein–Gordon action. Integrating
the exact finite phase change proves the first variation for arbitrary
smooth compact interior phase tests even on an infinite-action background.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarNoetherAction

open MeasureTheory ScalarNoetherSymmetry DressedMassDensityVariation Madelung RelativeAction
open scoped ContDiff

private theorem continuousAt_contraction {A B : Covector → Covector} {x : Covector}
    (ha : ContinuousAt A x) (hb : ContinuousAt B x) :
    ContinuousAt (fun y => minkowski (A y) (B y)) x := by
  have c (i : Fin 4) := ((continuous_apply i).continuousAt.comp ha).mul
    ((continuous_apply i).continuousAt.comp hb)
  exact (((c 0).sub (c 1)).sub (c 2)).sub (c 3)

/-- Both coefficients of the localized relative action density are integrable
on the open chart because derivatives of the phase test vanish off its compact support. -/
theorem integrable_coefficients (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ}
    {V : Set Covector} (hψ : ∀ x ∈ V, ContDiffAt ℝ 2 ψ x) (hb : ContDiff ℝ 2 b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ V) :
    IntegrableOn (linear p b ψ) V ∧ IntegrableOn (quadratic p b ψ) V := by
  have hd (x : Covector) : ContinuousAt (phaseDifferential b) x := by
    apply continuousAt_pi.mpr
    intro i
    exact (hb.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply continuousAt_const
  have hz {x : Covector} (hx : x ∉ tsupport b) : phaseDifferential b x = 0 := by
    funext i
    change fderiv ℝ b x (coordinateVector i) = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
  constructor
  · apply DiracActionSupport.integrableOn_of_compact_support hc hs
    · intro x hx
      exact (continuousAt_const.mul
        (continuousAt_contraction (ScalarPhaseCurrent.continuousAt_current p ((hψ x hx).of_le (by norm_num))) (hd x))).continuousWithinAt
    · intro x hx
      simp [linear, hz hx, minkowski]
  · apply DiracActionSupport.integrableOn_of_compact_support hc hs
    · intro x hx
      exact ((continuousAt_const.mul (Complex.continuous_normSq.continuousAt.comp
        (hψ x hx).continuousAt)).mul (continuousAt_contraction (hd x) (hd x))).continuousWithinAt
    · intro x hx
      simp [quadratic, hz hx, minkowski]

/-- Exact integrated finite phase rotation for the physical quadratic action.
Both integrals on the right are genuine compactly supported perturbations. -/
theorem relativeAction_rotate (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ}
    {V : Set Covector} (hV : IsOpen V) (hψ : ∀ x ∈ V, ContDiffAt ℝ 2 ψ x)
    (hb : ContDiff ℝ 2 b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ V) (t : ℝ) :
    relativeAction p ψ (rotate b ψ t) coordinateVector V =
      t * (∫ x in V, linear p b ψ x) + t^2 * (∫ x in V, quadratic p b ψ x) := by
  obtain ⟨hl,hq⟩ := integrable_coefficients p hψ hb hc hs
  unfold relativeAction
  rw [setIntegral_congr_fun (g := fun x => t * linear p b ψ x + t^2 * quadratic p b ψ x)
    hV.measurableSet (fun x hx => relativeDensity_eq p ((hψ x hx).differentiableAt (by norm_num))
      (hb.differentiable (by norm_num) x) t)]
  rw [integral_add (hl.const_mul _) (hq.const_mul _), integral_const_mul, integral_const_mul]

/-- The first variation of the actual KG action under a compact phase rotation
is the integral of −2mℏ times the current paired with the phase-test gradient. -/
theorem hasDerivAt_relativeAction_rotate (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ}
    {V : Set Covector} (hV : IsOpen V) (hψ : ∀ x ∈ V, ContDiffAt ℝ 2 ψ x)
    (hb : ContDiff ℝ 2 b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ V) :
    HasDerivAt (fun t => relativeAction p ψ (rotate b ψ t) coordinateVector V)
      (∫ x in V, -2 * p.m * p.hbar *
        minkowski (ScalarPhaseCurrent.current p ψ x) (phaseDifferential b x)) 0 := by
  simp_rw [relativeAction_rotate p hV hψ hb hc hs]
  have hl := (hasDerivAt_id (0 : ℝ)).mul_const (∫ x in V, linear p b ψ x)
  have hq := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x in V, quadratic p b ψ x)
  simpa [linear, Pi.add_def] using! hl.add hq

end FoliationQM.ScalarNoetherAction
