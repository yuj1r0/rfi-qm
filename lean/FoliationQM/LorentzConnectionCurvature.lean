module

public import FoliationQM.LorentzCoefficientUniqueness
public import FoliationQM.MaurerCartanDifferential
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import FoliationQM.MaurerCartanCurvature
public import FoliationQM.LorentzGeneratorBracket

/-!
# Actual Lorentz coefficient and spin-connection curvature

Source: the Maurer--Cartan structure equation and spin-frame curvature in
v13 `thm:dirac_lift`, immediately after `eq:canonical_P_L` and in its proof.
The body connection is the actual inverse-matrix product with the actual
Frechet derivative of a locally C2 matrix field. Its real coefficient
expansion and antisymmetry are supplied locally; scalar coefficient fields
are genuinely differentiable. Antisymmetry of their derivatives follows by
differentiating the local equality.

The coefficient curvature equation is derived from the actual matrix
Maurer--Cartan equation, the proved generator commutator and uniqueness of
real antisymmetric coefficients. No flatness relation is a premise. The
source spin connection is the actual scalar field -(hbar/2) omega_12, whose
alternating directional derivative has the explicit signed coefficient
contraction. Exterior-form packaging and local exactness are separate results.
-/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.LorentzConnectionCurvature
open DiracMatrices MaurerCartanDifferential CliffordCommutators
open LorentzGeneratorBracket LorentzCoefficientUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Frechet derivative in the first direction of the coefficient field evaluated in the fixed second direction. -/
def coefficientDerivative (omega : E → E → Fin 4 → Fin 4 → ℝ) (x v w : E) :
    Fin 4 → Fin 4 → ℝ := fderiv ℝ (fun y => omega y w) x v

/-- The source scalar spin-frame connection evaluated on a direction, with its negative half-hbar coefficient. -/
def spinConnection (hbar : ℝ) (omega : E → E → Fin 4 → Fin 4 → ℝ) (y v : E) : ℝ :=
  -(hbar/2) * omega y v 1 2

private theorem coefficients_differentiableAt {omega : E → E → Fin 4 → Fin 4 → ℝ}
    {x : E} (w : E) (hcoeff : ∀ a b, DifferentiableAt ℝ (fun y => omega y w a b) x) :
    DifferentiableAt ℝ (fun y => omega y w) x :=
  differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr (hcoeff a)

/-- Evaluating the actual coefficient-array derivative gives the actual derivative of the corresponding scalar component. -/
theorem coefficientDerivative_apply {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E}
    (v w : E) (hcoeff : ∀ a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (a b : Fin 4) :
    coefficientDerivative omega x v w a b = fderiv ℝ (fun y => omega y w a b) x v := by
  symm
  rw [fderiv_apply (differentiableAt_pi.mpr (hcoeff a)) b,
    fderiv_apply (coefficients_differentiableAt w hcoeff) a]
  rfl

/-- Local antisymmetry of differentiable coefficient fields yields antisymmetry of their actual directional derivative arrays. -/
theorem coefficientDerivative_antisymmetric {omega : E → E → Fin 4 → Fin 4 → ℝ}
    {x : E} (v w : E)
    (hcoeff : ∀ a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ a b, omega y w a b = -omega y w b a) (a b : Fin 4) :
    coefficientDerivative omega x v w a b = -coefficientDerivative omega x v w b a := by
  rw [coefficientDerivative_apply v w hcoeff a b, coefficientDerivative_apply v w hcoeff b a]
  have heq : (fun y => omega y w a b) =ᶠ[𝓝 x] (fun y => -omega y w b a) :=
    hanti.mono fun _ h => h a b
  have he := congrArg (fun T : E →L[ℝ] ℝ => T v) heq.fderiv_eq
  have hn : HasFDerivAt (fun y => -omega y w b a)
      (-fderiv ℝ (fun y => omega y w b a) x) x := (hcoeff b a).hasFDerivAt.neg
  rw [hn.fderiv] at he
  simpa only [neg_apply] using he

/-- The actual scalar spin-connection derivative has the negative half-hbar factor multiplying the actual 12 coefficient derivative. -/
theorem fderiv_spinConnection_apply {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hbar : ℝ) (v w : E) (hcoeff : DifferentiableAt ℝ (fun y => omega y w 1 2) x) :
    fderiv ℝ (fun y => spinConnection hbar omega y w) x v =
      -(hbar/2) * fderiv ℝ (fun y => omega y w 1 2) x v := by
  have hd := congrArg (fun T : E →L[ℝ] ℝ => T v)
    (hcoeff.hasFDerivAt.const_mul (-(hbar/2))).fderiv
  simpa only [spinConnection, _root_.smul_apply, smul_eq_mul] using hd

/-- A local actual body-generator expansion differentiates through the continuous real generator map. -/
theorem fderiv_body_coefficients {L : E → Mat}
    {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E} (v w : E)
    (hcoeff : ∀ a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (hbody : ∀ᶠ y in 𝓝 x, body L y w = generator (omega y w)) :
    fderiv ℝ (fun y => body L y w) x v = generator (coefficientDerivative omega x v w) := by
  have heq : (fun y => body L y w) =ᶠ[𝓝 x] (fun y => generator (omega y w)) := hbody
  have he := congrArg (fun T : E →L[ℝ] Mat => T v) heq.fderiv_eq
  exact he.trans (fderiv_generator_comp_apply (coefficients_differentiableAt w hcoeff) v)

/-- Actual C2 matrix Maurer--Cartan curvature and coefficient uniqueness derive the vanishing real antisymmetric coefficient curvature. -/
theorem coefficient_curvature {L : E → Mat}
    {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (hcoeff : ∀ w a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w)) (v w : E) :
    coefficientDerivative omega x v w - coefficientDerivative omega x w v +
      bracket (omega x v) (omega x w) = 0 := by
  have hv := hanti.self_of_nhds v
  have hw := hanti.self_of_nhds w
  have hcurv := MaurerCartanCurvature.body_curvature hL hunit v w
  rw [fderiv_body_coefficients v w (hcoeff w) (hbody.mono fun _ h => h w),
    fderiv_body_coefficients w v (hcoeff v) (hbody.mono fun _ h => h v),
    hbody.self_of_nhds v, hbody.self_of_nhds w] at hcurv
  have hgen : generator (coefficientDerivative omega x v w - coefficientDerivative omega x w v +
      bracket (omega x v) (omega x w)) = 0 := by
    change generatorCLM (coefficientDerivative omega x v w - coefficientDerivative omega x w v +
      bracket (omega x v) (omega x w)) = 0
    rw [map_add, map_sub]
    simp only [generatorCLM_apply]
    rw [← generator_commutator (omega x v) (omega x w) hv hw]
    simpa only [sub_eq_add_neg, add_assoc] using hcurv
  have hantider : ∀ a b,
      (coefficientDerivative omega x v w - coefficientDerivative omega x w v +
        bracket (omega x v) (omega x w)) a b =
      -(coefficientDerivative omega x v w - coefficientDerivative omega x w v +
        bracket (omega x v) (omega x w)) b a := by
    intro a b
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [coefficientDerivative_antisymmetric v w (hcoeff w) (hanti.mono fun _ h => h w) a b,
      coefficientDerivative_antisymmetric w v (hcoeff v) (hanti.mono fun _ h => h v) a b,
      bracket_antisymmetric (omega x v) (omega x w) hv hw a b]
    ring
  exact (generator_eq_zero_iff _ hantider).mp hgen

/-- Each scalar component satisfies the actual directional coefficient structure equation with the signed Lorentz bracket. -/
theorem coefficient_curvature_apply {L : E → Mat}
    {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (hcoeff : ∀ w a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w))
    (v w : E) (a b : Fin 4) :
    fderiv ℝ (fun y => omega y w a b) x v - fderiv ℝ (fun y => omega y v a b) x w +
      bracket (omega x v) (omega x w) a b = 0 := by
  have h := congrFun (congrFun (coefficient_curvature hL hunit hcoeff hanti hbody v w) a) b
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    coefficientDerivative_apply v w (hcoeff w), coefficientDerivative_apply w v (hcoeff v)] using h

/-- The actual alternating directional derivative of the spin-frame connection is the source half-hbar signed Lorentz contraction. -/
theorem spinConnection_curvature {L : E → Mat}
    {omega : E → E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (hcoeff : ∀ w a b, DifferentiableAt ℝ (fun y => omega y w a b) x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w))
    (hbar : ℝ) (v w : E) :
    fderiv ℝ (fun y => spinConnection hbar omega y w) x v -
      fderiv ℝ (fun y => spinConnection hbar omega y v) x w =
      (hbar/2) * ∑ c, RealLorentzFrame.sign c *
        (omega x v 1 c * omega x w c 2 - omega x w 1 c * omega x v c 2) := by
  have hc := coefficient_curvature_apply hL hunit hcoeff hanti hbody v w 1 2
  have hb : bracket (omega x v) (omega x w) 1 2 =
      ∑ c, RealLorentzFrame.sign c *
        (omega x v 1 c * omega x w c 2 - omega x w 1 c * omega x v c 2) := by
    unfold bracket
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hb] at hc
  rw [fderiv_spinConnection_apply hbar v w (hcoeff w 1 2),
    fderiv_spinConnection_apply hbar w v (hcoeff v 1 2)]
  linear_combination -(hbar/2) * hc

end FoliationQM.LorentzConnectionCurvature
