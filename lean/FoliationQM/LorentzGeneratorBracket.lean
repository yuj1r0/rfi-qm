module

public import FoliationQM.CliffordCommutators
public import FoliationQM.RealLorentzFrame
public import Mathlib.Analysis.Calculus.FDeriv.Linear
/-!
# Actual Lorentz-generator bracket and differential map

Source: v13 `lem:maurer_cartan` and the structure-equation step of
`thm:dirac_lift`. The coefficients here are the real antisymmetric arrays
paired with the upper-index sigma matrices by the existing ordered
minus-i-over-four generator. The bracket therefore inserts one explicit
Minkowski diagonal sign between the two coefficient arrays.

The matrix commutator identity is proved directly in the actual Dirac
representation: its six-coefficient generator matrix is derived, and all
matrix entries are checked by kernel-verified polynomial identities. No
converse inference from the gamma adjoint action or central ambiguity is
used. The actual continuous real linear generator map also transports
Frechet derivatives of coefficient fields on any real normed domain.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.LorentzGeneratorBracket
open DiracMatrices CliffordCommutators RealLorentzFrame

/-- The real Lorentz coefficient bracket with the explicit signature (+---) contraction. -/
def bracket (omega theta : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ∑c : Fin 4, (omega a c * sign c * theta c b - theta a c * sign c * omega c b)

/-- The signed Lorentz coefficient bracket preserves real antisymmetry. -/
theorem bracket_antisymmetric (omega theta : Fin 4 → Fin 4 → ℝ)
    (hω : ∀a b, omega a b = -omega b a) (hθ : ∀a b, theta a b = -theta b a)
    (a b : Fin 4) : bracket omega theta a b = -bracket omega theta b a := by
  simp only [bracket, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [hω a c, hθ c b, hθ a c, hω c b]
  ring

/-- The actual matrix generator bundled as a continuous real linear map on coefficient arrays. -/
def generatorCLM : (Fin 4 → Fin 4 → ℝ) →L[ℝ] Mat :=
  ({ toFun := generator
     map_add' := by
       intro omega theta
       simp only [generator, Pi.add_apply, Complex.ofReal_add, mul_add, add_div, add_smul,
         Finset.sum_add_distrib]
     map_smul' := by
       intro r omega
       change generator (r • omega) = r • generator omega
       rw [← IsScalarTower.algebraMap_smul ℂ r (generator omega)]
       simp only [generator, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul,
         Complex.ofReal_mul]
       apply Finset.sum_congr rfl
       intro a _
       apply Finset.sum_congr rfl
       intro b _
       congr 1
       change -Complex.I*((r : ℂ)*(omega a b : ℂ))/4 =
         (r : ℂ)*(-Complex.I*(omega a b : ℂ)/4)
       ring } : (Fin 4 → Fin 4 → ℝ) →ₗ[ℝ] Mat).toContinuousLinearMap

/-- The continuous linear generator evaluates to the original ordered sigma-matrix sum. -/
theorem generatorCLM_apply (omega : Fin 4 → Fin 4 → ℝ) : generatorCLM omega = generator omega := rfl

/-- The zero coefficient array has zero actual matrix generator. -/
theorem generator_zero : generator (0 : Fin 4 → Fin 4 → ℝ) = 0 := generatorCLM.map_zero

/-- Addition of real coefficient arrays gives addition of their actual matrix generators. -/
theorem generator_add (omega theta : Fin 4 → Fin 4 → ℝ) :
    generator (omega+theta) = generator omega + generator theta := generatorCLM.map_add omega theta

/-- Subtraction of real coefficient arrays gives subtraction of their actual matrix generators. -/
theorem generator_sub (omega theta : Fin 4 → Fin 4 → ℝ) :
    generator (omega-theta) = generator omega - generator theta := generatorCLM.map_sub omega theta

/-- Real scaling of a coefficient array scales its actual matrix generator. -/
theorem generator_real_smul (r : ℝ) (omega : Fin 4 → Fin 4 → ℝ) :
    generator (r • omega) = r • generator omega := generatorCLM.map_smul r omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine Frechet derivative of a coefficient field composes with the continuous linear generator map. -/
theorem hasFDerivAt_generator_comp {omega : E → Fin 4 → Fin 4 → ℝ}
    {omega' : E →L[ℝ] (Fin 4 → Fin 4 → ℝ)} {x : E}
    (hω : HasFDerivAt omega omega' x) :
    HasFDerivAt (fun y => generator (omega y)) (generatorCLM.comp omega') x := by
  simpa only [Function.comp_def, generatorCLM_apply] using! generatorCLM.hasFDerivAt.comp x hω

/-- The actual directional derivative of the matrix generator is the generator of the actual coefficient derivative. -/
theorem fderiv_generator_comp_apply {omega : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hω : DifferentiableAt ℝ omega x) (v : E) :
    fderiv ℝ (fun y => generator (omega y)) x v = generator (fderiv ℝ omega x v) := by
  rw [(hasFDerivAt_generator_comp hω.hasFDerivAt).fderiv]
  rfl

private theorem antisymmetric_zero {omega : Fin 4 → Fin 4 → ℝ}
    (hω : ∀a b, omega a b = -omega b a) (a : Fin 4) : omega a a = 0 := by
  have h := hω a a
  linarith

set_option maxHeartbeats 5000000 in
private theorem generator_explicit (omega : Fin 4 → Fin 4 → ℝ)
    (hω : ∀a b, omega a b = -omega b a) :
    generator omega =
      !![-Complex.I*(omega 1 2 : ℂ)/2, ((omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2,
          (omega 0 3 : ℂ)/2, ((omega 0 1 : ℂ)-Complex.I*(omega 0 2 : ℂ))/2;
        (-(omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2, Complex.I*(omega 1 2 : ℂ)/2,
          ((omega 0 1 : ℂ)+Complex.I*(omega 0 2 : ℂ))/2, -(omega 0 3 : ℂ)/2;
        (omega 0 3 : ℂ)/2, ((omega 0 1 : ℂ)-Complex.I*(omega 0 2 : ℂ))/2,
          -Complex.I*(omega 1 2 : ℂ)/2, ((omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2;
        ((omega 0 1 : ℂ)+Complex.I*(omega 0 2 : ℂ))/2, -(omega 0 3 : ℂ)/2,
          (-(omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2, Complex.I*(omega 1 2 : ℂ)/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, sigma, gamma, Fin.sum_univ_succ, hω 1 0, hω 2 0, hω 3 0,
      hω 2 1, hω 3 1, hω 3 2] <;> ring_nf <;> norm_num <;> ring

set_option maxHeartbeats 10000000 in
/-- Actual Dirac-matrix generators realize the signed Lorentz bracket for real antisymmetric coefficient arrays. -/
theorem generator_commutator (omega theta : Fin 4 → Fin 4 → ℝ)
    (hω : ∀a b, omega a b = -omega b a) (hθ : ∀a b, theta a b = -theta b a) :
    generator omega * generator theta - generator theta * generator omega =
      generator (bracket omega theta) := by
  rw [generator_explicit omega hω, generator_explicit theta hθ,
    generator_explicit (bracket omega theta) (bracket_antisymmetric omega theta hω hθ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bracket, sign, Fin.sum_univ_succ, antisymmetric_zero hω, antisymmetric_zero hθ,
      hω 1 0, hω 2 0, hω 2 1, hω 3 1, hω 3 2,
      hθ 1 0, hθ 2 0, hθ 2 1, hθ 3 1, hθ 3 2] <;>
    ring_nf <;> norm_num <;> ring

end FoliationQM.LorentzGeneratorBracket
