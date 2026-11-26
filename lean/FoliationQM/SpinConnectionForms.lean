module

public import FoliationQM.MaurerCartanCurvature
public import FoliationQM.LorentzConnectionCurvature
public import FoliationQM.RealLorentzFrame
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Actual scalar spin-connection forms and exterior curvature

Source: v13's spin-connection curvature following `eq:canonical_P_L`.
The coefficient field takes values in actual real continuous-linear maps
on tangent directions. Projection and the continuous alternating one-form
lift construct genuine scalar component forms and the source spin form.
The signed two-form is defined independently from actual products and
alternation, with no exterior-derivative or flatness premise.

The local curvature result uses a C2 matrix field, pointwise invertibility,
and actual local antisymmetric body-generator expansions. It establishes
actual exterior differentiation locally, without a phase-exactness or
global-topology claim.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace FoliationQM.SpinConnectionForms
open DiracMatrices RealLorentzFrame MaurerCartanDifferential CliffordCommutators
open LorentzConnectionCurvature

/-- A real four-by-four array of Lorentz connection coefficients. -/
abbrev Coeff := Fin 4 → Fin 4 → ℝ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real continuous-linear functional lifted to a genuine continuous alternating one-form. -/
def oneFormLift : (E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

/-- Actual evaluation of one real connection coefficient as a continuous-linear map. -/
def coefficientProjection (a b : Fin 4) : Coeff →L[ℝ] ℝ :=
  ({ toFun := fun c => c a b
     map_add' := by intro c d; rfl
     map_smul' := by intro r c; rfl } : Coeff →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- One component of the actual continuous-linear coefficient map on tangent directions. -/
def componentLinear (omega : E →L[ℝ] Coeff) (a b : Fin 4) : E →L[ℝ] ℝ :=
  (coefficientProjection a b).comp omega

/-- One real connection component bundled as a genuine continuous alternating one-form. -/
def componentForm (omega : E →L[ℝ] Coeff) (a b : Fin 4) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  oneFormLift (componentLinear omega a b)

/-- The source scalar spin connection minus hbar over two times the actual 12 component. -/
def spinLinear (hbar : ℝ) (omega : E →L[ℝ] Coeff) : E →L[ℝ] ℝ :=
  (-(hbar/2)) • componentLinear omega 1 2

/-- The scalar spin-connection field as a genuine continuous alternating one-form. -/
def spinForm (hbar : ℝ) (omega : E → (E →L[ℝ] Coeff)) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  oneFormLift (spinLinear hbar (omega x))

/-- The continuous coefficient projection evaluates the actual real array entry. -/
theorem coefficientProjection_apply (c : Coeff) (a b : Fin 4) :
    coefficientProjection a b c = c a b := rfl

/-- The bundled real component functional evaluates the supplied coefficient map. -/
theorem componentLinear_apply (omega : E →L[ℝ] Coeff) (a b : Fin 4) (v : E) :
    componentLinear omega a b v = omega v a b := rfl

/-- The component one-form evaluates its coefficient map on the unique tangent argument. -/
theorem componentForm_apply (omega : E →L[ℝ] Coeff) (a b : Fin 4) (v : Fin 1 → E) :
    componentForm omega a b v = omega (v 0) a b := rfl

/-- The actual spin one-form has the source negative hbar-over-two 12-component value. -/
theorem spinForm_apply (hbar : ℝ) (omega : E → (E →L[ℝ] Coeff)) (x : E) (v : Fin 1 → E) :
    spinForm hbar omega x v = -(hbar/2)*omega x (v 0) 1 2 := rfl

/-- Differentiability of the actual coefficient-map field implies differentiability of every fixed scalar coefficient evaluation. -/
theorem differentiableAt_coefficient {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (v : E) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => omega y v a b) x :=
  (coefficientProjection a b).differentiableAt.comp x
    (homega.clm_apply (differentiableAt_const v))

/-- The actual component functional field is differentiable by continuous-linear coefficient projection. -/
theorem differentiableAt_componentLinear {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => componentLinear (omega y) a b) x :=
  (differentiableAt_const (coefficientProjection a b)).clm_comp homega

/-- The genuine spin one-form field is differentiable wherever the supplied coefficient-map field is differentiable. -/
theorem differentiableAt_spinForm {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (hbar : ℝ) :
    DifferentiableAt ℝ (spinForm hbar omega) x :=
  oneFormLift.differentiableAt.comp x
    ((differentiableAt_componentLinear homega 1 2).const_smul (-(hbar/2)))

/-- The actual scalar wedge of two real continuous-linear functionals, constructed independently by bilinear multiplication and alternation. -/
def scalarWedge (T S : E →L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin (oneFormLift.comp (T.smulRight S))

/-- The independently constructed scalar wedge is the actual alternating product on a pair of tangent vectors. -/
theorem scalarWedge_apply (T S : E →L[ℝ] ℝ) (v : Fin 2 → E) :
    scalarWedge T S v = T (v 0)*S (v 1)-T (v 1)*S (v 0) := by
  simp [scalarWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, oneFormLift, Fin.removeNth, sub_eq_add_neg]

/-- The signed Lorentz-coefficient wedge contraction, constructed independently from the actual component functionals. -/
def coefficientWedgeSquare (omega : E →L[ℝ] Coeff) (a b : Fin 4) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  ∑ c : Fin 4, sign c • scalarWedge (componentLinear omega a c) (componentLinear omega c b)

/-- The genuine coefficient two-form evaluates to the signed alternating product sum over the contracted Lorentz index. -/
theorem coefficientWedgeSquare_apply (omega : E →L[ℝ] Coeff) (a b : Fin 4) (v : Fin 2 → E) :
    coefficientWedgeSquare omega a b v =
      ∑ c : Fin 4, sign c*(omega (v 0) a c*omega (v 1) c b-omega (v 1) a c*omega (v 0) c b) := by
  simp [coefficientWedgeSquare, ContinuousAlternatingMap.sum_apply,
    scalarWedge_apply, componentLinear_apply]

/-- The actual exterior derivative of the spin one-form is the alternating pair of genuine scalar directional derivatives. -/
theorem extDeriv_spinForm_apply {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (hbar : ℝ) (v : Fin 2 → E) :
    extDeriv (spinForm hbar omega) x v =
      fderiv ℝ (fun y => -(hbar/2)*omega y (v 1) 1 2) x (v 0) -
      fderiv ℝ (fun y => -(hbar/2)*omega y (v 0) 1 2) x (v 1) := by
  rw [extDeriv_apply (differentiableAt_spinForm homega hbar)]
  simp [spinForm_apply, Fin.sum_univ_succ, Fin.removeNth, sub_eq_add_neg, add_comm]

/-- Each genuine coefficient one-form field is differentiable under actual coefficient-map differentiability. -/
theorem differentiableAt_componentForm {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => componentForm (omega y) a b) x :=
  oneFormLift.differentiableAt.comp x (differentiableAt_componentLinear homega a b)

/-- The actual exterior derivative of each coefficient one-form is the alternating pair of its actual scalar directional derivatives. -/
theorem extDeriv_componentForm_apply {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (homega : DifferentiableAt ℝ omega x) (a b : Fin 4) (v : Fin 2 → E) :
    extDeriv (fun y => componentForm (omega y) a b) x v =
      fderiv ℝ (fun y => omega y (v 1) a b) x (v 0) -
      fderiv ℝ (fun y => omega y (v 0) a b) x (v 1) := by
  rw [extDeriv_apply (differentiableAt_componentForm homega a b)]
  simp [componentForm_apply, Fin.sum_univ_succ, Fin.removeNth, sub_eq_add_neg]


/-- The independently defined coefficient wedge evaluates to the actual signed Lorentz bracket of the two coefficient arrays. -/
theorem coefficientWedgeSquare_bracket (omega : E →L[ℝ] Coeff) (a b : Fin 4)
    (v : Fin 2 → E) :
    coefficientWedgeSquare omega a b v =
      LorentzGeneratorBracket.bracket (omega (v 0)) (omega (v 1)) a b := by
  rw [coefficientWedgeSquare_apply, LorentzGeneratorBracket.bracket]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Actual local body-generator expansions give the genuine exterior structure equation for every real coefficient one-form. -/
theorem exterior_coefficient_equation {L : E → Mat} {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (homega : DifferentiableAt ℝ omega x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w)) (a b : Fin 4) :
    extDeriv (fun y => componentForm (omega y) a b) x + coefficientWedgeSquare (omega x) a b = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (fun y => componentForm (omega y) a b) x v +
    coefficientWedgeSquare (omega x) a b v = (0 : ℝ)
  rw [extDeriv_componentForm_apply homega, coefficientWedgeSquare_bracket]
  exact coefficient_curvature_apply hL hunit
    (fun w a b => differentiableAt_coefficient homega w a b) hanti hbody (v 0) (v 1) a b

/-- The actual exterior derivative of the source spin form has the positive half-hbar signed alternating coefficient contraction. -/
theorem extDeriv_spinForm_curvature_apply {L : E → Mat} {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (homega : DifferentiableAt ℝ omega x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w))
    (hbar : ℝ) (v : Fin 2 → E) :
    extDeriv (spinForm hbar omega) x v =
      (hbar/2)*(∑ c : Fin 4, sign c*
        (omega x (v 0) 1 c*omega x (v 1) c 2-omega x (v 1) 1 c*omega x (v 0) c 2)) := by
  rw [extDeriv_spinForm_apply homega]
  simpa only [spinConnection] using
    spinConnection_curvature hL hunit
      (fun w a b => differentiableAt_coefficient homega w a b) hanti hbody hbar (v 0) (v 1)

/-- The genuine exterior derivative of the scalar spin connection equals half hbar times its independently constructed signed coefficient wedge. -/
theorem exterior_spin_equation {L : E → Mat} {omega : E → (E →L[ℝ] Coeff)} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x))
    (homega : DifferentiableAt ℝ omega x)
    (hanti : ∀ᶠ y in 𝓝 x, ∀ w a b, omega y w a b = -omega y w b a)
    (hbody : ∀ᶠ y in 𝓝 x, ∀ w, body L y w = generator (omega y w)) (hbar : ℝ) :
    extDeriv (spinForm hbar omega) x = (hbar/2) • coefficientWedgeSquare (omega x) 1 2 := by
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (spinForm hbar omega) x v = (hbar/2)*coefficientWedgeSquare (omega x) 1 2 v
  rw [coefficientWedgeSquare_apply]
  exact extDeriv_spinForm_curvature_apply hL hunit homega hanti hbody hbar v

end FoliationQM.SpinConnectionForms
