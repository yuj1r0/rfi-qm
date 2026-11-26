module

public import FoliationQM.PolarSpinorBilinears
public import FoliationQM.MatrixDifferential
public import FoliationQM.ChiralDifferential
public import FoliationQM.MaurerCartanDifferential

/-!
# Actual Frechet derivatives of the polar spinor field

Source: v13 `eq:d_psi_polar_main` and `eq:d_psibar_polar_main` in
`lem:maurer_cartan`. The field is the actual polar matrix ansatz. Its
continuous-linear derivative is obtained from the square-root, chiral and
matrix product rules. The positive-density condition is pointwise, and
structural conditions on the matrix field are explicitly local.

No supplied first-order jet or asserted polar-derivative identity replaces
actual differentiation. The matrix connection is the actual spatial
Maurer--Cartan derivative; identifying its Lorentz-generator coefficients
and constructing a general spin-bundle field are separate tasks.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PolarSpinorDifferential
open DiracMatrices DiracAdjoint ChiralMatrix MatrixDifferential ChiralDifferential Matrix
open MaurerCartanDifferential

variable {E : Type*}

/-- The actual polar spinor field obtained by evaluating its three parameter fields. -/
def polarField (rho beta : E → ℝ) (L : E → Mat) (x : E) : Spinor :=
  PolarSpinorBilinears.polarSpinor (rho x) (beta x) (L x)

/-- The actual polar field is a real square-root amplitude times a matrix action. -/
theorem polarField_eq_real_smul (rho beta : E → ℝ) (L : E → Mat) (x : E) :
    polarField rho beta L x =
      Real.sqrt (rho x) • ((chiral (beta x)*L x).mulVec restSpinor) := by
  ext i
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous-linear Leibniz derivative built from the actual three factor derivatives. -/
def polarDerivative (r b : ℝ) (M : Mat) (r' b' : E →L[ℝ] ℝ)
    (M' : E →L[ℝ] Mat) : E →L[ℝ] Spinor :=
  Real.sqrt r • (mulVecCLM restSpinor).comp
    (((ContinuousLinearMap.mul ℝ Mat) (chiral b)).comp M' +
      ((ContinuousLinearMap.mul ℝ Mat).flip M).comp
        (b'.smulRight ((Complex.I/2 : ℂ) • (gamma5*chiral b)))) +
    ((1/(2*Real.sqrt r)) • r').smulRight ((chiral b*M).mulVec restSpinor)

/-- The actual Frechet derivative of the polar field is its full continuous-linear Leibniz map. -/
theorem hasFDerivAt_polarField {rho beta : E → ℝ} {L : E → Mat}
    {rho' beta' : E →L[ℝ] ℝ} {L' : E →L[ℝ] Mat} {x : E}
    (hrho : HasFDerivAt rho rho' x) (hbeta : HasFDerivAt beta beta' x)
    (hL : HasFDerivAt L L' x) (hpos : 0 < rho x) :
    HasFDerivAt (polarField rho beta L)
      (polarDerivative (rho x) (beta x) (L x) rho' beta' L') x := by
  have hC := hasFDerivAt_chiral_comp hbeta
  have hM := hC.mul' hL
  have hV := hasFDerivAt_mulVec_const_field hM restSpinor
  have h := (hasFDerivAt_sqrt hrho hpos).smul hV
  convert! h using 1

/-- Actual differentiability of all three fields and positive density imply differentiability of the polar spinor. -/
theorem differentiableAt_polarField {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) :
    DifferentiableAt ℝ (polarField rho beta L) x :=
  (hasFDerivAt_polarField hrho.hasFDerivAt hbeta.hasFDerivAt hL.hasFDerivAt hpos).differentiableAt

/-- The actual Frechet derivative equals the Leibniz map with the genuine parameter-field derivatives. -/
theorem fderiv_polarField {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) :
    fderiv ℝ (polarField rho beta L) x =
      polarDerivative (rho x) (beta x) (L x)
        (fderiv ℝ rho x) (fderiv ℝ beta x) (fderiv ℝ L x) :=
  (hasFDerivAt_polarField hrho.hasFDerivAt hbeta.hasFDerivAt hL.hasFDerivAt hpos).fderiv

/-- Every directional evaluation of the full Leibniz map has the three differentiated polar factors. -/
theorem polarDerivative_apply (r b : ℝ) (M : Mat) (r' b' : E →L[ℝ] ℝ)
    (M' : E →L[ℝ] Mat) (v : E) :
    polarDerivative r b M r' b' M' v =
      Real.sqrt r • ((chiral b*M' v +
        (Complex.I*(b' v : ℂ)/2) • (gamma5*chiral b*M)).mulVec restSpinor) +
      (r' v/(2*Real.sqrt r)) • ((chiral b*M).mulVec restSpinor) := by
  change Real.sqrt r • ((chiral b*M' v +
    (b' v • ((Complex.I/2 : ℂ) • (gamma5*chiral b)))*M).mulVec restSpinor) +
    ((1/(2*Real.sqrt r))*r' v) • ((chiral b*M).mulVec restSpinor) = _
  have hc : b' v • ((Complex.I/2 : ℂ) • (gamma5*chiral b)) =
      (Complex.I*(b' v : ℂ)/2) • (gamma5*chiral b) := by
    rw [← IsScalarTower.algebraMap_smul ℂ (b' v)
      ((Complex.I/2 : ℂ) • (gamma5*chiral b)), smul_smul]
    congr 1
    change (b' v : ℂ)*(Complex.I/2)=_
    ring
  rw [hc, smul_mul_assoc]
  congr 1
  congr 1
  ring

/-- The actual directional Frechet derivative has the unfactored amplitude, chiral and matrix product terms. -/
theorem fderiv_polarField_apply {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (v : E) :
    fderiv ℝ (polarField rho beta L) x v =
      Real.sqrt (rho x) • ((chiral (beta x)*fderiv ℝ L x v +
        (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • (gamma5*chiral (beta x)*L x)).mulVec restSpinor) +
      (fderiv ℝ rho x v/(2*Real.sqrt (rho x))) • ((chiral (beta x)*L x).mulVec restSpinor) := by
  rw [fderiv_polarField hrho hbeta hL hpos, polarDerivative_apply]


/-- The source matrix connection as a real continuous-linear map of the tangent direction, using actual logarithmic, chiral and spatial derivatives. -/
def polarConnection (rho beta : E → ℝ) (L : E → Mat) (x : E) : E →L[ℝ] Mat :=
  let amplitude : E →L[ℝ] Mat :=
    ((1/2 : ℝ) • fderiv ℝ (fun y => Real.log (rho y)) x).smulRight (1 : Mat)
  let angle : E →L[ℝ] Mat :=
    (fderiv ℝ beta x).smulRight ((Complex.I/2 : ℂ) • gamma5)
  let connection : E →L[ℝ] Mat :=
    ((ContinuousLinearMap.mul ℝ Mat).flip ((L x)⁻¹)).comp (fderiv ℝ L x)
  amplitude + angle + connection

private theorem real_smul_I_half (d : ℝ) (A : Mat) :
    d • ((Complex.I/2 : ℂ) • A) = (Complex.I*(d : ℂ)/2) • A := by
  rw [← IsScalarTower.algebraMap_smul ℂ d ((Complex.I/2 : ℂ) • A), smul_smul]
  congr 1
  change (d : ℂ)*(Complex.I/2)=_
  ring

/-- Each evaluation of the continuous-linear polar connection has the actual source half-logarithmic, chiral and spatial coefficients. -/
theorem polarConnection_apply (rho beta : E → ℝ) (L : E → Mat) (x v : E) :
    polarConnection rho beta L x v =
      ((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
      (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 + spatial L x v := by
  change ((1/2 : ℝ)*fderiv ℝ (fun y => Real.log (rho y)) x v) • (1 : Mat) +
      (fderiv ℝ beta x v) • ((Complex.I/2 : ℂ) • gamma5) +
      fderiv ℝ L x v*(L x)⁻¹ = _
  rw [real_smul_I_half]
  congr 2
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

private theorem commute_chiral {K : Mat} (hK : Commute K gamma5) (b : ℝ) :
    Commute K (chiral b) := by
  change K*chiral b=chiral b*K
  simp only [chiral, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hK.eq]

private theorem factor_polar_action (s a : ℝ) (b : ℂ) (C M K D : Mat)
    (hk : K*(C*M)=C*D) (psi : Spinor) :
    s • ((C*D+b • (gamma5*C*M)).mulVec psi) + (a*s) • ((C*M).mulVec psi) =
      ((a : ℂ) • (1 : Mat) + b • gamma5 + K).mulVec (s • ((C*M).mulVec psi)) := by
  have hm : ((a : ℂ) • (1 : Mat)+b • gamma5+K)*(C*M) =
      (a : ℂ) • (C*M)+b • (gamma5*C*M)+C*D := by
    simp only [add_mul, smul_mul_assoc, one_mul, hk, mul_assoc]
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, smul_add]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The actual directional derivative factors through the source matrix connection, derived from local gamma5 commutation and actual inverse cancellation. -/
theorem fderiv_polarField_factored_apply {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) (v : E) :
    fderiv ℝ (polarField rho beta L) x v =
      (polarConnection rho beta L x v).mulVec (polarField rho beta L x) := by
  have hcomm := commute_chiral (spatial_commute_gamma5 hL hunit h5 v) (beta x)
  have hk : spatial L x v*(chiral (beta x)*L x) = chiral (beta x)*fderiv ℝ L x v := by
    rw [← mul_assoc, hcomm.eq, mul_assoc, spatial_mul hunit]
  rw [fderiv_polarField_apply hrho hbeta hL hpos, polarConnection_apply,
    polarField_eq_real_smul, ← fderiv_sqrt_apply hrho hpos v,
    fderiv_sqrt_eq_half_log_mul hrho hpos v]
  exact factor_polar_action _ _ _ _ _ _ _ hk restSpinor

/-- The entire actual Frechet derivative is the continuous-linear polar connection acting on the actual spinor value. -/
theorem fderiv_polarField_factored {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) :
    fderiv ℝ (polarField rho beta L) x =
      (mulVecCLM (polarField rho beta L x)).comp (polarConnection rho beta L x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact fderiv_polarField_factored_apply hrho hbeta hL hpos hunit h5 v

/-- The source factored continuous-linear map is an actual Frechet derivative, not merely a directional jet identity. -/
theorem hasFDerivAt_polarField_factored {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) :
    HasFDerivAt (polarField rho beta L)
      ((mulVecCLM (polarField rho beta L x)).comp (polarConnection rho beta L x)) x := by
  rw [← fderiv_polarField_factored hrho hbeta hL hpos hunit h5]
  exact (differentiableAt_polarField hrho hbeta hL hpos).hasFDerivAt

/-- The actual spinor directional derivative has the explicit source half-log, positive chiral and positive spatial-connection coefficients. -/
theorem fderiv_polarField_source {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) (v : E) :
    fderiv ℝ (polarField rho beta L) x v =
      (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
      (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 + spatial L x v).mulVec
        (polarField rho beta L x) := by
  rw [fderiv_polarField_factored_apply hrho hbeta hL hpos hunit h5,
    polarConnection_apply]

/-- The actual polar spinor-adjoint row field. -/
def adjointField (rho beta : E → ℝ) (L : E → Mat) (x : E) : Spinor :=
  spinorAdjoint (polarField rho beta L x)

/-- Actual real continuous-linearity of the spinor adjoint differentiates the full polar row field. -/
theorem hasFDerivAt_adjointField {rho beta : E → ℝ} {L : E → Mat}
    {rho' beta' : E →L[ℝ] ℝ} {L' : E →L[ℝ] Mat} {x : E}
    (hrho : HasFDerivAt rho rho' x) (hbeta : HasFDerivAt beta beta' x)
    (hL : HasFDerivAt L L' x) (hpos : 0 < rho x) :
    HasFDerivAt (adjointField rho beta L)
      (spinorAdjointCLM.comp (polarDerivative (rho x) (beta x) (L x) rho' beta' L')) x :=
  hasFDerivAt_spinorAdjoint_field (hasFDerivAt_polarField hrho hbeta hL hpos)

/-- The full actual Frechet derivative of the polar adjoint row is the real adjoint map composed with the spinor Leibniz derivative. -/
theorem fderiv_adjointField {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) :
    fderiv ℝ (adjointField rho beta L) x =
      spinorAdjointCLM.comp (polarDerivative (rho x) (beta x) (L x)
        (fderiv ℝ rho x) (fderiv ℝ beta x) (fderiv ℝ L x)) :=
  (hasFDerivAt_adjointField hrho.hasFDerivAt hbeta.hasFDerivAt hL.hasFDerivAt hpos).fderiv

private theorem diracAdjoint_source_matrix (a b : ℝ) (K : Mat)
    (hK : diracAdjoint K = -K) :
    diracAdjoint (((a : ℂ) • (1 : Mat)) + (Complex.I*(b : ℂ)/2) • gamma5 + K) =
      (a : ℂ) • (1 : Mat)+(Complex.I*(b : ℂ)/2) • gamma5-K := by
  simp only [diracAdjoint_add, diracAdjoint_smul, diracAdjoint_one,
    diracAdjoint_gamma5, hK, star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, smul_neg, sub_eq_add_neg]
  module

/-- The actual derivative of the polar Dirac-adjoint row has the same half-log and chiral signs and the opposite spatial-connection sign. -/
theorem fderiv_adjointField_source {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1) (v : E) :
    fderiv ℝ (adjointField rho beta L) x v =
      Matrix.vecMul (adjointField rho beta L x)
        (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I*(fderiv ℝ beta x v : ℂ)/2) • gamma5 - spatial L x v) := by
  change fderiv ℝ (fun y => spinorAdjoint (polarField rho beta L y)) x v = _
  rw [fderiv_spinorAdjoint_apply (differentiableAt_polarField hrho hbeta hL hpos),
    fderiv_polarField_source hrho hbeta hL hpos hunit h5,
    spinorAdjoint_mulVec, diracAdjoint_source_matrix _ _ _ (spatial_diracAdjoint hL hunit hiso v)]
  rfl

end FoliationQM.PolarSpinorDifferential
