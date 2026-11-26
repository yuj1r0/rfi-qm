module

public import FoliationQM.JointL2Sections
public import FoliationQM.ScalarFiberPairing
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Scalar and Hilbert derivatives of a family of Schwartz fibers

In the marginal current of v13 `thm:entanglement_nosignaling`, the retained
spatial derivative acts on the joint scalar wave before integration over
the remote position. For a family differentiable in the Schwartz topology,
inclusion in remote `L²` and evaluation at a remote point both carry its
derivative to the derivative of the corresponding wave.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SchwartzFiberDerivative

open LorentzCoordinates MeasureTheory JointL2Sections HilbertFiberObservables

/-- Rapidly decreasing smooth complex waves on the remote spatial slice. -/
abbrev Fiber := SchwartzMap Spatial ℂ

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Hilbert-valued wave obtained by taking the remote `L²` class at each position. -/
def hilbertWave (S : X → Fiber) (x : X) : Remote := (S x).toLp 2 volume

/-- Postcomposition with a continuous linear observation carries the derivative
to the derivative of the observed wave in the topological vector space calculus. -/
theorem hasFDerivAt_image {E H : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
    (T : E →L[ℝ] H) {S : X → E} {D : X →L[ℝ] E} {x : X}
    (hS : HasFDerivAt S D x) : HasFDerivAt (fun z => T (S z)) (T.comp D) x := by
  refine .of_isLittleOTVS <| (T.isBigOTVS_comp.trans_isLittleOTVS hS.isLittleOTVS).congr_left ?_
  intro p
  simp

/-- Passing to the Hilbert space differentiates the Schwartz family in its retained argument. -/
theorem hasFDerivAt_hilbertWave (S : X → Fiber) {x : X} (hS : DifferentiableAt ℝ S x) :
    HasFDerivAt (hilbertWave S) ((SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp (fderiv ℝ S x)) x :=
  hasFDerivAt_image (SchwartzMap.toLpCLM ℝ ℂ 2 volume) hS.hasFDerivAt

/-- The Hilbert directional derivative is the class of the corresponding Schwartz derivative. -/
theorem fderiv_hilbertWave (S : X → Fiber) {x : X} (hS : DifferentiableAt ℝ S x) (v : X) :
    fderiv ℝ (hilbertWave S) x v = (fderiv ℝ S x v).toLp 2 volume :=
  congrArg (fun D : X →L[ℝ] Remote => D v) (hasFDerivAt_hilbertWave S hS).fderiv

private def pointValue (y : Spatial) : Fiber →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℝ Spatial ℂ)

/-- At each remote point the scalar spatial derivative is the value of the Schwartz derivative. -/
theorem fderiv_eval (S : X → Fiber) {x : X} (hS : DifferentiableAt ℝ S x) (y : Spatial) (v : X) :
    fderiv ℝ (fun z => S z y) x v = (fderiv ℝ S x v) y :=
  congrArg (fun D : X →L[ℝ] ℂ => D v) (hasFDerivAt_image (pointValue y) hS.hasFDerivAt).fderiv

/-- The actual scalar derivative represents the Hilbert directional derivative almost everywhere. -/
theorem derivative_rep (S : X → Fiber) {x : X} (hS : DifferentiableAt ℝ S x) (v : X) :
    (fderiv ℝ (hilbertWave S) x v : Spatial → ℂ) =ᵐ[volume]
      fun y => fderiv ℝ (fun z => S z y) x v := by
  simp only [fderiv_hilbertWave S hS, fderiv_eval S hS]
  exact (fderiv ℝ S x v).coeFn_toLp 2 volume

/-- The scalar current density in the remote variable is integrable. -/
theorem integrable_current (hbar m : ℝ) (S : X → Fiber) {x : X}
    (hS : DifferentiableAt ℝ S x) (v : X) :
    Integrable (fun y => (hbar / m) * (star (S x y) * fderiv ℝ (fun z => S z y) x v).im) := by
  simp only [fderiv_eval S hS]
  exact ScalarFiberPairing.integrable_current hbar m ((S x).memLp 2 volume)
    ((fderiv ℝ S x v).memLp 2 volume)

/-- The marginal Hilbert current is the scalar current integrated over the full remote slice. -/
theorem current_eq_integral (hbar m : ℝ) (S : X → Fiber) {x : X}
    (hS : DifferentiableAt ℝ S x) (v : X) :
    current hbar m (hilbertWave S) x v =
      (hbar / m) * ∫ y, (star (S x y) * fderiv ℝ (fun z => S z y) x v).im := by
  simp only [fderiv_eval S hS]
  exact ScalarFiberPairing.current_eq_integral hbar m (hilbertWave S) x v
    ((S x).memLp 2 volume) ((fderiv ℝ S x v).memLp 2 volume) rfl (fderiv_hilbertWave S hS v)

end FoliationQM.SchwartzFiberDerivative
