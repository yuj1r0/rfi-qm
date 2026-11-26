module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Marginal density and current from a Hilbert-valued wave

In v13 `thm:entanglement_nosignaling`, the reduced kernel pairs fibers of
the joint wave over the remote subsystem. Its diagonal gives the marginal
Born density. Differentiating its first argument and then taking the diagonal
gives the marginal current. A fixed remote complex linear isometry preserves
these observables for an arbitrary family of fibers.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.HilbertFiberObservables

variable {X H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The reduced kernel with retained ket coordinate `x` and bra coordinate `y`. -/
def kernel (F : X → H) (x y : X) : ℂ := inner ℂ (F y) (F x)

/-- The marginal Born density of a Hilbert-valued wave. -/
def density (F : X → H) (x : X) : ℝ := ‖F x‖ ^ 2

/-- The real part of the diagonal of the reduced kernel is the Born density. -/
theorem kernel_diagonal (F : X → H) (x : X) : (kernel F x x).re = density F x :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) (F x)).symm

/-- An isometry on the remote subsystem preserves each entry of the reduced kernel. -/
theorem kernel_isometry (U : H →ₗᵢ[ℂ] K) (F : X → H) (x y : X) :
    kernel (fun z => U (F z)) x y = kernel F x y :=
  U.inner_map_map (F y) (F x)

/-- A remote isometry preserves marginal density pointwise. -/
theorem density_isometry (U : H →ₗᵢ[ℂ] K) (F : X → H) (x : X) :
    density (fun z => U (F z)) x = density F x := by
  simp [density]

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℝ H]

/-- The marginal current in the retained direction `v`. -/
def current (hbar m : ℝ) (F : X → H) (x v : X) : ℝ :=
  (hbar / m) * (inner ℂ (F x) (fderiv ℝ F x v)).im

/-- The derivative in the ket coordinate pairs the fixed bra with the fiber derivative. -/
theorem kernel_fderiv (F : X → H) {x : X} (hF : DifferentiableAt ℝ F x) (y v : X) :
    fderiv ℝ (fun z => kernel F z y) x v = inner ℂ (F y) (fderiv ℝ F x v) := by
  simpa [kernel] using fderiv_inner_apply ℂ (differentiableAt_const (F y)) hF v

/-- The imaginary part of the ket derivative, restricted to the diagonal, gives the current. -/
theorem current_eq_kernel_derivative (hbar m : ℝ) (F : X → H) {x : X}
    (hF : DifferentiableAt ℝ F x) (v : X) :
    current hbar m F x v = (hbar / m) * (fderiv ℝ (fun z => kernel F z x) x v).im := by
  rw [kernel_fderiv F hF]
  rfl

/-- Differentiating the density gives twice the real part of the directional pairing. -/
theorem density_fderiv (F : X → H) {x : X} (hF : DifferentiableAt ℝ F x) (v : X) :
    fderiv ℝ (density F) x v = 2 * (inner ℂ (F x) (fderiv ℝ F x v)).re := by
  have he : density F = fun z => (inner ℂ (F z) (F z)).re :=
    funext fun z => (kernel_diagonal F z).symm
  have hd := Complex.reCLM.hasFDerivAt.comp x (hF.hasFDerivAt.inner ℂ hF.hasFDerivAt)
  rw [he]
  change fderiv ℝ (Complex.reCLM ∘ fun z => inner ℂ (F z) (F z)) x v = _
  rw [hd.fderiv]
  change (inner ℂ (F x) (fderiv ℝ F x v) + inner ℂ (fderiv ℝ F x v) (F x)).re = _
  rw [Complex.add_re, two_mul]
  exact congrArg (_ + ·) (inner_re_symm (𝕜 := ℂ) (fderiv ℝ F x v) (F x))

variable [NormedSpace ℝ K] [IsScalarTower ℝ ℂ H] [IsScalarTower ℝ ℂ K]

/-- A fixed remote isometry commutes with differentiation in a retained direction. -/
theorem fderiv_isometry (U : H →ₗᵢ[ℂ] K) (F : X → H) {x : X}
    (hF : DifferentiableAt ℝ F x) (v : X) :
    fderiv ℝ (fun z => U (F z)) x v = U (fderiv ℝ F x v) :=
  congrArg (fun D : X →L[ℝ] K => D v)
    (((U.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x hF.hasFDerivAt).fderiv)

/-- A position-independent isometry on the remote subsystem preserves the marginal current. -/
theorem current_isometry (U : H →ₗᵢ[ℂ] K) (hbar m : ℝ) (F : X → H) {x : X}
    (hF : DifferentiableAt ℝ F x) (v : X) :
    current hbar m (fun z => U (F z)) x v = current hbar m F x v := by
  simp only [current, fderiv_isometry U F hF, U.inner_map_map]

end FoliationQM.HilbertFiberObservables
