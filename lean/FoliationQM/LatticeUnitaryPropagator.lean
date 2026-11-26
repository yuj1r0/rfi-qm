module

public import FoliationQM.LatticeNeumannMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Unitary time evolution of the finite Neumann Hamiltonian

The same-lattice comparison in v13 line 229 uses the exponential of the
time-independent finite-difference Hamiltonian. The Hermitian matrix in
angular-frequency units acts on the complex Euclidean site space. Its
skew-adjoint generator gives a unitary group for all real times.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeUnitaryPropagator

open LatticeNeumannMatrix
open scoped InnerProductSpace

/-- The finite complex Hilbert space of rectangular site samples. -/
abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)

local instance {n : ℕ} : NormedAlgebra ℚ (Space n →L[ℂ] Space n) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- The Neumann frequency matrix acting as a continuous linear map on site profiles. -/
def ham {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) : Space n →L[ℂ] Space n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (frequencyMatrix p h V)

/-- The complex Schrödinger generator in physical time. -/
def generator {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) : Space n →L[ℂ] Space n :=
  (-Complex.I) • ham p h V

/-- Time evolution from time zero of the autonomous Neumann Hamiltonian. -/
def propagator {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) : Space n →L[ℂ] Space n :=
  NormedSpace.exp (t • generator p h V)

/-- Self-adjointness of the frequency operator in the complex site inner product. -/
theorem ham_selfAdjoint {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) :
    IsSelfAdjoint (ham p h V) :=
  IsSelfAdjoint.map Matrix.toEuclideanCLM (frequencyMatrix_isHermitian p h V).isSelfAdjoint

/-- The real-time Schrödinger generator is skew-adjoint. -/
theorem generator_skewAdjoint {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) :
    generator p h V ∈ skewAdjoint (Space n →L[ℂ] Space n) := by
  have hI : -Complex.I ∈ skewAdjoint ℂ := by
    simp [skewAdjoint.mem_iff]
  exact IsSelfAdjoint.smul_mem_skewAdjoint hI (ham_selfAdjoint p h V)

/-- The propagator is unitary at every real time. -/
theorem propagator_unitary {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    propagator p h V t ∈ unitary (Space n →L[ℂ] Space n) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t (generator_skewAdjoint p h V))

/-- Unitary evolution preserves the Euclidean norm of every initial sample vector. -/
theorem propagator_norm {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) (x : Space n) :
    ‖propagator p h V t x‖ = ‖x‖ :=
  (propagator p h V t).norm_map_of_mem_unitary (propagator_unitary p h V t) x

/-- Unitary evolution preserves the entire complex inner product of two samples. -/
theorem propagator_inner {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (t : ℝ) (x y : Space n) :
    ⟪propagator p h V t x, propagator p h V t y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (propagator p h V t).inner_map_map_of_mem_unitary (propagator_unitary p h V t) x y

/-- Propagation over a zero time increment acts by the identity. -/
theorem propagator_zero {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) :
    propagator p h V 0 = 1 := by
  unfold propagator
  have hz : (0 : ℝ) • generator p h V = 0 := zero_smul ℝ (generator p h V)
  rw [hz, NormedSpace.exp_zero]

/-- Propagation over successive time increments composes by addition of the times. -/
theorem propagator_add {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t s : ℝ) :
    propagator p h V (t + s) = propagator p h V t * propagator p h V s := by
  unfold propagator
  rw [add_smul t s (generator p h V)]
  apply NormedSpace.exp_add_of_commute
  change (t • generator p h V) * (s • generator p h V) = (s • generator p h V) * (t • generator p h V)
  ext x
  simp [smul_comm t s]

/-- Evolution forward then backward, or backward then forward, gives the identity. -/
theorem propagator_inverse {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    propagator p h V t * propagator p h V (-t) = 1 ∧
      propagator p h V (-t) * propagator p h V t = 1 := by
  simp only [← propagator_add, add_neg_cancel, neg_add_cancel, propagator_zero, and_self]

/-- The Hamiltonian commutes with its time evolution. -/
theorem ham_commute_propagator {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    Commute (ham p h V) (propagator p h V t) := by
  apply Commute.exp_right
  change ham p h V * (t • ((-Complex.I) • ham p h V)) = (t • ((-Complex.I) • ham p h V)) * ham p h V
  ext x
  simp

/-- Differentiating the propagator in real time places the generator on the left. -/
theorem propagator_deriv_left {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (propagator p h V) (generator p h V * propagator p h V t) t :=
  hasDerivAt_exp_smul_const' (generator p h V) t

/-- The derivative can equally be written with the generator on the right. -/
theorem propagator_deriv_right {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (propagator p h V) (propagator p h V t * generator p h V) t :=
  hasDerivAt_exp_smul_const (generator p h V) t

/-- The propagated state solves the Schrödinger equation at every time. -/
theorem trajectory_deriv {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (t : ℝ) (x : Space n) :
    HasDerivAt (fun s => propagator p h V s x) (generator p h V (propagator p h V t x)) t :=
  ((ContinuousLinearMap.apply ℂ (Space n) x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (propagator_deriv_left p h V t)

open scoped Matrix.Norms.L2Operator

local instance {n : ℕ} : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- The operator propagator is the image of the raw matrix exponential of −itH. -/
theorem matrix_exp_eq_propagator {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (t : ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp (((t : ℂ) * -Complex.I) • frequencyMatrix p h V)) =
      propagator p h V t := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  have hc : Continuous e := e.toAlgEquiv.toLinearEquiv.continuous_of_finiteDimensional
  rw [NormedSpace.map_exp e hc, map_smul, mul_smul]
  rfl

end FoliationQM.LatticeUnitaryPropagator
