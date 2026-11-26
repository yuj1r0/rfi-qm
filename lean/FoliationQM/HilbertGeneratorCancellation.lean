module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Remote-generator cancellation on a Hilbert-space domain

For v13 `thm:entanglement_nosignaling` (lines 1297 and 1315–1321),
the derivative of the partial inner product pairs the two appearances of
the remote Hamiltonian with opposite signs. The identity below holds on
its domain, including for unbounded self-adjoint operators. It applies
at each time to the state fiber and its retained spatial derivative when
their strong time derivatives satisfy the two stated evolution equations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.HilbertGeneratorCancellation

open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The remote Schrödinger velocity on the Hamiltonian's own domain. -/
def generator (hbar : ℝ) (H : E →ₗ.[ℂ] E) (u : H.domain) : E :=
  (-Complex.I / (hbar : ℂ)) • H u

/-- A self-adjoint, possibly unbounded, Hamiltonian is symmetric on its domain. -/
theorem formalAdjoint_of_selfAdjoint [CompleteSpace E] {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) : H.IsFormalAdjoint H := by
  have h := H.adjoint_isFormalAdjoint hH.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hH] at h

/-- The remote contribution to the derivative of an arbitrary complex partial
inner product vanishes by symmetry on the two domain vectors. -/
theorem remote_gram_zero (hbar : ℝ) (H : E →ₗ.[ℂ] E) (hsym : H.IsFormalAdjoint H)
    (u v : H.domain) :
    inner ℂ (u : E) (generator hbar H v) + inner ℂ (generator hbar H u) (v : E) = 0 := by
  rw [generator, generator, inner_smul_right, inner_smul_left, hsym u v]
  simp [div_eq_mul_inv, mul_assoc]

/-- If both paths have a common remote Hamiltonian, only the two remaining
velocities contribute to the derivative of their complex pairing. -/
theorem gram_derivative (hbar : ℝ) (H : E →ₗ.[ℂ] E) (hsym : H.IsFormalAdjoint H)
    {u v : ℝ → E} {t : ℝ} {a b : E} (hu : u t ∈ H.domain) (hv : v t ∈ H.domain)
    (hx : HasDerivAt u (a + generator hbar H ⟨u t, hu⟩) t)
    (hy : HasDerivAt v (b + generator hbar H ⟨v t, hv⟩) t) :
    HasDerivAt (fun s => inner ℂ (u s) (v s)) (inner ℂ (u t) b + inner ℂ a (v t)) t := by
  apply (hx.inner ℂ hy).congr_deriv
  have h := remote_gram_zero hbar H hsym ⟨u t, hu⟩ ⟨v t, hv⟩
  simp only [inner_add_left, inner_add_right]
  linear_combination h

/-- The remote velocity contributes zero to the derivative of the fiber Born weight. -/
theorem density_derivative (hbar : ℝ) (H : E →ₗ.[ℂ] E) (hsym : H.IsFormalAdjoint H)
    {u : ℝ → E} {t : ℝ} {a : E} (hu : u t ∈ H.domain)
    (hx : HasDerivAt u (a + generator hbar H ⟨u t, hu⟩) t) :
    HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * (inner ℂ (u t) a).re) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (gram_derivative hbar H hsym hu hu hx hx)
  have he := inner_conj_symm (𝕜 := ℂ) (u t) a
  have hr := congrArg Complex.re he
  simp only [Complex.conj_re] at hr
  have hn (x : E) : (inner ℂ x x).re = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Function.comp_def, Complex.reCLM_apply, hn,
    Complex.add_re, hr, two_mul] using hd

/-- When the second path is the retained spatial derivative, multiplying the
imaginary part by ℏ/m gives the retained current. Its time derivative is
independent of the two common remote-generator terms. -/
theorem current_derivative (hbar m : ℝ) (H : E →ₗ.[ℂ] E) (hsym : H.IsFormalAdjoint H)
    {u v : ℝ → E} {t : ℝ} {a b : E} (hu : u t ∈ H.domain) (hv : v t ∈ H.domain)
    (hx : HasDerivAt u (a + generator hbar H ⟨u t, hu⟩) t)
    (hy : HasDerivAt v (b + generator hbar H ⟨v t, hv⟩) t) :
    HasDerivAt (fun s => (hbar / m) * (inner ℂ (u s) (v s)).im)
      ((hbar / m) * (inner ℂ (u t) b + inner ℂ a (v t)).im) t :=
  (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (gram_derivative hbar H hsym hu hv hx hy)).const_mul _

/-- For a differentiable retained spatial section and its actual directional derivative,
the strong evolution equations on a self-adjoint remote Hamiltonian's domain give
the two physical time derivatives with only the retained velocities on the right. -/
theorem spatial_observable_derivatives [CompleteSpace E] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (hbar m : ℝ) (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (F : ℝ → X → E) (t : ℝ) (x v : X) (d : X →L[ℝ] E) (hd : HasFDerivAt (F t) d x)
    (a b : E) (hu : F t x ∈ H.domain) (hv : d v ∈ H.domain)
    (hx : HasDerivAt (fun s => F s x) (a + generator hbar H ⟨F t x, hu⟩) t)
    (hy : HasDerivAt (fun s => fderiv ℝ (F s) x v) (b + generator hbar H ⟨d v, hv⟩) t) :
    HasDerivAt (fun s => ‖F s x‖ ^ 2) (2 * (inner ℂ (F t x) a).re) t ∧
    HasDerivAt (fun s => (hbar / m) * (inner ℂ (F s x) (fderiv ℝ (F s) x v)).im)
      ((hbar / m) * (inner ℂ (F t x) b + inner ℂ a (d v)).im) t := by
  have hs := formalAdjoint_of_selfAdjoint hH
  refine ⟨density_derivative hbar H hs hu hx, ?_⟩
  have hv' : fderiv ℝ (F t) x v ∈ H.domain := hd.fderiv.symm ▸ hv
  have hy' : HasDerivAt (fun s => fderiv ℝ (F s) x v)
      (b + generator hbar H ⟨fderiv ℝ (F t) x v, hv'⟩) t := by simpa only [hd.fderiv] using hy
  simpa only [hd.fderiv] using current_derivative hbar m H hs hu hv' hx hy'

end FoliationQM.HilbertGeneratorCancellation
