module

public import FoliationQM.CurvedFluxGreen

/-!
# Amplitude variation of the tidal quadratic functional

Source: v13 `thm:tidal_dispersion` (Conjecture 9.7) and `eq:tidal_KG_eq`, the
variation of `eq:tidal_lagrangian_thm`, component kinds B and C. For a
symmetric coefficient field `T^{ij}` (in the source `κ √(-g) B^{ij}` with the
external velocity held fixed) the tidal density of an amplitude `R` is
`T^{ij} ∂_i R ∂_j R`. Along an affine amplitude variation `R + t a` with
compactly supported `a`, the density is an exact quadratic polynomial in `t`,
so the relative functional is differentiable at `t = 0` with derivative
`2 ∫ T^{ij} ∂_i R ∂_j a`, and integration by parts turns this into
`-2 ∫ a ∂_j(T^{ij} ∂_i R)`.

The background functional itself need not be integrable; only the difference
from it is integrated. The variation is in the amplitude alone. Nothing here
supports the physical ansatz of the conjecture or extends through zeros of
the field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalAmplitudeVariation

open MeasureTheory Set Matrix LorentzMatrixGroup RNCCoordinateConnection RealLorentzFrame
open scoped Topology

variable {T : Covector → Mat4} {R a : Covector → ℝ} {U : Set Covector} {x : Covector}

/-- The coordinate components of the differential of an amplitude. -/
def grad (R : Covector → ℝ) (x : Covector) : Fin 4 → ℝ := fun i => fderiv ℝ R x (axis i)

/-- The tidal density `T^{ij} ∂_i R ∂_j R`. -/
def tidalDensity (T : Covector → Mat4) (R : Covector → ℝ) (x : Covector) : ℝ :=
  grad R x ⬝ᵥ (T x *ᵥ grad R x)

/-- The tidal flux `T^{ji} ∂_i R`. -/
def tidalFlux (T : Covector → Mat4) (R : Covector → ℝ) (x : Covector) : Fin 4 → ℝ :=
  T x *ᵥ grad R x

/-- The first-order term `2 T^{ij} ∂_i R ∂_j a` of the density along `R + t a`. -/
def tidalCross (T : Covector → Mat4) (R a : Covector → ℝ) (x : Covector) : ℝ :=
  2 * (tidalFlux T R x ⬝ᵥ grad a x)

/-- The coordinate divergence `∂_j(T^{ji} ∂_i R)` of the tidal flux. -/
def tidalDivergence (T : Covector → Mat4) (R : Covector → ℝ) (x : Covector) : ℝ :=
  ∑ j, fderiv ℝ (fun y => tidalFlux T R y j) x (axis j)

/-- The differential of an affine amplitude variation. -/
theorem grad_add_mul (hR : DifferentiableAt ℝ R x) (ha : DifferentiableAt ℝ a x) (t : ℝ) :
    grad (fun y => R y + t * a y) x = grad R x + t • grad a x := by
  funext i
  simp only [grad, fderiv_fun_add hR (ha.const_mul t), fderiv_const_mul ha, _root_.add_apply,
    _root_.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Along an affine amplitude variation the tidal density is an exact
quadratic polynomial in the parameter. -/
theorem tidalDensity_add_mul (hsym : (T x).IsSymm) (hR : DifferentiableAt ℝ R x)
    (ha : DifferentiableAt ℝ a x) (t : ℝ) :
    tidalDensity T (fun y => R y + t * a y) x =
      tidalDensity T R x + t * tidalCross T R a x + t ^ 2 * tidalDensity T a x := by
  have h1 : grad R x ⬝ᵥ (T x *ᵥ grad a x) = (T x *ᵥ grad R x) ⬝ᵥ grad a x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym.eq]
  have h2 : grad a x ⬝ᵥ (T x *ᵥ grad R x) = (T x *ᵥ grad R x) ⬝ᵥ grad a x :=
    dotProduct_comm _ _
  simp only [tidalDensity, tidalCross, tidalFlux, grad_add_mul hR ha, mulVec_add, mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination t * h1 + t * h2

/-- The relative tidal functional is differentiable along an affine compactly
supported amplitude variation, with derivative the integral of the cross term. -/
theorem hasDerivAt_relative (hsym : ∀ x ∈ U, (T x).IsSymm)
    (hT : ∀ i j, ContinuousOn (fun y => T y i j) U)
    (hR : ∀ x ∈ U, ContDiffAt ℝ 1 R x) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    Integrable (tidalCross T R a) ∧
    HasDerivAt (fun t : ℝ => ∫ x,
        (tidalDensity T (fun y => R y + t * a y) x - tidalDensity T R x))
      (∫ x, tidalCross T R a x) 0 := by
  have hK : IsCompact (tsupport a) := hc
  have hgrad0 : ∀ x, x ∉ tsupport a → grad a x = 0 := fun x hx => by
    funext i
    simp [grad, fderiv_of_notMem_tsupport ℝ hx]
  have hcross0 : ∀ x, x ∉ tsupport a → tidalCross T R a x = 0 := fun x hx => by
    simp [tidalCross, hgrad0 x hx]
  have hdens0 : ∀ x, x ∉ tsupport a → tidalDensity T a x = 0 := fun x hx => by
    simp [tidalDensity, hgrad0 x hx]
  have hrel : ∀ (t : ℝ) (x : Covector),
      tidalDensity T (fun y => R y + t * a y) x - tidalDensity T R x =
        t * tidalCross T R a x + t ^ 2 * tidalDensity T a x := by
    intro t x
    by_cases hx : x ∈ tsupport a
    · rw [tidalDensity_add_mul (hsym x (hs hx)) ((hR x (hs hx)).differentiableAt one_ne_zero)
        (ha.differentiable one_ne_zero x) t]
      ring
    · have he : (fun y => R y + t * a y) =ᶠ[𝓝 x] R :=
        (notMem_tsupport_iff_eventuallyEq.mp hx).mono fun y hy => by simp [hy]
      have hg : grad (fun y => R y + t * a y) x = grad R x := by
        funext i
        simp only [grad, he.fderiv_eq]
      rw [hcross0 x hx, hdens0 x hx]
      simp [tidalDensity, hg]
  have hgR (i : Fin 4) : ContinuousOn (fun y => grad R y i) (tsupport a) := fun x hx =>
    (((hR x (hs hx)).fderiv_right (m := 0) le_rfl).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hga (i : Fin 4) : Continuous (fun y => grad a y i) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcrossc : ContinuousOn (tidalCross T R a) (tsupport a) := by
    have hf : tidalCross T R a = fun y =>
        2 * ∑ j, (∑ i, T y j i * grad R y i) * grad a y j := by
      funext y
      simp [tidalCross, tidalFlux, mulVec, dotProduct]
    rw [hf]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun j _ =>
      (continuousOn_finsetSum _ fun i _ => ((hT j i).mono hs).mul (hgR i)).mul
        (hga j).continuousOn)
  have hdensc : ContinuousOn (tidalDensity T a) (tsupport a) := by
    have hf : tidalDensity T a = fun y => ∑ j, grad a y j * ∑ i, T y j i * grad a y i := by
      funext y
      simp [tidalDensity, mulVec, dotProduct]
    rw [hf]
    exact continuousOn_finsetSum _ fun j _ => (hga j).continuousOn.mul
      (continuousOn_finsetSum _ fun i _ => ((hT j i).mono hs).mul (hga i).continuousOn)
  have hic : Integrable (tidalCross T R a) :=
    (hcrossc.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero hcross0
  have hid : Integrable (tidalDensity T a) :=
    (hdensc.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero hdens0
  refine ⟨hic, ?_⟩
  have hfun : (fun t : ℝ => ∫ x,
      (tidalDensity T (fun y => R y + t * a y) x - tidalDensity T R x)) = fun t : ℝ =>
      t * (∫ x, tidalCross T R a x) + t ^ 2 * ∫ x, tidalDensity T a x := by
    funext t
    simp only [hrel]
    rw [integral_add (hic.const_mul t) (hid.const_mul (t ^ 2)), integral_const_mul,
      integral_const_mul]
  rw [hfun]
  have h := (hasDerivAt_mul_const (∫ x, tidalCross T R a x) (x := (0 : ℝ))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, tidalDensity T a x))
  exact h.congr_deriv (by simp)

/-- Integration by parts: the integrated cross term is minus twice the pairing
of the variation with the divergence of the tidal flux. -/
theorem integral_cross_eq (hT : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => T y i j) x)
    (hR : ∀ x ∈ U, ContDiffAt ℝ 2 R x) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    (∫ x, tidalCross T R a x) = -2 * ∫ x, a x * tidalDivergence T R x := by
  have hq (j : Fin 4) : ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => tidalFlux T R y j) x := by
    intro x hx
    have hf : (fun y => tidalFlux T R y j) = fun y =>
        ∑ i, T y j i * fderiv ℝ R y (axis i) := by
      funext y
      simp [tidalFlux, mulVec, dotProduct, grad]
    rw [hf]
    exact ContDiffAt.sum fun i _ => (hT j i x hx).mul
      (((hR x hx).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have G (j : Fin 4) := CurvedFluxGreen.direction_green (K := ℝ) ha hc hs (hq j) (axis j)
  have h1 : (∫ x, tidalCross T R a x) =
      2 * ∑ j, ∫ x, fderiv ℝ a x (axis j) * tidalFlux T R x j := by
    have hf : tidalCross T R a = fun x =>
        2 * ∑ j, fderiv ℝ a x (axis j) * tidalFlux T R x j := by
      funext x
      simp [tidalCross, dotProduct, grad, mul_comm]
    rw [hf, integral_const_mul, integral_finsetSum _ fun j _ => by simpa using (G j).1]
  have h2 : (∫ x, a x * tidalDivergence T R x) =
      ∑ j, ∫ x, a x * fderiv ℝ (fun y => tidalFlux T R y j) x (axis j) := by
    simp only [tidalDivergence, Finset.mul_sum]
    exact integral_finsetSum _ fun j _ => by simpa using (G j).2.1
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := (G j).2.2
  simp only [star_trivial] at h3
  rw [h3]
  ring

/-- The first variation of the tidal functional in the amplitude:
`d/dt ∫ (T ∂(R + t a) ∂(R + t a) - T ∂R ∂R) = -2 ∫ a ∂_j(T^{ji} ∂_i R)` at `t = 0`. -/
theorem first_variation (hsym : ∀ x ∈ U, (T x).IsSymm)
    (hT : ∀ i j, ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => T y i j) x)
    (hR : ∀ x ∈ U, ContDiffAt ℝ 2 R x) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x,
        (tidalDensity T (fun y => R y + t * a y) x - tidalDensity T R x))
      (-2 * ∫ x, a x * tidalDivergence T R x) 0 := by
  have hTc : ∀ i j, ContinuousOn (fun y => T y i j) U := fun i j x hx =>
    (hT i j x hx).continuousAt.continuousWithinAt
  have h := (hasDerivAt_relative hsym hTc
    (fun x hx => (hR x hx).of_le (by norm_num)) ha hc hs).2
  rw [integral_cross_eq hT hR ha hc hs] at h
  exact h

end FoliationQM.TidalAmplitudeVariation
