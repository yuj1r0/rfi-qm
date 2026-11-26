module

public import FoliationQM.KLDifferentiation
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Componentwise envelopes for actual translated KL differentiation

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, supplement
`prop:audit11_kl`. In three spatial coordinates, integrable common envelopes
for the three weighted first log partials and nine weighted second log
partials suffice for the continuous-linear-map domination hypotheses.
The operator-norm bounds follow from expansion in the actual coordinate
basis and the coordinate supremum norm; they are not additional assumptions.
All bounds use the same translation ball and an almost-everywhere set that
is independent of the translation. Finite linearity also transports explicit
coordinate boundary integral conditions to arbitrary directions, with every
integrability premise retained. No KL Hessian identity is assumed here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLDomination

open MeasureTheory Metric TranslatedKL
open scoped BigOperators

local notation "V" => Fin 3 → ℝ

/-- An actual continuous linear map is determined by its coordinate entries. -/
theorem linear_apply_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : V →L[ℝ] G) (v : V) :
    L v = ∑ i : Fin 3, (v i) • L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul]

/-- The two genuine linear evaluations of a bilinear form give its finite
coordinate expansion, without symmetry assumptions. -/
theorem bilinear_apply_eq_sum (H : V →L[ℝ] (V →L[ℝ] ℝ)) (u v : V) :
    H u v = ∑ i : Fin 3, ∑ j : Fin 3,
      (u i * v j) * H (Pi.single i 1) (Pi.single j 1) := by
  calc
    H u v = ∑ i : Fin 3, u i * H (Pi.single i 1) v := by
      simpa only [sum_apply, smul_apply, smul_eq_mul] using
        congrArg (fun L : V →L[ℝ] ℝ => L v) (linear_apply_eq_sum H u)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [linear_apply_eq_sum (H (Pi.single i 1)) v, Finset.mul_sum]
      simp only [smul_eq_mul, mul_assoc]

/-- The genuine operator norm of a map on the three spatial coordinates is
bounded by the sum of its three actual coordinate-basis evaluations. -/
theorem norm_le_sum_basis {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : V →L[ℝ] G) : ‖L‖ ≤ ∑ i : Fin 3, ‖L (Pi.single i 1)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  rw [linear_apply_eq_sum L v]
  calc
    ‖∑ i : Fin 3, (v i) • L (Pi.single i 1)‖ ≤
        ∑ i : Fin 3, ‖(v i) • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖v i‖ * ‖L (Pi.single i 1)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖L (Pi.single i 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (Pi.single i 1)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- The genuine nested operator norm of a continuous bilinear form is
bounded by the nine absolute coordinate entries. -/
theorem norm_bilinear_le_sum_basis (H : V →L[ℝ] (V →L[ℝ] ℝ)) :
    ‖H‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H (Pi.single i 1) (Pi.single j 1)‖ := by
  exact (norm_le_sum_basis H).trans
    (Finset.sum_le_sum fun i _ => norm_le_sum_basis (H (Pi.single i 1)))

/-- A first coordinate entry is the actual weighted first log partial,
including the negative sign from differentiating the translated KL density. -/
theorem firstIntegrand_basis (f : V → ℝ) (a x : V) (i : Fin 3) :
    firstIntegrand f a x (Pi.single i 1) =
      -(f x) * fderiv ℝ (fun y => Real.log (f y)) (x + a) (Pi.single i 1) := rfl

/-- A second coordinate entry is the actual weighted mixed log partial;
both derivatives are genuine Fréchet derivatives. -/
theorem secondIntegrand_basis (f : V → ℝ) (a x : V) (i j : Fin 3) :
    secondIntegrand f a x (Pi.single i 1) (Pi.single j 1) =
      -(f x) * fderiv ℝ (fderiv ℝ (fun y => Real.log (f y)))
        (x + a) (Pi.single i 1) (Pi.single j 1) := rfl

/-- Finite componentwise integrable envelopes on the same translation ball
produce the operator-norm domination record used for actual KL differentiation. -/
def of_component_bounds {f : V → ℝ} {μ : Measure V} {r : ℝ} (hr : 0 < r)
    (B₁ : Fin 3 → V → ℝ) (B₂ : Fin 3 → Fin 3 → V → ℝ)
    (hB₁ : ∀ i, Integrable (B₁ i) μ) (hB₂ : ∀ i j, Integrable (B₂ i j) μ)
    (hfirst : ∀ i, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      ‖firstIntegrand f a x (Pi.single i 1)‖ ≤ B₁ i x)
    (hsecond : ∀ i j, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      ‖secondIntegrand f a x (Pi.single i 1) (Pi.single j 1)‖ ≤ B₂ i j x) :
    KLDifferentiation.Domination f μ r where
  radius_pos := hr
  firstBound x := ∑ i : Fin 3, B₁ i x
  secondBound x := ∑ i : Fin 3, ∑ j : Fin 3, B₂ i j x
  first_integrable := integrable_finsetSum _ (fun i _ => hB₁ i)
  second_integrable := integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hB₂ i j))
  first_le := by
    have hall : ∀ᵐ x ∂μ, ∀ i, ∀ a ∈ ball (0 : V) r,
        ‖firstIntegrand f a x (Pi.single i 1)‖ ≤ B₁ i x :=
      ae_all_iff.mpr hfirst
    filter_upwards [hall] with x hx
    intro a ha
    exact (norm_le_sum_basis (firstIntegrand f a x)).trans
      (Finset.sum_le_sum fun i _ => hx i a ha)
  second_le := by
    have hall : ∀ᵐ x ∂μ, ∀ i j, ∀ a ∈ ball (0 : V) r,
        ‖secondIntegrand f a x (Pi.single i 1) (Pi.single j 1)‖ ≤ B₂ i j x :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hsecond i)
    filter_upwards [hall] with x hx
    intro a ha
    exact (norm_bilinear_le_sum_basis (secondIntegrand f a x)).trans
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hx i j a ha)

/-- Common absolute-value envelopes for the source's literal weighted first
and second log partials suffice for the same domination record. -/
def of_weighted_log_bounds {f : V → ℝ} {μ : Measure V} {r : ℝ} (hr : 0 < r)
    (B₁ : Fin 3 → V → ℝ) (B₂ : Fin 3 → Fin 3 → V → ℝ)
    (hB₁ : ∀ i, Integrable (B₁ i) μ) (hB₂ : ∀ i j, Integrable (B₂ i j) μ)
    (hfirst : ∀ i, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      |f x * fderiv ℝ (fun y => Real.log (f y)) (x + a) (Pi.single i 1)| ≤ B₁ i x)
    (hsecond : ∀ i j, ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : V) r,
      |f x * fderiv ℝ (fderiv ℝ (fun y => Real.log (f y)))
        (x + a) (Pi.single i 1) (Pi.single j 1)| ≤ B₂ i j x) :
    KLDifferentiation.Domination f μ r := by
  apply of_component_bounds hr B₁ B₂ hB₁ hB₂
  · intro i
    filter_upwards [hfirst i] with x hx
    intro a ha
    simpa only [firstIntegrand_basis, neg_mul, norm_neg, Real.norm_eq_abs] using hx a ha
  · intro i j
    filter_upwards [hsecond i j] with x hx
    intro a ha
    simpa only [secondIntegrand_basis, neg_mul, norm_neg, Real.norm_eq_abs] using hx a ha

section Boundary

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrable coordinate entries make every directional evaluation of a
linear field genuinely integrable. -/
theorem integrable_linear_apply (L : X → V →L[ℝ] ℝ)
    (hL : ∀ i, Integrable (fun x => L x (Pi.single i 1)) μ) (v : V) :
    Integrable (fun x => L x v) μ := by
  have he : (fun x => L x v) = (fun x => ∑ i : Fin 3, v i * L x (Pi.single i 1)) := by
    funext x
    exact linear_apply_eq_sum (L x) v
  rw [he]
  exact integrable_finsetSum _ (fun i _ => (hL i).const_mul (v i))

/-- Genuine integration commutes with the finite coordinate expansion of
a linear field, with integrability checked for every entry. -/
theorem integral_linear_apply (L : X → V →L[ℝ] ℝ)
    (hL : ∀ i, Integrable (fun x => L x (Pi.single i 1)) μ) (v : V) :
    (∫ x, L x v ∂μ) = ∑ i : Fin 3, v i * ∫ x, L x (Pi.single i 1) ∂μ := by
  have he : (fun x => L x v) = (fun x => ∑ i : Fin 3, v i * L x (Pi.single i 1)) := by
    funext x
    exact linear_apply_eq_sum (L x) v
  rw [he, integral_finsetSum _ (fun i _ => (hL i).const_mul (v i))]
  simp only [integral_const_mul]

/-- Zero integrals of the three integrable coordinate entries imply the
zero integral boundary condition in every direction. -/
theorem integral_linear_apply_eq_zero (L : X → V →L[ℝ] ℝ)
    (hL : ∀ i, Integrable (fun x => L x (Pi.single i 1)) μ)
    (hzero : ∀ i, (∫ x, L x (Pi.single i 1) ∂μ) = 0) (v : V) :
    (∫ x, L x v ∂μ) = 0 := by
  rw [integral_linear_apply L hL v]
  simp only [hzero, mul_zero, Finset.sum_const_zero]

/-- Integrability of the nine coordinate entries gives genuine integrability
of every mixed directional evaluation of a bilinear field. -/
theorem integrable_bilinear_apply (H : X → V →L[ℝ] (V →L[ℝ] ℝ))
    (hH : ∀ i j, Integrable (fun x => H x (Pi.single i 1) (Pi.single j 1)) μ)
    (u v : V) : Integrable (fun x => H x u v) μ := by
  have he : (fun x => H x u v) = (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      (u i * v j) * H x (Pi.single i 1) (Pi.single j 1)) :=
    funext (fun x => bilinear_apply_eq_sum (H x) u v)
  rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hH i j).const_mul (u i * v j)))

/-- Genuine integration commutes with both finite coordinate expansions
of an entrywise integrable bilinear field. -/
theorem integral_bilinear_apply (H : X → V →L[ℝ] (V →L[ℝ] ℝ))
    (hH : ∀ i j, Integrable (fun x => H x (Pi.single i 1) (Pi.single j 1)) μ)
    (u v : V) : (∫ x, H x u v ∂μ) = ∑ i : Fin 3, ∑ j : Fin 3,
      (u i * v j) * ∫ x, H x (Pi.single i 1) (Pi.single j 1) ∂μ := by
  have he : (fun x => H x u v) = (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      (u i * v j) * H x (Pi.single i 1) (Pi.single j 1)) :=
    funext (fun x => bilinear_apply_eq_sum (H x) u v)
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hH i j).const_mul (u i * v j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hH i j).const_mul (u i * v j))]
  simp only [integral_const_mul]

/-- Zero integrals of the nine integrable coordinate entries imply every
mixed-direction zero integral boundary condition. -/
theorem integral_bilinear_apply_eq_zero (H : X → V →L[ℝ] (V →L[ℝ] ℝ))
    (hH : ∀ i j, Integrable (fun x => H x (Pi.single i 1) (Pi.single j 1)) μ)
    (hzero : ∀ i j, (∫ x, H x (Pi.single i 1) (Pi.single j 1) ∂μ) = 0)
    (u v : V) : (∫ x, H x u v ∂μ) = 0 := by
  rw [integral_bilinear_apply H hH u v]
  simp only [hzero, mul_zero, Finset.sum_const_zero]

end Boundary

end FoliationQM.KLDomination
