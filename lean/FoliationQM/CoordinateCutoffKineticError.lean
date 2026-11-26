module

public import FoliationQM.CoordinateMetricFluxL2
public import FoliationQM.CoordinateCutoffTestLimit
public import FoliationQM.CurvedFluxGreen
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The actual metric cutoff error and weighted kinetic limit

Source: v13 `eq:weak_pde_cutoff_bound`, component kinds C and D.
The literal double sum retains the inverse metric, volume factor and
actual field derivatives. Compact metric bounds and local coordinate L²
control give a genuine error estimate and the full kinetic pairing limit.
The field energy is on the fixed compact test support; comparison with an
arbitrary positive metric and localization to the cutoff derivative's
support remain separate geometric obligations.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffKineticError

open Filter MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open RNCVolumeDensity CurvedWaveDivergence CurvedFluxGreen SmoothCoordinateTubeCutoff
open CoordinateCutoffTestError CoordinateCutoffTestLimit
open scoped ContDiff Topology Matrix.Norms.Operator

/-- The literal source-index metric error, with the complex test conjugated and the field derivative unchanged. -/
def error (ε : ℝ) (g : Covector → Mat4) (φ ψ : Covector → ℂ) (x : Covector) : ℂ :=
  ∑ μ, ∑ ν, (volumeFactor (g x) * (g x)⁻¹ μ ν *
    fderiv ℝ (profile ε) x (axis ν)) • (star (φ x) * fderiv ℝ ψ x (axis μ))

private theorem error_zero {ε : ℝ} {g : Covector → Mat4} {φ ψ : Covector → ℂ}
    {x : Covector} (hx : x ∉ tsupport φ) : error ε g φ ψ x = 0 := by
  simp [error, image_eq_zero_of_notMem_tsupport hx]

private theorem kinetic_zero {g : Covector → Mat4} {a ψ : Covector → ℂ}
    {C : Set Covector} (hs : tsupport a ⊆ C) {x : Covector} (hx : x ∉ C) :
    volumeFactor (g x) • kinetic g a ψ x = 0 := by
  have hz := fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))
  simp [kinetic, hz]

private theorem error_sum {ε : ℝ} {g : Covector → Mat4} {φ ψ : Covector → ℂ}
    (h0 : 0 < ε) (h1 : ε < 1) (hφ : ContDiff ℝ ∞ φ)
    (hsym : ∀ x ∈ tsupport φ, (g x).IsSymm) (x : Covector) :
    error ε g φ ψ x = ∑ i, commutator ε φ (fun y => flux g ψ y i) (axis i) x := by
  have he (i : Fin 4) : commutator ε φ (fun y => flux g ψ y i) (axis i) x =
      fderiv ℝ (profile ε) x (axis i) • (star (φ x) * flux g ψ x i) := by
    rw [CoordinateCutoffTestError.commutator, CoordinateCutoffTests.directional_test h0 h1
      (hφ.differentiable (by simp) x)]
    simp only [star_add, star_smul, star_trivial, add_sub_cancel_right, smul_mul_assoc]
  simp_rw [he]
  by_cases hx : x ∈ tsupport φ
  · rw [error, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [flux, coefficient, Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hsym x hx).inv.apply]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  · simp [error_zero hx, image_eq_zero_of_notMem_tsupport hx]

private theorem kinetic_integrals {g : Covector → Mat4} {φ ψ : Covector → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hF : ∀ i : Fin 4, MemLp (fun x => flux g ψ x i) 2 (volume.restrict (tsupport φ))) :
    Integrable (fun x => volumeFactor (g x) • kinetic g φ ψ x) volume ∧
    (∫ x, volumeFactor (g x) • kinetic g φ ψ x) =
      ∑ i, ∫ x in tsupport φ, star (fderiv ℝ φ x (axis i)) * flux g ψ x i ∧
    ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      Integrable (fun x => volumeFactor (g x) • kinetic g (CoordinateCutoffTests.test ε φ) ψ x) volume ∧
      (∫ x, volumeFactor (g x) • kinetic g (CoordinateCutoffTests.test ε φ) ψ x) =
        ∑ i, ∫ x in tsupport φ,
          star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x (axis i)) * flux g ψ x i := by
  have H (i : Fin 4) := test_pairing_data hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ)
    (hF i) (axis i)
  have transfer (a : Covector → ℂ) (hs : tsupport a ⊆ tsupport φ)
      (hi : ∀ i : Fin 4, IntegrableOn
        (fun x => star (fderiv ℝ a x (axis i)) * flux g ψ x i) (tsupport φ) volume) :
      Integrable (fun x => volumeFactor (g x) • kinetic g a ψ x) volume ∧
      (∫ x, volumeFactor (g x) • kinetic g a ψ x) =
        ∑ i, ∫ x in tsupport φ, star (fderiv ℝ a x (axis i)) * flux g ψ x i := by
    have hiK : IntegrableOn (fun x => volumeFactor (g x) • kinetic g a ψ x)
        (tsupport φ) volume := by
      simp_rw [kinetic_flux]
      exact integrable_finsetSum Finset.univ fun i _ => hi i
    refine ⟨hiK.integrable_of_forall_notMem_eq_zero (fun x hx => kinetic_zero hs hx), ?_⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => kinetic_zero hs hx)]
    simp_rw [kinetic_flux]
    exact integral_finsetSum Finset.univ fun i _ => hi i
  have ho := transfer φ Subset.rfl (fun i => (H i).2.1)
  refine ⟨ho.1, ho.2, ?_⟩
  intro ε h0 h1
  have ht := CoordinateCutoffTests.test_data h0 h1 hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ)
  exact transfer (CoordinateCutoffTests.test ε φ) (fun x hx => (ht.2.2.1 hx).1)
    (fun i => ((H i).2.2 h0 h1).2)

private theorem flux_energy_bound {C : Set Covector} (hC : IsCompact C)
    {g : Covector → Mat4} {ψ : Covector → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ j : Fin 4, IntegrableOn (fun x => ‖fderiv ℝ ψ x (axis j)‖ ^ 2) C volume)
    (hF : ∀ i : Fin 4, MemLp (fun x => flux g ψ x i) 2 (volume.restrict C) ∧
      ∀ x ∈ C, ‖flux g ψ x i‖ ≤ B * ∑ j, ‖fderiv ℝ ψ x (axis j)‖) (i : Fin 4) :
    Real.sqrt (∫ x in C, ‖flux g ψ x i‖ ^ 2) ≤
      (2 * B) * Real.sqrt (∫ x in C, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (hF i).1.aestronglyMeasurable).1 (hF i).1
  have hsum := integrable_finsetSum Finset.univ fun j _ => hD j
  have he : (∫ x in C, ‖flux g ψ x i‖ ^ 2) ≤
      (2 * B) ^ 2 * (∫ x in C, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) := by
    calc
      _ ≤ ∫ x in C, (2 * B) ^ 2 * ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2 := by
        apply integral_mono_ae hi (hsum.const_mul ((2 * B) ^ 2))
        filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
        have hs : (∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖) ^ 2 ≤
            4 * ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun j : Fin 4 => ‖fderiv ℝ ψ x (axis j)‖)
        calc
          _ ≤ (B * ∑ j, ‖fderiv ℝ ψ x (axis j)‖) ^ 2 := by gcongr; exact (hF i).2 x hx
          _ = B ^ 2 * (∑ j, ‖fderiv ℝ ψ x (axis j)‖) ^ 2 := by ring
          _ ≤ B ^ 2 * (4 * ∑ j, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hs (sq_nonneg B)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ Real.sqrt ((2 * B) ^ 2 *
        (∫ x in C, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2)) := Real.sqrt_le_sqrt he
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg (2 * B)), Real.sqrt_sq (by positivity)]

/-- Bounds derived from the compact test and metric before the field give genuine kinetic and error integrability, the literal metric commutator identity, and its explicit fixed-support coordinate-energy estimate. -/
theorem error_data {φ : Covector → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ x, ‖φ x‖ ≤ A) ∧
      ∀ (g : Covector → Mat4) (U : Set Covector), tsupport φ ⊆ U →
        (∀ x ∈ U, ContDiffAt ℝ 1 g x) → (∀ x ∈ U, (g x).det < 0) →
        (∀ x ∈ tsupport φ, (g x).IsSymm) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : Covector → ℂ,
          (∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U)) →
          IntegrableOn (fun x => ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) (tsupport φ) volume ∧
          Integrable (fun x => volumeFactor (g x) • kinetic g φ ψ x) volume ∧
          ∀ {ε : ℝ}, 0 < ε → ε < 1 →
            Integrable (fun x => volumeFactor (g x) • kinetic g (CoordinateCutoffTests.test ε φ) ψ x) volume ∧
            Integrable (error ε g φ ψ) volume ∧ Integrable (fun x => ‖error ε g φ ψ x‖) volume ∧
            (∀ x, volumeFactor (g x) • kinetic g (CoordinateCutoffTests.test ε φ) ψ x =
              profile ε x • (volumeFactor (g x) • kinetic g φ ψ x) + error ε g φ ψ x) ∧
            ‖∫ x, error ε g φ ψ x‖ ≤ ∫ x, ‖error ε g φ ψ x‖ ∧
            (∫ x, ‖error ε g φ ψ x‖) ≤
              A * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
                ∑ i : Fin 4, Real.sqrt (∫ x in tsupport φ, ‖flux g ψ x i‖ ^ 2) ∧
            (∫ x, ‖error ε g φ ψ x‖) ≤
              8 * A * B * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
                Real.sqrt (∫ x in tsupport φ, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) := by
  obtain ⟨A, hA, hAb, htest⟩ := test_error_data hφ hc
  refine ⟨A, hA, hAb, ?_⟩
  intro g U hs hg hd hsym
  obtain ⟨B, hB, hflux⟩ := CoordinateMetricFluxL2.flux_data hc hs hg hd
  refine ⟨B, hB, ?_⟩
  intro ψ hD
  have hF := hflux ψ hD
  have hD2 (j : Fin 4) : IntegrableOn (fun x => ‖fderiv ℝ ψ x (axis j)‖ ^ 2)
      (tsupport φ) volume := by
    have H := MemLp.mono_measure (Measure.restrict_mono_set volume hs) (hD j)
    exact (memLp_two_iff_integrable_sq_norm H.aestronglyMeasurable).1 H
  have hK := kinetic_integrals hφ hc (fun i => (hF i).1)
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hD2 j), hK.1, ?_⟩
  intro ε h0 h1
  have H (i : Fin 4) := ((htest (tsupport φ) (fun x => flux g ψ x i) Subset.rfl
    (hF i).1).2 (axis i) h0 h1)
  have he (x) := error_sum h0 h1 hφ hsym (ψ := ψ) x
  have hi : IntegrableOn (error ε g φ ψ) (tsupport φ) volume := by
    exact (integrable_finsetSum Finset.univ (fun i _ => (H i).2.1)).congr
      (Eventually.of_forall fun x => (he x).symm)
  have hiA := hi.integrable_of_forall_notMem_eq_zero (fun x hx => error_zero hx)
  have hn : (∫ x, ‖error ε g φ ψ x‖) = ∫ x in tsupport φ, ‖error ε g φ ψ x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [error_zero hx, norm_zero])).symm
  have hb : (∫ x, ‖error ε g φ ψ x‖) ≤
      A * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
        ∑ i : Fin 4, Real.sqrt (∫ x in tsupport φ, ‖flux g ψ x i‖ ^ 2) := by
    rw [hn]
    calc
      _ ≤ ∫ x in tsupport φ, ∑ i : Fin 4,
          ‖commutator ε φ (fun y => flux g ψ y i) (axis i) x‖ := by
        apply integral_mono hi.norm (integrable_finsetSum Finset.univ fun i _ => (H i).2.2.1)
        intro x
        dsimp only
        rw [he]
        exact norm_sum_le _ _
      _ = ∑ i : Fin 4, ∫ x in tsupport φ,
          ‖commutator ε φ (fun y => flux g ψ y i) (axis i) x‖ :=
        integral_finsetSum Finset.univ fun i _ => (H i).2.2.1
      _ ≤ ∑ i : Fin 4, A * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
          Real.sqrt (∫ x in tsupport φ, ‖flux g ψ x i‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [axis, Pi.norm_single, norm_one, mul_one] using (H i).2.2.2.2
      _ = _ := by rw [Finset.mul_sum]
  refine ⟨(hK.2.2 h0 h1).1, hiA, hiA.norm, ?_, norm_integral_le_integral_norm _, hb, ?_⟩
  · intro x
    rw [kinetic_flux, kinetic_flux, he, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [CoordinateCutoffTestError.commutator, sub_mul, smul_mul_assoc]
    abel
  · calc
      _ ≤ A * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
          ∑ i : Fin 4, Real.sqrt (∫ x in tsupport φ, ‖flux g ψ x i‖ ^ 2) := hb
      _ ≤ A * Real.sqrt (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
          ∑ _i : Fin 4, (2 * B) * Real.sqrt
            (∫ x in tsupport φ, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (Real.sqrt_nonneg _))
        exact Finset.sum_le_sum fun i _ => flux_energy_bound hc hB hD2 hF i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The actual error and its norm integral vanish, while the full ambient density-weighted kinetic pairing converges, for the same local coordinate-L² field and smooth compact test. -/
theorem error_and_kinetic_limits {φ ψ : Covector → ℂ} {g : Covector → Mat4} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hsym : ∀ x ∈ tsupport φ, (g x).IsSymm)
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U)) :
    Tendsto (fun ε : ℝ => ∫ x, ‖error ε g φ ψ x‖) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x, error ε g φ ψ x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x, volumeFactor (g x) • kinetic g (CoordinateCutoffTests.test ε φ) ψ x)
      (𝓝[>] 0) (𝓝 (∫ x, volumeFactor (g x) • kinetic g φ ψ x)) := by
  obtain ⟨A, _, _, hdata⟩ := error_data hφ hc
  obtain ⟨B, _, H⟩ := hdata g U hs hg hd hsym
  have Hψ := H ψ hD
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp
    (CoordinateCutoffCompactEnergy.compact_derivative_decay (tsupport φ) hc).1
  have hr0 : Tendsto (fun ε : ℝ => Real.sqrt
      (∫ x in tsupport φ, ‖fderiv ℝ (profile ε) x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using hr
  have hupper := (hr0.const_mul (8 * A * B)).mul_const
    (Real.sqrt (∫ x in tsupport φ, ∑ j : Fin 4, ‖fderiv ℝ ψ x (axis j)‖ ^ 2))
  have hnorm : Tendsto (fun ε : ℝ => ∫ x, ‖error ε g φ ψ x‖) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => norm_nonneg _)) ?_
      (by simpa only [mul_zero, zero_mul] using hupper)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (Hψ.2.2 hε.1 hε.2).2.2.2.2.2.2
  have hcomplex : Tendsto (fun ε : ℝ => ∫ x, error ε g φ ψ x) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hnorm
    exact Eventually.of_forall fun ε => norm_integral_le_integral_norm _
  refine ⟨hnorm, hcomplex, ?_⟩
  obtain ⟨_, _, hflux⟩ := CoordinateMetricFluxL2.flux_data hc hs hg hd
  have hF (i : Fin 4) := (hflux ψ hD i).1
  have hK := kinetic_integrals hφ hc hF
  have hlim := tendsto_finsetSum Finset.univ fun i _ =>
    (test_pairing_limits hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ) (hF i) (axis i)).2
  rw [← hK.2.1] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (hK.2.2 hε.1 hε.2).2.symm

end FoliationQM.CoordinateCutoffKineticError
