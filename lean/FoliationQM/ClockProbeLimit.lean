module

public import FoliationQM.ClockProbeCovariance
public import FoliationQM.SecondOrderFrechet
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform quadratic remainders under actual bounded clock-probe averages

Source: the averaged small-shift step in v13 `eq:kl_fisher_expansion`.
The three independent physical phases use the already defined actual iterated
normalized integrals. Bounded probes turn a genuine uniform Fréchet remainder
into a bound uniform in all phases, and actual integrability permits subtraction
inside the averages. This is an analytic bridge for a supplied real function;
identification of that function with translated KL and of its Hessian with
spatial Fisher information is not asserted here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockProbeLimit

open ClockCircleAverage ClockProbeCovariance Filter Topology Set
open MeasureTheory (volume)
open scoped BigOperators

/-- The three-dimensional real probe displacement space, with its usual finite-product norm. -/
abbrev Space := Fin 3 → ℝ

/-- The quadratic term associated with an actual continuous bilinear second derivative. -/
def quadratic (H : Space →L[ℝ] Space →L[ℝ] ℝ) (a : Space) : ℝ :=
  (1 / 2 : ℝ) * H a a

/-- A continuous bilinear form gives a continuous quadratic function. -/
theorem continuous_quadratic (H : Space →L[ℝ] Space →L[ℝ] ℝ) :
    Continuous (quadratic H) := by
  unfold quadratic
  fun_prop

/-- Scaling a displacement scales its quadratic term by the squared real factor. -/
theorem quadratic_smul (H : Space →L[ℝ] Space →L[ℝ] ℝ) (ε : ℝ) (a : Space) :
    quadratic H (ε • a) = ε ^ 2 * quadratic H a := by
  simp only [quadratic, map_smul, smul_apply, smul_eq_mul]
  ring

/-- Every stipulated physical probe has norm bounded by the absolute radius. -/
theorem norm_displacement_le (ell : ℝ) (θ : Space) :
    ‖displacement ell θ‖ ≤ |ell| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg ell)).mpr
  intro i
  simp only [displacement, Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (θ i)) (abs_nonneg ell)

/-- The physical probe depends continuously on its three real phase representatives. -/
theorem continuous_displacement (ell : ℝ) : Continuous (displacement ell) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul (Real.continuous_cos.comp (continuous_apply i))

/-- Small real scaling puts all bounded physical probes into any prescribed
neighborhood of zero, uniformly in the three phase representatives. -/
theorem eventually_scaled_displacement_mem (ell : ℝ) {s : Set Space}
    (hs : s ∈ 𝓝 (0 : Space)) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ θ : Space, ε • displacement ell θ ∈ s := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hs
  have hden : 0 < |ell| + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hr hden)] with ε hε
  intro θ
  apply hsub
  rw [Metric.mem_ball, dist_zero_right]
  have he : |ε| * (|ell| + 1) < r := by
    apply (lt_div_iff₀ hden).mp
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hε
  calc
    ‖ε • displacement ell θ‖ = |ε| * ‖displacement ell θ‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |ε| * |ell| := mul_le_mul_of_nonneg_left (norm_displacement_le ell θ) (abs_nonneg ε)
    _ < r := by nlinarith [abs_nonneg ε]

/-- A uniform pointwise norm bound passes through one actual normalized phase integral. -/
theorem norm_average_le {f : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ θ, ‖f θ‖ ≤ C) : ‖average f‖ ≤ C := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun θ _ => hf θ)
  have hp : 0 < 2 * Real.pi := by positivity
  rw [sub_zero, abs_of_pos hp] at hi
  rw [average, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, f θ‖ ≤
        (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hp.le)
    _ = C := by field_simp

/-- A uniform pointwise bound survives the actual three successive normalized averages. -/
theorem norm_average3_le {f : Space → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ θ, ‖f θ‖ ≤ C) : ‖average3 f‖ ≤ C := by
  apply norm_average_le hC
  intro t0
  apply norm_average_le hC
  intro t1
  exact norm_average_le hC (fun t2 => hf ![t0, t1, t2])

/-- A jointly continuous phase family has a continuously varying actual circle average. -/
theorem continuous_average {X : Type*} [TopologicalSpace X] {F : X → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) : Continuous (fun x => average (F x)) := by
  unfold average
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 (2 * Real.pi))

/-- Every continuous function of the three phases has genuine integrability
at all three stages of the iterated average. -/
theorem iteratedIntegrable_of_continuous {f : Space → ℝ} (hf : Continuous f) :
    IteratedIntegrable f := by
  have hinner : Continuous (fun a : ℝ × ℝ => average (fun t => f ![a.1, a.2, t])) := by
    apply continuous_average
    apply hf.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hmiddle : Continuous (fun t0 : ℝ => average (fun t1 =>
      average (fun t2 => f ![t0, t1, t2]))) := continuous_average hinner
  refine ⟨?_, ?_, hmiddle.intervalIntegrable _ _⟩
  · intro t0 t1
    apply Continuous.intervalIntegrable
    apply hf.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  · intro t0
    exact (hinner.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- Subtraction commutes with the actual iterated average when every stage
is genuinely integrable for both functions. -/
theorem average3_sub {f g : Space → ℝ} (hf : IteratedIntegrable f)
    (hg : IteratedIntegrable g) :
    average3 (fun θ => f θ - g θ) = average3 f - average3 g := by
  unfold average3
  simp_rw [average_sub (hf.1 _ _) (hg.1 _ _)]
  simp_rw [average_sub (hf.2.1 _) (hg.2.1 _)]
  exact average_sub hf.2.2 hg.2.2

/-- Addition commutes with the actual iterated average under genuine stagewise integrability. -/
theorem average3_add {f g : Space → ℝ} (hf : IteratedIntegrable f)
    (hg : IteratedIntegrable g) :
    average3 (fun θ => f θ + g θ) = average3 f + average3 g := by
  unfold average3
  simp_rw [average_add (hf.1 _ _) (hg.1 _ _)]
  simp_rw [average_add (hf.2.1 _) (hg.2.1 _)]
  exact average_add hf.2.2 hg.2.2

/-- Finite sums of continuous phase functions commute with the actual threefold average. -/
theorem average3_sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    average3 (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, average3 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [average3_const]
  | @insert i s hi ih =>
    have hsi : Continuous (f i) := hf i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, Continuous (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [average3_add (iteratedIntegrable_of_continuous hsi)
      (iteratedIntegrable_of_continuous (continuous_finsetSum s hs)), ih hs]

/-- The ordinary coordinate vectors decompose every finite physical displacement. -/
theorem sum_coordinate_vectors (a : Space) :
    (∑ i : Fin 3, a i • (Pi.single i 1 : Space)) = a := by
  have he (i : Fin 3) : a i • (Pi.single i 1 : Space) = Pi.single i (a i) := by
    rw [← Pi.single_smul]
    simp
  simp_rw [he]
  exact Finset.univ_sum_single a

/-- A continuous bilinear Hessian is exactly its coordinate double sum,
without any symmetry assumption. -/
theorem bilinear_coordinate_expansion (H : Space →L[ℝ] Space →L[ℝ] ℝ) (a b : Space) :
    H a b = ∑ i : Fin 3, ∑ j : Fin 3,
      (a i * b j) * H (Pi.single i 1) (Pi.single j 1) := by
  conv_lhs => rw [← sum_coordinate_vectors a, ← sum_coordinate_vectors b]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual physical probe average of a continuous Hessian's quadratic
term is one quarter the squared radius times its coordinate trace. -/
theorem average3_quadratic (ell : ℝ) (H : Space →L[ℝ] Space →L[ℝ] ℝ) :
    average3 (fun θ => quadratic H (displacement ell θ)) =
      ell ^ 2 / 4 * ∑ i : Fin 3, H (Pi.single i 1) (Pi.single i 1) := by
  have he : (fun θ => H (displacement ell θ) (displacement ell θ)) =
      (fun θ => ∑ i : Fin 3, ∑ j : Fin 3,
        H (Pi.single i 1) (Pi.single j 1) *
          (displacement ell θ i * displacement ell θ j)) := by
    funext θ
    rw [bilinear_coordinate_expansion]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc (i j : Fin 3) : Continuous (fun θ : Space =>
      H (Pi.single i 1) (Pi.single j 1) *
        (displacement ell θ i * displacement ell θ j)) := by
    unfold displacement
    fun_prop
  unfold quadratic
  rw [average3_const_mul, he, average3_sum _ _
    (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
  simp_rw [average3_sum _ _ (fun j _ => hc _ j), average3_const_mul]
  have hcov (i j : Fin 3) :
      average3 (fun θ => displacement ell θ i * displacement ell θ j) = covariance ell i j := by
    simp only [covariance, mean_zero, sub_zero]
  simp_rw [hcov, covariance_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  ring

/-- Continuity near zero gives genuine continuity of all sufficiently small
probe compositions, uniformly in the physical phases. -/
theorem eventually_continuous_probe (ell : ℝ) {K : Space → ℝ}
    (hK : ∀ᶠ a in 𝓝 (0 : Space), ContinuousAt K a) :
    ∀ᶠ ε : ℝ in 𝓝 0, Continuous (fun θ => K (ε • displacement ell θ)) := by
  filter_upwards [eventually_scaled_displacement_mem ell hK] with ε hε
  rw [continuous_iff_continuousAt]
  intro θ
  exact (hε θ).comp (x := θ)
    (show ContinuousAt (fun θ : Space => ε • displacement ell θ) θ from
      by simpa using! ((continuous_displacement ell).const_smul ε).continuousAt)

/-- Division by a fixed real factor commutes with the actual iterated phase integral. -/
theorem average3_div_const (f : Space → ℝ) (c : ℝ) :
    average3 (fun θ => f θ / c) = average3 f / c := by
  have he : (fun θ => f θ / c) = (fun θ => c⁻¹ * f θ) := by funext θ; ring
  rw [he, average3_const_mul]
  ring

/-- A uniform quadratic little-o remainder gives a quotient error bound
uniform in every bounded physical probe, including zero probe coordinates. -/
theorem eventually_probe_quotient_error_le (ell : ℝ) {K : Space → ℝ}
    (H : Space →L[ℝ] Space →L[ℝ] ℝ)
    (hrem : (fun a => K a - quadratic H a) =o[𝓝 (0 : Space)] (fun a => ‖a‖ ^ 2))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0, ∀ θ : Space,
      ‖K (ε • displacement ell θ) / ε ^ 2 - quadratic H (displacement ell θ)‖ ≤ η := by
  let c := η / (ell ^ 2 + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_bound : c * ell ^ 2 ≤ η := by
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < ell ^ 2 + 1)).mpr
    nlinarith
  have hsmall := eventually_scaled_displacement_mem ell (hrem.def hc)
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hε0
  intro θ
  have hεne : ε ≠ 0 := hε0
  have hnorm : ‖ε • displacement ell θ‖ ^ 2 ≤ ε ^ 2 * ell ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
    have hd := norm_displacement_le ell θ
    nlinarith [norm_nonneg (displacement ell θ), sq_abs ell]
  have hb : ‖K (ε • displacement ell θ) - quadratic H (ε • displacement ell θ)‖ ≤
      c * (ε ^ 2 * ell ^ 2) := by
    have he := hε θ
    rw [Real.norm_of_nonneg (sq_nonneg ‖ε • displacement ell θ‖)] at he
    exact he.trans (mul_le_mul_of_nonneg_left hnorm hc.le)
  have heq : K (ε • displacement ell θ) / ε ^ 2 - quadratic H (displacement ell θ) =
      (K (ε • displacement ell θ) - quadratic H (ε • displacement ell θ)) / ε ^ 2 := by
    rw [quadratic_smul]
    field_simp
  rw [heq, norm_div, Real.norm_of_nonneg (sq_nonneg ε)]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hεne)).mpr
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hc_bound (sq_nonneg ε)])

/-- Genuine near-origin continuity and a uniform quadratic remainder imply
the actual averaged small-probe limit. The remainder is an explicit analytic
hypothesis here; the next theorem derives it from an actual second derivative. -/
theorem tendsto_average3_div_sq_of_isLittleO (ell : ℝ) {K : Space → ℝ}
    (H : Space →L[ℝ] Space →L[ℝ] ℝ)
    (hK : ∀ᶠ a in 𝓝 (0 : Space), ContinuousAt K a)
    (hrem : (fun a => K a - quadratic H a) =o[𝓝 (0 : Space)] (fun a => ‖a‖ ^ 2)) :
    Tendsto (fun ε : ℝ => average3 (fun θ => K (ε • displacement ell θ)) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (average3 (fun θ => quadratic H (displacement ell θ)))) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have he := eventually_probe_quotient_error_le ell H hrem (half_pos hη)
  have hc : ∀ᶠ ε : ℝ in 𝓝[≠] 0, Continuous (fun θ => K (ε • displacement ell θ)) :=
    (eventually_continuous_probe ell hK).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, hc] with ε hε hcε
  have hiK := iteratedIntegrable_of_continuous (hcε.div_const (ε ^ 2))
  have hiQ := iteratedIntegrable_of_continuous
    ((continuous_quadratic H).comp (continuous_displacement ell))
  have hid := average3_sub hiK hiQ
  rw [average3_div_const] at hid
  simp only [Function.comp_def] at hid
  rw [dist_eq_norm, ← hid]
  exact (norm_average3_le (half_pos hη).le hε).trans_lt (half_lt_self hη)

/-- An actual second Fréchet derivative, eventual first differentiability,
and vanishing zeroth/first terms suffice for the averaged quadratic limit.
No remainder, covariance, Fisher identity, or limit is assumed. -/
theorem tendsto_average3_div_sq_of_second_derivative (ell : ℝ) {K : Space → ℝ}
    {H : Space →L[ℝ] Space →L[ℝ] ℝ}
    (hdiff : ∀ᶠ a in 𝓝 (0 : Space), DifferentiableAt ℝ K a)
    (hH : HasFDerivAt (fderiv ℝ K) H 0) (hzero : K 0 = 0) (hfirst : fderiv ℝ K 0 = 0) :
    Tendsto (fun ε : ℝ => average3 (fun θ => K (ε • displacement ell θ)) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (average3 (fun θ => quadratic H (displacement ell θ)))) :=
  tendsto_average3_div_sq_of_isLittleO ell H
    (hdiff.mono (fun _ h => h.continuousAt))
    (SecondOrderFrechet.isLittleO_sub_quadratic hdiff hH hzero hfirst)

/-- The actual averaged small-probe limit is the Hessian trace with the
calculated physical covariance coefficient. KL/Fisher identification is separate. -/
theorem tendsto_average3_div_sq_trace (ell : ℝ) {K : Space → ℝ}
    {H : Space →L[ℝ] Space →L[ℝ] ℝ}
    (hdiff : ∀ᶠ a in 𝓝 (0 : Space), DifferentiableAt ℝ K a)
    (hH : HasFDerivAt (fderiv ℝ K) H 0) (hzero : K 0 = 0) (hfirst : fderiv ℝ K 0 = 0) :
    Tendsto (fun ε : ℝ => average3 (fun θ => K (ε • displacement ell θ)) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (ell ^ 2 / 4 * ∑ i : Fin 3, H (Pi.single i 1) (Pi.single i 1))) := by
  simpa only [average3_quadratic] using
    tendsto_average3_div_sq_of_second_derivative ell hdiff hH hzero hfirst

end FoliationQM.ClockProbeLimit
