module

public import FoliationQM.KLHessian
public import FoliationQM.KLDomination
public import FoliationQM.ClockProbeLimit
public import FoliationQM.ClockFisherBridge
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The actual averaged translated KL limit and physical Fisher coefficient

Sources: v13 `eq:kl_fisher_expansion`, `thm:clock_sideband`, and supplement
`prop:audit11_kl`. The function being averaged is the actual translated KL
integral. Its derivatives, boundary cancellations, uniform quadratic remainder,
and phase-average limit are all derived. Actual auxiliary-density normalization
then gives the unnormalized physical Fisher coefficient. Only the independent
Compton probe model and the explicit regularity, common domination, finite
Fisher and zero-integral boundary conditions are inputs. No finite-shift
fourth-order remainder is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockKLLimit

open MeasureTheory Filter Metric TranslatedKL KLDifferentiation FisherNormalization
open ClockProbeCovariance ClockProbeLimit
open scoped Topology BigOperators

/-- The three actual laboratory coordinate directions. -/
def coordinate (i : Fin 3) : Space := Pi.single i 1

/-- Actual first-derivative domination and the three coordinate boundary
cancellations imply the full first-order boundary condition. -/
theorem boundary_all_directions {f : Space → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure Space} {r : ℝ} (D : Domination f μ r)
    (hboundary : ∀ i, (∫ x, fderiv ℝ f x (coordinate i) ∂μ) = 0) (v : Space) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 :=
  KLDomination.integral_linear_apply_eq_zero (fderiv ℝ f)
    (fun i => KLHessian.integrable_fderiv_apply hf hpos D (coordinate i)) hboundary v

/-- The actual three-phase averaged translated KL limit equals the positive
spatial Fisher trace with the calculated radius coefficient. -/
theorem tendsto_averaged_kl (ell : ℝ) {f : Space → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure Space} {r : ℝ} (D : Domination f μ r)
    (hfirst : ∀ i, (∫ x, fderiv ℝ f x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand f coordinate i i) μ)
    (hSecond : ∀ i, Integrable
      (fun x => fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i) ∂μ) = 0) :
    Tendsto (fun ε : ℝ => average3 (fun θ => value f μ (ε • displacement ell θ)) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (ell ^ 2 / 4 * fisherTrace f coordinate μ)) := by
  have hd : ∀ᶠ a in 𝓝 (0 : Space), DifferentiableAt ℝ (value f μ) a := by
    filter_upwards [ball_mem_nhds (0 : Space) D.radius_pos] with a ha
    exact (hasFDerivAt_value hf hpos D ha).differentiableAt
  have hH := hasFDerivAt_fderiv_value hf hpos D (mem_ball_self D.radius_pos)
  rw [← hH.fderiv] at hH
  have ht := tendsto_average3_div_sq_trace ell hd hH (value_zero f μ)
    (KLHessian.fderiv_value_zero hf hpos D (boundary_all_directions hf hpos D hfirst))
  have he (i : Fin 3) :
      fderiv ℝ (fderiv ℝ (value f μ)) 0 (Pi.single i 1) (Pi.single i 1) =
        fisherMatrix f coordinate μ i i :=
    KLHessian.hessian_eq_fisherMatrix hf hpos D coordinate i i
      (hFisher i) (hSecond i) (hsecond i)
  simp_rw [he] at ht
  rw [← fisherTrace_eq_sum_diagonal f coordinate μ hFisher] at ht
  exact ht

/-- The genuine translated KL density is integrable for all sufficiently
small scaled probes, uniformly in their three phase representatives. -/
theorem eventually_integrable_probe_kl (ell : ℝ) {f : Space → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure Space} {r : ℝ} (D : Domination f μ r) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ θ, Integrable (integrand f (ε • displacement ell θ)) μ := by
  filter_upwards [eventually_scaled_displacement_mem ell
    (ball_mem_nhds (0 : Space) D.radius_pos)] with ε hε
  exact fun θ => integrable_integrand hf hpos D (hε θ)

/-- The actual KL values are genuinely integrable at every stage of the
threefold phase average for every sufficiently small probe scale. -/
theorem eventually_iteratedIntegrable_probe_kl (ell : ℝ) {f : Space → ℝ}
    (hf : ContDiff ℝ 2 f) (hpos : ∀ x, 0 < f x)
    {μ : Measure Space} {r : ℝ} (D : Domination f μ r) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      IteratedIntegrable (fun θ => value f μ (ε • displacement ell θ)) := by
  have hc : ∀ᶠ a in 𝓝 (0 : Space), ContinuousAt (value f μ) a := by
    filter_upwards [ball_mem_nhds (0 : Space) D.radius_pos] with a ha
    exact (hasFDerivAt_value hf hpos D ha).continuousAt
  exact (eventually_continuous_probe ell hc).mono
    (fun _ h => iteratedIntegrable_of_continuous h)

/-- Constant spatial normalization preserves actual C2 density regularity. -/
theorem contDiff_normalizedDensity {ρ : Space → ℝ} (hρ : ContDiff ℝ 2 ρ) (Z : ℝ) :
    ContDiff ℝ 2 (normalizedDensity ρ Z) := by
  change ContDiff ℝ 2 (fun x => ρ x / Z)
  simpa only [div_eq_mul_inv] using hρ.mul (contDiff_const (c := Z⁻¹))

/-- Finite auxiliary Fisher entries imply finite physical entries by the
proved score normalization, with no extra finiteness assumption on the physical trace. -/
theorem integrable_physical_matrix {ρ : Space → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (μ : Measure Space) (i j : Fin 3)
    (hint : Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i j) μ) :
    Integrable (matrixIntegrand ρ coordinate i j) μ := by
  have he : matrixIntegrand ρ coordinate i j =
      fun x => Z * matrixIntegrand (normalizedDensity ρ Z) coordinate i j x := by
    funext x
    rw [matrixIntegrand_normalizedDensity (hρ x) (hpos x) hZ]
    field_simp
  rw [he]
  exact hint.const_mul Z

/-- The actual averaged KL limit for the normalized auxiliary density has
exactly the physical hbar-squared-over-four homogeneous Fisher coefficient. -/
theorem tendsto_normalized_clock_kl (p : MassiveParameters) {ρ : Space → ℝ} {Z : ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    {μ : Measure Space} {r : ℝ} (D : Domination (normalizedDensity ρ Z) μ r)
    (hfirst : ∀ i, (∫ x, fderiv ℝ (normalizedDensity ρ Z) x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i i) μ)
    (hSecond : ∀ i, Integrable (fun x => fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i) ∂μ) = 0) :
    Tendsto (fun ε : ℝ => (Z * p.m ^ 2 * p.c ^ 2) *
      (average3 (fun θ => value (normalizedDensity ρ Z) μ (ε • displacement p.ellC θ)) / ε ^ 2))
      (𝓝[≠] 0) (𝓝 (p.hbar ^ 2 / 4 * fisherTrace ρ coordinate μ)) := by
  have hf := contDiff_normalizedDensity hρ Z
  have hp := fun x => normalizedDensity_pos ρ hZ (hpos x)
  have ht := (tendsto_averaged_kl p.ellC hf hp D hfirst hFisher hSecond hsecond).const_mul
    (Z * p.m ^ 2 * p.c ^ 2)
  have hdi := hρ.differentiable (by norm_num)
  have hi i := integrable_physical_matrix hdi hpos hZ μ i i (hFisher i)
  have htrace := integrable_trace_of_diagonal ρ coordinate μ hi
  have hc : Z * p.m ^ 2 * p.c ^ 2 *
      (p.ellC ^ 2 / 4 * fisherTrace (normalizedDensity ρ Z) coordinate μ) =
      p.hbar ^ 2 / 4 * fisherTrace ρ coordinate μ := by
    calc
      _ = p.hbar ^ 2 / 4 * (Z * fisherTrace (normalizedDensity ρ Z) coordinate μ) := by
        unfold MassiveParameters.ellC
        have hm := p.m_pos.ne'
        have hcp := p.c_pos.ne'
        field_simp
      _ = _ := by rw [mass_mul_fisherTrace_normalizedDensity hdi hpos hZ coordinate μ htrace]
  rwa [hc] at ht

/-- With Z equal to the actual finite positive mass, the source auxiliary
density has unit mass and its genuine averaged KL limit is the physical Fisher functional. -/
theorem probability_clock_kl_limit (p : MassiveParameters) {ρ : Space → ℝ} {Z : ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    {μ : Measure Space} {r : ℝ} (D : Domination (normalizedDensity ρ Z) μ r)
    (hmassInt : Integrable ρ μ) (hmass : (∫ x, ρ x ∂μ) = Z)
    (hfirst : ∀ i, (∫ x, fderiv ℝ (normalizedDensity ρ Z) x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i i) μ)
    (hSecond : ∀ i, Integrable (fun x => fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i) ∂μ) = 0) :
    (∫ x, normalizedDensity ρ Z x ∂μ) = 1 ∧
      Tendsto (fun ε : ℝ => (Z * p.m ^ 2 * p.c ^ 2) *
        (average3 (fun θ => value (normalizedDensity ρ Z) μ (ε • displacement p.ellC θ)) / ε ^ 2))
        (𝓝[≠] 0) (𝓝 (p.hbar ^ 2 / 4 * fisherTrace ρ coordinate μ)) :=
  ⟨integral_normalizedDensity hmassInt hZ hmass,
    tendsto_normalized_clock_kl p hρ hpos hZ D hfirst hFisher hSecond hsecond⟩

/-- Spatial Lebesgue translation preserves genuine integrability of the
normalized auxiliary density. -/
theorem integrable_translated_density {ρ : Space → ℝ} (hρ : Integrable ρ)
    (Z : ℝ) (a : Space) : Integrable (fun x => normalizedDensity ρ Z (x + a)) :=
  (integrable_normalizedDensity hρ Z).comp_add_right a

/-- Every translated auxiliary density has unit spatial Lebesgue mass,
so the source compares two genuinely normalized density laws. -/
theorem integral_translated_density {ρ : Space → ℝ} {Z : ℝ} (hρ : Integrable ρ)
    (hZ : 0 < Z) (hmass : (∫ x, ρ x) = Z) (a : Space) :
    (∫ x, normalizedDensity ρ Z (x + a)) = 1 := by
  rw [integral_add_right_eq_self]
  exact integral_normalizedDensity hρ hZ hmass

/-- The source spatial Lebesgue formulation: every translated auxiliary
density is genuinely integrable with unit mass, and the actual clock-averaged
KL small-shift limit equals the physical homogeneous Fisher functional. -/
theorem spatial_probability_clock_kl_limit (p : MassiveParameters) {ρ : Space → ℝ} {Z : ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    {r : ℝ} (D : Domination (normalizedDensity ρ Z) volume r)
    (hmassInt : Integrable ρ) (hmass : (∫ x, ρ x) = Z)
    (hfirst : ∀ i, (∫ x, fderiv ℝ (normalizedDensity ρ Z) x (coordinate i)) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i i))
    (hSecond : ∀ i, Integrable (fun x => fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)))
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)) = 0) :
    (∀ a : Space, Integrable (fun x => normalizedDensity ρ Z (x + a)) ∧
      (∫ x, normalizedDensity ρ Z (x + a)) = 1) ∧
      Tendsto (fun ε : ℝ => (Z * p.m ^ 2 * p.c ^ 2) *
        (average3 (fun θ => value (normalizedDensity ρ Z) volume
          (ε • displacement p.ellC θ)) / ε ^ 2))
        (𝓝[≠] 0) (𝓝 (p.hbar ^ 2 / 4 * fisherTrace ρ coordinate volume)) :=
  ⟨fun a => ⟨integrable_translated_density hmassInt Z a,
      integral_translated_density hmassInt hZ hmass a⟩,
    tendsto_normalized_clock_kl p hρ hpos hZ D hfirst hFisher hSecond hsecond⟩

end FoliationQM.ClockKLLimit
