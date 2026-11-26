module

public import FoliationQM.TwoBodyActionDensity
public import FoliationQM.TwoBodyMarginalContinuity

/-!
# Polar two-body continuity and its compact-test identity

The divergence of the six mass-weighted polar currents in v13
`eq:2p_continuity` agrees with the physical wave-current divergence.
The density-square expansion also holds at zeros of the amplitude.
Compactly supported phase tests transfer the derivatives from all seven
current components onto the test function by integration by parts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyPolarContinuity

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyPolarWave
open scoped BigOperators Topology

/-- One Cartesian component of the polar particle current. -/
def flux (m₁ m₂ : ℝ) (ρ S : Point → ℝ) (j : Index) (p : Point) : ℝ :=
  (ρ p / mass m₁ m₂ j) * D (axis j) S p

/-- The two-body continuity residual as one sum over the six spatial coordinates. -/
def continuity (m₁ m₂ : ℝ) (ρ S : Point → ℝ) (p : Point) : ℝ :=
  Dt ρ p + ∑ j, D (axis j) (flux m₁ m₂ ρ S j) p

/-- Separating the left and right currents gives the residual used for marginal projection. -/
theorem continuity_eq_residual (m₁ m₂ : ℝ) (ρ S : Point → ℝ) (p : Point) :
    continuity m₁ m₂ ρ S p = TwoBodyMarginalContinuity.residual ρ
      (fun i => flux m₁ m₂ ρ S (.inl i)) (fun i => flux m₁ m₂ ρ S (.inr i)) p := by
  simp only [continuity, TwoBodyMarginalContinuity.residual, Fintype.sum_sum_type, axis,
    Sum.elim_inl, Sum.elim_inr, D₁, D₂, add_assoc]

/-- In both spatial sectors the wave current agrees with the corresponding polar flux. -/
theorem wave_current_eq_flux {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) {R S : Point → ℝ} {p : Point}
    (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p) (j : Index) :
    (h / mass m₁ m₂ j) * (star (wave h R S p) * D (axis j) (wave h R S) p).im =
      flux m₁ m₂ (fun z => R z ^ 2) S j p := current_eq hh _ hR hS _

/-- The wave-density residual in the marginal theorem equals the polar residual, with the
actual divergence applied to both wave currents at the point. -/
theorem wave_residual_eq {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) {R S : Point → ℝ} {p : Point}
    (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p) :
    TwoBodyMarginalContinuity.residual (fun z => ‖wave h R S z‖ ^ 2)
      (fun i z => (h/m₁) * (star (wave h R S z) * D₁ i (wave h R S) z).im)
      (fun i z => (h/m₂) * (star (wave h R S z) * D₂ i (wave h R S) z).im) p =
      continuity m₁ m₂ (fun z => R z ^ 2) S p := by
  have hj (j : Index) :
      (fun z => (h/mass m₁ m₂ j) * (star (wave h R S z) * D (axis j) (wave h R S) z).im)
        =ᶠ[𝓝 p] flux m₁ m₂ (fun z => R z ^ 2) S j := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hR,
      PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hS] with q hq hq'
    exact wave_current_eq_flux hh m₁ m₂ hq hq' j
  have hd (j : Index) := congrArg (fun L : Point →L[ℝ] ℝ => L (axis j)) (hj j).fderiv_eq
  rw [continuity_eq_residual]
  simp only [born, TwoBodyMarginalContinuity.residual]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => hd (.inl i)
  · exact Finset.sum_congr rfl fun i _ => hd (.inr i)

private theorem D_sq {R : Point → ℝ} {p : Point} (hR : DifferentiableAt ℝ R p) (v : Point) :
    D v (fun z => R z ^ 2) p = 2 * R p * D v R p := by
  simp only [D, pow_two, fderiv_fun_mul hR hR, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The actual product rule for the divergence of one polar component of a squared amplitude. -/
theorem flux_sq_derivative (m₁ m₂ : ℝ) {R S : Point → ℝ} {p : Point}
    (hR : DifferentiableAt ℝ R p) (hS : ContDiffAt ℝ 2 S p) (j : Index) :
    D (axis j) (flux m₁ m₂ (fun z => R z ^ 2) S j) p =
      (2 * R p * D (axis j) R p * D (axis j) S p +
        (R p)^2 * D (axis j) (D (axis j) S) p) / mass m₁ m₂ j := by
  have hs : DifferentiableAt ℝ (D (axis j) S) p :=
    ((hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  let A := fun z => R z ^ 2 / mass m₁ m₂ j
  have ha : DifferentiableAt ℝ A p := by
    unfold A
    fun_prop
  change fderiv ℝ (fun z => A z * D (axis j) S z) p (axis j) = _
  rw [fderiv_fun_mul ha hs]
  simp only [add_apply, smul_apply, smul_eq_mul, A, div_eq_mul_inv, fderiv_mul_const (c := fun z => R z ^ 2) (hR.pow 2)]
  have h := D_sq hR (axis j)
  unfold D at h ⊢
  rw [h]
  ring

/-- Expanding continuity for the Born density requires no division by the amplitude. -/
theorem continuity_sq (m₁ m₂ : ℝ) {R S : Point → ℝ} {p : Point}
    (hR : DifferentiableAt ℝ R p) (hS : ContDiffAt ℝ 2 S p) :
    continuity m₁ m₂ (fun z => R z ^ 2) S p =
      2 * R p * Dt R p + ∑ j, (2 * R p * D (axis j) R p * D (axis j) S p +
        (R p)^2 * D (axis j) (D (axis j) S) p) / mass m₁ m₂ j := by
  simp only [continuity, Dt, D_sq hR, flux_sq_derivative m₁ m₂ hR hS]

/-- With a C¹ density and C² phase, each polar current is continuously differentiable. -/
theorem contDiff_flux (m₁ m₂ : ℝ) {ρ S : Point → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hS : ContDiff ℝ 2 S) (j : Index) : ContDiff ℝ 1 (flux m₁ m₂ ρ S j) :=
  (hρ.div_const _).mul ((hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)

private theorem compact_pair {f g : Point → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hg : Continuous g) :
    Integrable (fun p => f p * g p) :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_right

private theorem D_continuous {f : Point → ℝ} (hf : ContDiff ℝ 1 f) (v : Point) :
    Continuous (D v f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The nested product Lebesgue volume on joint spacetime is additive Haar measure. -/
theorem volume_isAddHaarMeasure : (volume : Measure Point).IsAddHaarMeasure := by
  change Measure.IsAddHaarMeasure (((volume : Measure ℝ).prod
    (volume : Measure LorentzCoordinates.Spatial)).prod (volume : Measure LorentzCoordinates.Spatial))
  let μ := (volume : Measure ℝ).prod (volume : Measure LorentzCoordinates.Spatial)
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure μ _

/-- A compact C¹ test can be integrated by parts against any C¹ real current component. -/
theorem compact_test_parts {η g : Point → ℝ} (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hg : ContDiff ℝ 1 g) (v : Point) :
    (∫ p, η p * D v g p) = -(∫ p, D v η p * g p) := by
  let := volume_isAddHaarMeasure
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (compact_pair (D_continuous hη v) (hc.fderiv_apply ℝ v) hg.continuous)
    (compact_pair hη.continuous hc (D_continuous hg v))
    (compact_pair hη.continuous hc hg.continuous)
    (fun x _ => hη.differentiable (by norm_num) x) (fun x _ => hg.differentiable (by norm_num) x)

/-- Testing the full continuity residual transfers the time and both particles' spatial
derivatives to the compactly supported test. All products are genuinely integrable. -/
theorem continuity_test (m₁ m₂ : ℝ) {ρ S η : Point → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hS : ContDiff ℝ 2 S) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    (∫ p, η p * continuity m₁ m₂ ρ S p) =
      -(∫ p, Dt η p * ρ p + ∑ j, D (axis j) η p * flux m₁ m₂ ρ S j p) := by
  have hf := contDiff_flux m₁ m₂ hρ hS
  have h₁ (v : Point) (g : Point → ℝ) (hg : ContDiff ℝ 1 g) :
      Integrable (fun p => η p * D v g p) :=
    compact_pair hη.continuous hc (D_continuous hg v)
  have h₂ (v : Point) (g : Point → ℝ) (hg : ContDiff ℝ 1 g) :
      Integrable (fun p => D v η p * g p) :=
    compact_pair (D_continuous hη v) (hc.fderiv_apply ℝ v) hg.continuous
  simp only [continuity, Dt, mul_add, Finset.mul_sum]
  rw [integral_add (h₁ timeAxis ρ hρ) (integrable_finsetSum _ fun j _ => h₁ (axis j) _ (hf j)),
    integral_add (h₂ timeAxis ρ hρ) (integrable_finsetSum _ fun j _ => h₂ (axis j) _ (hf j)),
    integral_finsetSum _ (fun j _ => h₁ (axis j) _ (hf j)),
    integral_finsetSum _ (fun j _ => h₂ (axis j) _ (hf j))]
  simp only [compact_test_parts hη hc hρ, fun j => compact_test_parts hη hc (hf j) (axis j),
    Finset.sum_neg_distrib, neg_add_rev, add_comm]

end FoliationQM.TwoBodyPolarContinuity
