module

public import FoliationQM.GaussianCenterFrequencyVariance
public import FoliationQM.GaussianPacketParity
public import FoliationQM.GaussianPacketLaboratoryInterval
public import FoliationQM.CanonicalScalarEnergy

/-!
# Central normal score and dilatation at the onset of free Gaussian evolution

The variance of the massive frequency fixes the curvature of the density
trace in the normal coordinate s. At the spatial center its log derivative
is the normal score N. The transport law gives the full dilatation −cN
there. Differentiating in physical laboratory time τ, with s=cτ, gives
strict and opposite onset rates for the quantities in v13 lines 754–767.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCenterDilatation

open Filter LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeRegularity
open GaussianCenterFrequencyVariance OsmoticSliceFields
open scoped Topology

private theorem continuous_center : Continuous (fun s : ℝ => slicePoint s (0 : Spatial)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> first | exact continuous_id | exact continuous_const

private theorem near_domain (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ s : ℝ in 𝓝 0, slicePoint s 0 ∈ domain p σ :=
  continuous_center.continuousAt <| (isOpen_domain p hσ).mem_nhds
    (slice_mem_domain p hσ 0 (GaussianRegionalCoercivity.center_mem_futureRegion p hσ))

private theorem trace_derivative (f : Covector → ℝ) (s : ℝ)
    (hf : DifferentiableAt ℝ f (slicePoint s 0)) :
    HasDerivAt (fun t => f (slicePoint t 0)) (fderiv ℝ f (slicePoint s 0) (Madelung.coordinateVector 0)) s := by
  have h : DifferentiableAt ℝ f (slicePoint (1*s) 0) := by simpa using hf
  simpa only [one_mul, one_smul] using CanonicalScalarEnergy.labTime_derivative 1 (0 : Spatial) h

/-- On the regular central trace the actual normal log-density score is the ratio
of the normal-time derivative of the packet density to its value. -/
theorem score_eq_trace_ratio (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (s : ℝ)
    (hx : slicePoint s 0 ∈ domain p σ) :
    let r := centerDensity (p.m*p.c/p.hbar) σ
    normalScore (density p σ) (slicePoint s 0) = deriv r s / r s := by
  let r := centerDensity (p.m*p.c/p.hbar) σ
  have hf := fields p hσ hx
  have hr := trace_derivative (density p σ) s (hf.density_smooth.differentiableAt (by simp))
  have hd : HasDerivAt r (deriv r s) s := hr.differentiableAt.hasDerivAt
  have hp : r s ≠ 0 := hf.density_pos.ne'
  have hl := trace_derivative (fun x => Real.log (density p σ x)) s
    ((hf.density_smooth.log hf.density_pos.ne').differentiableAt (by simp))
  exact hl.unique (hd.log hp)

/-- The full material dilatation on the future central trace equals −c times
the normal score, since spatial reflection forces the spatial score to vanish. -/
theorem center_balance (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (s : ℝ)
    (hx : slicePoint s 0 ∈ domain p σ) :
    dilatation p.c (action p σ) (slicePoint s 0) = -p.c * normalScore (density p σ) (slicePoint s 0) := by
  have hb := normal_balance p.c_pos (GaussianPacketLaboratoryInterval.transport p hσ hx)
  rw [GaussianPacketParity.center_spatial_score p hσ s] at hb
  simp only [spatialDot, Pi.zero_apply, mul_zero, add_zero, neg_zero, zero_sub] at hb
  linarith

private theorem normal_time_onset (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => normalScore (density p σ) (slicePoint s 0))
      (-2*variance (p.m*p.c/p.hbar) σ) 0 := by
  let μ := p.m*p.c/p.hbar
  have hR : centerDensity μ σ 0 = 1 := by
    change Complex.normSq (GaussianPositiveFrequencyPacket.packet μ σ (slicePoint 0 0)) = 1
    rw [GaussianPositiveFrequencyPacket.initial_value μ hσ]
    simp [GaussianCauchySlice.amplitude, speedSq, spatialDot]
  have h := (hasDerivAt_deriv_centerDensity_zero μ hσ).div (hasDerivAt_centerDensity_zero μ hσ)
    (hR ▸ one_ne_zero)
  simp only [hR, mul_one, mul_zero, sub_zero, one_pow, div_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [near_domain p hσ] with s hs
  exact score_eq_trace_ratio p hσ s hs

/-- In laboratory time the central normal score has onset derivative −2c Var(Ω). -/
theorem lab_score_onset (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun t => normalScore (density p σ) (slicePoint (p.c*t) 0))
      (-2*p.c*variance (p.m*p.c/p.hbar) σ) 0 := by
  have hc := (hasDerivAt_id (0 : ℝ)).const_mul p.c
  have h := (normal_time_onset p hσ).comp_of_eq (x := 0) hc (by simp)
  convert h using 1 <;> simp [Function.comp_def, mul_assoc, mul_comm]

/-- In laboratory time the central full dilatation has onset derivative
2c² Var(Ω), with both factors of c coming from the physical source conventions. -/
theorem lab_dilatation_onset (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun t => dilatation p.c (action p σ) (slicePoint (p.c*t) 0))
      (2*p.c^2*variance (p.m*p.c/p.hbar) σ) 0 := by
  have hc : Tendsto (fun t : ℝ => p.c*t) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_id (α := ℝ) (x := 𝓝 0))
  have h := (lab_score_onset p hσ).const_mul (-p.c)
  rw [show -p.c * (-2*p.c*variance (p.m*p.c/p.hbar) σ) = 2*p.c^2*variance (p.m*p.c/p.hbar) σ by ring] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hc (near_domain p hσ)] with t ht
  exact center_balance p hσ _ ht

private theorem score_signs (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    (∀ᶠ t : ℝ in 𝓝[>] 0, normalScore (density p σ) (slicePoint (p.c*t) 0) < 0) ∧
    (∀ᶠ t : ℝ in 𝓝[<] 0, 0 < normalScore (density p σ) (slicePoint (p.c*t) 0)) := by
  let f := fun t => normalScore (density p σ) (slicePoint (p.c*t) 0)
  have hf : f 0 = 0 := by simp [f, GaussianPacketPolarDomain.normal_score p hσ]
  have hneg : -2*p.c*variance (p.m*p.c/p.hbar) σ < 0 := by
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) p.c_pos)
      (variance_pos (p.m*p.c/p.hbar) hσ)
  obtain ⟨hl, hr⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp (lab_score_onset p hσ)
  constructor
  · filter_upwards [hr.eventually_lt_const hneg, self_mem_nhdsWithin] with t hs ht
    change slope f 0 t < 0 at hs
    change 0 < t at ht
    rw [slope_def_field, hf, sub_zero, sub_zero] at hs
    rcases div_neg_iff.mp hs with hh | hh <;> linarith [hh.1, hh.2]
  · filter_upwards [hl.eventually_lt_const hneg, self_mem_nhdsWithin] with t hs ht
    change slope f 0 t < 0 at hs
    change t < 0 at ht
    rw [slope_def_field, hf, sub_zero, sub_zero] at hs
    rcases div_neg_iff.mp hs with hh | hh <;> linarith [hh.1, hh.2]

private theorem lab_domain (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ t : ℝ in 𝓝 0, slicePoint (p.c*t) 0 ∈ domain p σ := by
  have hc : Tendsto (fun t : ℝ => p.c*t) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_id (α := ℝ) (x := 𝓝 0))
  exact hc (near_domain p hσ)

/-- At all sufficiently small positive laboratory times the center is future-timelike,
has zero spatial score, has negative normal score and has strictly positive dilatation. -/
theorem eventually_positive_time (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, let x := slicePoint (p.c*t) 0
      x ∈ domain p σ ∧ spatialScore (density p σ) x = 0 ∧ normalScore (density p σ) x < 0 ∧
        0 < dilatation p.c (action p σ) x := by
  filter_upwards [(lab_domain p hσ).filter_mono nhdsWithin_le_nhds, (score_signs p hσ).1] with t hx hn
  refine ⟨hx, GaussianPacketParity.center_spatial_score p hσ _, hn, ?_⟩
  rw [center_balance p hσ _ hx]
  exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr p.c_pos) hn

/-- At all sufficiently small negative laboratory times the same future center
has positive normal score and strictly negative dilatation. -/
theorem eventually_negative_time (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ t : ℝ in 𝓝[<] 0, let x := slicePoint (p.c*t) 0
      x ∈ domain p σ ∧ spatialScore (density p σ) x = 0 ∧ 0 < normalScore (density p σ) x ∧
        dilatation p.c (action p σ) x < 0 := by
  filter_upwards [(lab_domain p hσ).filter_mono nhdsWithin_le_nhds, (score_signs p hσ).2] with t hx hn
  refine ⟨hx, GaussianPacketParity.center_spatial_score p hσ _, hn, ?_⟩
  rw [center_balance p hσ _ hx]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr p.c_pos) hn

end FoliationQM.GaussianCenterDilatation
