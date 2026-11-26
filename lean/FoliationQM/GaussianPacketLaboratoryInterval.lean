module

public import FoliationQM.GaussianPacketTimeCoercivity

/-!
# The signed osmotic integral on a fixed laboratory cylinder

V13 Eqs. 57–58 concern the material dilatation and the integrated Minkowski
square of the physical osmotic momentum. We use x⁰=cτ to give the same
fixed region for every laboratory time τ in a two-sided interval.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketLaboratoryInterval

open MeasureTheory LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeWindow
open OsmoticSliceFields ObserverFluxDensity GaussianPacketTimeCoercivity SpacelikeOsmoticIntegral

/-- The actual signed integral in Eq. 58 on a spatial region at normal time s=cτ. -/
def signedIntegral (p : MassiveParameters) (σ s : ℝ) (A : Set Spatial) : ℝ :=
  ∫ y in A, density p σ (slicePoint s y) *
    minkowski (infoMomentum p (density p σ) (slicePoint s y))
      (infoMomentum p (density p σ) (slicePoint s y))

/-- The massive spacetime equation yields the source's logarithmic transport
formulas at every point of the packet's regular future chart. -/
theorem transport (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {x : Covector}
    (hx : x ∈ GaussianPacketTimeRegularity.domain p σ) :
    NormalLogDensity.Formulas p.c (density p σ) (action p σ) x := by
  have hf := GaussianPacketTimeRegularity.fields p hσ hx
  apply NormalLogDensity.of_klein_gordon p (hf.density_smooth.of_le (by simp))
    (hf.action_smooth.of_le (by simp)) hf.density_pos hf.normal_pos
  rw [GaussianGlobalCauchyData.reconstruct]
  exact GaussianPositiveFrequencyPacket.massive_klein_gordon p hσ x

/-- On each compact positive-volume slice carrying the window bounds,
the original density-weighted osmotic Minkowski square is strictly negative. -/
theorem signed_negative (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (s : ℝ)
    {A : Set Spatial} (hA : IsCompact A) (hvA : 0 < volume A)
    (hb : ∀ y ∈ A, PointBounds p σ (slicePoint s y)) : signedIntegral p σ s A < 0 := by
  have hm := hA.measurableSet
  have hi := integrable_squares p σ s hA hb
  have hc := (SpatialFisherEnergy.contDiff_slicePoint s 1).continuous
  have hn : ContinuousOn (fun y => density p σ (slicePoint s y) *
      normalScore (density p σ) (slicePoint s y)^2) A := by
    intro y hy
    exact (((hb y hy).density_smooth.continuousAt.comp hc.continuousAt).mul
      (((hb y hy).normal_score_smooth.continuousAt.comp hc.continuousAt).pow 2)).continuousWithinAt
  apply (integral_spacelike p (density p σ) (action p σ) s A (V := p.c/2)
    (by linarith [p.c_pos]) (by linarith [p.c_pos])
    ((ae_restrict_iff' hm).mpr (ae_of_all _ fun y hy => (hb y hy).density_pos.le))
    ((ae_restrict_iff' hm).mpr (ae_of_all _ fun y hy => transport p hσ (hb y hy).mem_domain))
    ((ae_restrict_iff' hm).mpr (ae_of_all _ fun y hy => (hb y hy).speed_lt.le))
    (hn.aestronglyMeasurable hm) hi.1 hi.2
    (strict_on_subset p σ s hA hb hm Set.Subset.rfl hvA).2).2

/-- At every positive width there is one fixed positive-volume closed spatial
ball and a positive laboratory duration. Throughout that interval the physical
drift has supremum at most c/2, Eq. 57 holds and the signed Eq. 58 integral is negative. -/
theorem exists_laboratory_interval (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (y₀ : Spatial) (r T : ℝ), 0 < r ∧ 0 < T ∧ 0 < volume (Metric.closedBall y₀ r) ∧
      ∀ τ ∈ Set.Icc (-T) T,
        let s := p.c*τ
        let A := Metric.closedBall y₀ r
        (⨆ y : A, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint s y.val))) ≤ p.c/2 ∧
          DilatationBoundOn p σ s A (p.c/2) ∧ signedIntegral p σ s A < 0 := by
  obtain ⟨y₀,r,hr,hw⟩ := exists_window p hσ
  have hv := Metric.measure_closedBall_pos (volume : Measure Spatial) y₀ hr
  refine ⟨y₀,r,r/p.c,hr,div_pos hr p.c_pos,hv,fun τ ht => ?_⟩
  have hs : p.c*τ ∈ Set.Icc (-r) r := by
    have h1 := mul_le_mul_of_nonneg_left ht.1 p.c_pos.le
    have h2 := mul_le_mul_of_nonneg_left ht.2 p.c_pos.le
    have he : p.c * (r/p.c) = r := by field_simp [p.c_pos.ne']
    rw [mul_neg, he] at h1
    rw [he] at h2
    exact ⟨h1,h2⟩
  have hb := hw (p.c*τ) hs
  have h := strict_on_subset p σ (p.c*τ) (isCompact_closedBall y₀ r) hb
    Metric.isClosed_closedBall.measurableSet Set.Subset.rfl hv
  exact ⟨h.1,h.2,signed_negative p hσ _ (isCompact_closedBall y₀ r) hv hb⟩

end FoliationQM.GaussianPacketLaboratoryInterval
