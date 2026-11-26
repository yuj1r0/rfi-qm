module

public import FoliationQM.GaussianPacketPolarDomain
public import FoliationQM.GaussianRegionalCoercivity
public import FoliationQM.GaussianPacketCurrentSign

/-!
# The integrated osmotic momentum of the positive-frequency rest packet

For v13 Eq. 58 we compute the initial integral directly from the actual
density. The normal log-density derivative vanishes even where the temporal
phase momentum changes sign. The restricted osmotic integral is therefore
a negative constant times the genuinely spatial Gaussian Fisher integral.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketOsmoticIntegral

open LorentzCoordinates MeasureTheory OsmoticSliceFields GaussianPacketPolarDomain

/-- Density-weighted Minkowski square of the packet's lower osmotic momentum,
evaluated on its initial laboratory slice. -/
def integrand (p : MassiveParameters) (σ : ℝ) (y : Spatial) : ℝ :=
  density p σ (slicePoint 0 y) * minkowski (infoMomentum p (density p σ) (slicePoint 0 y))
    (infoMomentum p (density p σ) (slicePoint 0 y))

/-- The signed integrand is exactly the negative spatial Fisher term at every point,
including points where the temporal phase momentum vanishes. -/
theorem integrand_eq (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    integrand p σ y = -(p.hbar^2/4) * (GaussianSliceMoments.density σ y *
      speedSq (SpatialFisherEnergy.score (GaussianSliceMoments.density σ) y)) := by
  have hr : density p σ (slicePoint 0 y) = GaussianSliceMoments.density σ y :=
    congrFun (density_eq p hσ) y
  rw [integrand, info_square, hr, normal_score p hσ y, spatial_score p hσ y]
  ring

/-- The actual signed integrand is integrable on the entire initial slice. -/
theorem integrable_signed (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (integrand p σ) := by
  rw [funext (integrand_eq p hσ)]
  exact (GaussianSliceMoments.integrable_fisher hσ).const_mul _

/-- On each spatial region the integrated osmotic square equals −ℏ²/4 times
the restricted spatial Fisher integral, with the same physical density. -/
theorem integral_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (A : Set Spatial) :
    (∫ y in A, integrand p σ y) = -(p.hbar^2/4) *
      ∫ y in A, GaussianSliceMoments.density σ y *
        speedSq (SpatialFisherEnergy.score (GaussianSliceMoments.density σ) y) := by
  simp_rw [integrand_eq p hσ]
  exact integral_const_mul _ _

/-- Every region of positive spatial volume has a strictly negative integrated
osmotic square on this initial slice, regardless of the sign of its phase current. -/
theorem integral_neg_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial}
    (hA : 0 < volume A) : (∫ y in A, integrand p σ y) < 0 := by
  rw [integral_on p hσ]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)))
    (GaussianRegionalCoercivity.fisher_pos_on_of_volume_pos hσ hA)

/-- Over the complete initial slice the signed physical integral is
−(ℏ²/4) M (3/σ²), where M is the total Gaussian modulus mass. -/
theorem whole_slice (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    GaussianSliceCoercivity.signedIntegral p (density p σ) =
      -(p.hbar^2/4) * (GaussianSliceMoments.normalization σ * (3/σ^2)) := by
  change (∫ y, integrand p σ y) = _
  simp_rw [integrand_eq p hσ]
  rw [integral_const_mul, GaussianSliceMoments.integral_fisher hσ]

/-- At the physical width σ=ℓ_C the actual rest packet has past temporal current
on positive volume while its full initial osmotic integral is strictly negative. -/
theorem compton_current_and_integral (p : MassiveParameters) :
    0 < volume {y : Spatial |
      GaussianPacketCurrentSign.temporal p (p.m*p.c/p.hbar) p.ellC y < 0} ∧
      GaussianSliceCoercivity.signedIntegral p (density p p.ellC) < 0 := by
  have hμ : 0 < p.m*p.c/p.hbar := div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos
  have hs := ClockScales.ellC_pos p
  have hunit : p.ellC * (p.m*p.c/p.hbar) = 1 := by
    unfold MassiveParameters.ellC
    field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne']
  refine ⟨GaussianPacketCurrentSign.past_volume_at_compton p hμ hs hunit, ?_⟩
  rw [whole_slice p hs]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)))
    (mul_pos (GaussianSliceMoments.normalization_pos hs) (div_pos (by norm_num) (sq_pos_of_pos hs)))

/-- At one Compton width a point of strictly positive modulus density has
vanishing full four-current on the initial slice. -/
theorem compton_current_zero_at_positive_density (p : MassiveParameters) :
    ∃ y : Spatial, 0 < density p p.ellC (slicePoint 0 y) ∧
      ScalarPhaseCurrent.current p (wave p p.ellC) (slicePoint 0 y) = 0 := by
  have hμ := div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos
  have hs := ClockScales.ellC_pos p
  obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero (compton_current_and_integral p).1.ne'
  obtain ⟨t, _, ht, _⟩ := GaussianPacketCurrentSign.zero_on_segment p hμ hs hy
  refine ⟨t • y, (regularity p hs _).2.2, funext ?_⟩
  intro i
  exact Fin.cases ht (fun j => spatial_current p hs (t • y) j) i

end FoliationQM.GaussianPacketOsmoticIntegral
