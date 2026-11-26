module

public import FoliationQM.GaussianFutureCurrentGeometry
public import FoliationQM.GaussianCompactOsmoticMargin

/-!
# Regional coercivity and the complete initial osmotic integral

The initial future region of the physical positive-frequency rest packet is an
open Euclidean ball. V13 Eq. 57 holds there at zero drift. On each smaller
closed ball a common laboratory interval preserves the phase chart, drift
cap and strict margins in Eqs. 57–58. The signed initial integral can also be
evaluated on both sides of the transition without dividing by the current.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianInteriorCoercivity

open LorentzCoordinates Set MeasureTheory GaussianFutureCurrentGeometry GaussianEuclideanRegions
open GaussianPacketPolarDomain GaussianPrescribedRegion GaussianPacketLaboratoryInterval
open OsmoticSliceFields ObserverFluxDensity SpacelikeOsmoticIntegral

private theorem volume_closed_pos {r : ℝ} (hr : 0 < r) : 0 < volume (closedRegion r) := by
  rw [volume_closed]
  positivity

/-- The entire open Euclidean future ball satisfies Eq. 57 with its exact initial
speed cap zero at every positive width. -/
theorem initial_open_ball (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    GaussianRegionalCoercivity.DilatationBoundOn p σ (openRegion (radius p σ)) 0 := by
  rw [← futureRegion_eq p hσ]
  exact GaussianRegionalCoercivity.strict_on_future_region p hσ

/-- Each prescribed inner closed ball retains its future chart, strict weighted
norm margin, subluminal drift supremum and half its initial negative signed
margin throughout one two-sided laboratory interval. -/
theorem inner_interval (p : MassiveParameters) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 0 < r) (hin : r < radius p σ) :
    let K := closedRegion r
    ∃ T : ℝ, 0 < T ∧ signedIntegral p σ 0 K / 2 < 0 ∧ ∀ τ ∈ Icc (-T) T,
      (∀ y ∈ K, slicePoint (p.c*τ) y ∈ GaussianPacketTimeRegularity.domain p σ) ∧
      scoreNorm p σ K 0 / 2 < scoreNorm p σ K τ ∧
      dilatationNorm p σ K τ < (p.c/4)*scoreNorm p σ K τ ∧
      (⨆ y : K, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint (p.c*τ) y.val))) ≤ p.c/2 ∧
      GaussianPacketTimeCoercivity.DilatationBoundOn p σ (p.c*τ) K (p.c/2) ∧
      signedIntegral p σ (p.c*τ) K < signedIntegral p σ 0 K / 2 := by
  let K := closedRegion r
  have hf : K ⊆ GaussianRegionalCoercivity.futureRegion p σ := by
    rw [futureRegion_eq p hσ]
    exact fun _ hy => lt_of_le_of_lt hy hin
  obtain ⟨A,hA,weighted⟩ := interval p hσ (compact_closed r) (volume_closed_pos hr) hf
  obtain ⟨B,hB,hneg,signed⟩ := GaussianCompactOsmoticMargin.uniform_signed_margin
    p hσ (compact_closed r) (volume_closed_pos hr) hf
  obtain ⟨C,hC,tube⟩ := GaussianCompactFutureTube.exists_tube p hσ (compact_closed r) hf
  let T := min A (min B C)
  refine ⟨T, lt_min hA (lt_min hB hC), hneg, fun τ hτ => ?_⟩
  have sub {d : ℝ} (hd : T ≤ d) : τ ∈ Icc (-d) d :=
    ⟨(neg_le_neg hd).trans hτ.1, hτ.2.trans hd⟩
  have w := weighted τ (sub (min_le_left _ _))
  exact ⟨tube.in_domain τ (sub ((min_le_right A _).trans (min_le_right B C))),
    w.1, w.2.1, w.2.2.1, w.2.2.2.1, signed τ (sub ((min_le_right A _).trans (min_le_left B C)))⟩

/-- Both the closed initial ball and its infinite-volume exterior have strictly
negative signed osmotic integrals. They sum to the exact full-slice Fisher value. -/
theorem initial_signed_split (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    let r := radius p σ
    let K := closedRegion r
    let E := {y : Spatial | r < euclideanSpeed y}
    signedIntegral p σ 0 K < 0 ∧ signedIntegral p σ 0 E < 0 ∧
      signedIntegral p σ 0 K + signedIntegral p σ 0 E =
        -(p.hbar^2/4) * (GaussianSliceMoments.normalization σ * (3/σ^2)) := by
  let r := radius p σ
  let E := {y : Spatial | r < euclideanSpeed y}
  have hE : E = (closedRegion r)ᶜ := by ext y; simp [E, closedRegion]
  have hv : 0 < volume E := by rw [show volume E = ⊤ from volume_exterior r]; exact ENNReal.zero_lt_top
  refine ⟨GaussianPacketOsmoticIntegral.integral_neg_on p hσ (volume_closed_pos (radius_pos p hσ)),
    GaussianPacketOsmoticIntegral.integral_neg_on p hσ hv, ?_⟩
  change (∫ y in closedRegion r, GaussianPacketOsmoticIntegral.integrand p σ y) +
    (∫ y in E, GaussianPacketOsmoticIntegral.integrand p σ y) = _
  rw [hE, integral_add_compl (compact_closed r).measurableSet (GaussianPacketOsmoticIntegral.integrable_signed p hσ)]
  exact GaussianPacketOsmoticIntegral.whole_slice p hσ

end FoliationQM.GaussianInteriorCoercivity
