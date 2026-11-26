module

public import FoliationQM.GaussianPacketTimeWindow

/-!
# A fixed compact portion of the future phase chart over laboratory time

For v13 Theorem 5.8(ii), a compact part of the initial Gaussian future
region stays inside the regular chart with a subluminal cap over a common
two-sided time interval. The time coordinate of each event is x⁰=cτ.
The weighted moment integrands vary continuously across this compact strip.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCompactFutureTube

open Set Metric LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeRegularity
open OsmoticSliceFields ObserverFluxDensity
open scoped Topology

/-- The spacetime event with physical laboratory time τ and spatial coordinates y. -/
def sliceMap (p : MassiveParameters) (w : ℝ × Spatial) : Covector := slicePoint (p.c*w.1) w.2

/-- Laboratory time and spatial position jointly determine the event continuously. -/
theorem continuous_sliceMap (p : MassiveParameters) : Continuous (sliceMap p) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const.mul continuous_fst
  · exact (continuous_apply (0 : Fin 3)).comp continuous_snd
  · exact (continuous_apply (1 : Fin 3)).comp continuous_snd
  · exact (continuous_apply (2 : Fin 3)).comp continuous_snd

/-- Product of a closed symmetric laboratory-time interval and a fixed spatial set. -/
def strip (δ : ℝ) (K : Set Spatial) : Set (ℝ × Spatial) := Icc (-δ) δ ×ˢ K

/-- The future chart and the strict physical speed cap hold on the whole product.
The pointwise spatial Fisher score may vanish within the compact region. -/
structure Tube (p : MassiveParameters) (σ δ : ℝ) (K : Set Spatial) : Prop where
  in_domain : ∀ t ∈ Icc (-δ) δ, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ
  speed_lt : ∀ t ∈ Icc (-δ) δ, ∀ y ∈ K,
    euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint (p.c*t) y)) < p.c/2

private theorem open_slow_domain (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    IsOpen {x | x ∈ domain p σ ∧ euclideanSpeed (phaseDrift p.c (action p σ) x) < p.c/2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨hmem, hs⟩ := hx
  filter_upwards [(isOpen_domain p hσ).mem_nhds hmem,
    (fields p hσ hmem).speed_continuous.eventually (gt_mem_nhds hs)] with z hz hv
  exact ⟨hz,hv⟩

/-- Every compact part of the initial future-timelike region, including one
containing the packet center, admits a common strictly positive time radius
on which the actual chart persists with drift speed below c/2. -/
theorem exists_tube (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {K : Set Spatial}
    (hK : IsCompact K) (hfuture : K ⊆ GaussianRegionalCoercivity.futureRegion p σ) :
    ∃ δ : ℝ, 0 < δ ∧ Tube p σ δ K := by
  let U := {x | x ∈ domain p σ ∧ euclideanSpeed (phaseDrift p.c (action p σ) x) < p.c/2}
  have hU := (open_slow_domain p hσ).preimage (continuous_sliceMap p)
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ sliceMap p ⁻¹' U := by
    rintro ⟨t,y⟩ ⟨(rfl : t = 0),hy⟩
    change slicePoint (p.c*0) y ∈ domain p σ ∧ _ < _
    simp only [mul_zero]
    exact ⟨slice_mem_domain p hσ y (hfuture hy), by
      change euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint (p.c*0) y)) < p.c/2
      rw [mul_zero, drift_zero p hσ y]
      simpa [euclideanSpeed, speedSq, spatialDot] using half_pos p.c_pos⟩
  obtain ⟨A,B,hA,_,h0,hB,hAB⟩ := generalized_tube_lemma isCompact_singleton hK hU hsub
  obtain ⟨δ,hδ,hball⟩ := nhds_basis_closedBall.mem_iff.mp (hA.mem_nhds (singleton_subset_iff.mp h0))
  have point (t : ℝ) (ht : t ∈ Icc (-δ) δ) (y : Spatial) (hy : y ∈ K) :
      sliceMap p (t,y) ∈ U := by
    apply hAB
    exact ⟨hball (by simpa [Real.closedBall_eq_Icc] using ht), hB hy⟩
  exact ⟨δ,hδ,fun t ht y hy => (point t ht y hy).1,fun t ht y hy => (point t ht y hy).2⟩

/-- The packet modulus density at the chosen laboratory time and position. -/
def massWeight (p : MassiveParameters) (σ : ℝ) (w : ℝ × Spatial) : ℝ :=
  density p σ (sliceMap p w)

/-- The physical density times the square of the material dilatation. -/
def dilatationSquare (p : MassiveParameters) (σ : ℝ) (w : ℝ × Spatial) : ℝ :=
  massWeight p σ w * (dilatation p.c (action p σ) (sliceMap p w))^2

/-- The spatial Fisher contribution to the weighted comparison on each laboratory slice. -/
def spatialSquare (p : MassiveParameters) (σ : ℝ) (w : ℝ × Spatial) : ℝ :=
  massWeight p σ w * (euclideanSpeed (spatialScore (density p σ) (sliceMap p w)))^2

/-- The density-weighted square of the actual normal logarithmic derivative. -/
def normalSquare (p : MassiveParameters) (σ : ℝ) (w : ℝ × Spatial) : ℝ :=
  massWeight p σ w * (normalScore (density p σ) (sliceMap p w))^2

variable {I : Set ℝ} {K : Set Spatial}

/-- On a product in the future domain the modulus density varies jointly
continuously in laboratory time and spatial position. -/
theorem continuous_massWeight_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (hdom : ∀ t ∈ I, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ) :
    ContinuousOn (massWeight p σ) (I ×ˢ K) := by
  intro z hz
  exact ((fields p hσ (x := sliceMap p z) (hdom _ hz.1 _ hz.2)).density_smooth.continuousAt.comp
    (continuous_sliceMap p).continuousAt).continuousWithinAt

/-- The physical weighted dilatation integrand is jointly continuous on
each product contained in the regular future chart. -/
theorem continuous_dilatationSquare_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (hdom : ∀ t ∈ I, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ) :
    ContinuousOn (dilatationSquare p σ) (I ×ˢ K) := by
  intro z hz
  have hd := (fields p hσ (x := sliceMap p z) (hdom _ hz.1 _ hz.2)).dilatation_smooth.continuousAt.comp
    (continuous_sliceMap p).continuousAt
  exact (continuous_massWeight_on p hσ hdom z hz).mul (hd.continuousWithinAt.pow 2)

/-- The physical weighted spatial score square varies jointly continuously
on a future time-space product, including at points with vanishing gradient. -/
theorem continuous_spatialSquare_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (hdom : ∀ t ∈ I, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ) :
    ContinuousOn (spatialSquare p σ) (I ×ˢ K) := by
  intro z hz
  have hg := (fields p hσ (x := sliceMap p z) (hdom _ hz.1 _ hz.2)).score_continuous.comp (continuous_sliceMap p).continuousAt
  exact (continuous_massWeight_on p hσ hdom z hz).mul (hg.continuousWithinAt.pow 2)

/-- The physical normal weighted square varies jointly continuously throughout
each time-space product in the future chart. -/
theorem continuous_normalSquare_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (hdom : ∀ t ∈ I, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ) :
    ContinuousOn (normalSquare p σ) (I ×ˢ K) := by
  intro z hz
  have hn := (fields p hσ (x := sliceMap p z) (hdom _ hz.1 _ hz.2)).normal_score_smooth.continuousAt.comp
    (continuous_sliceMap p).continuousAt
  exact (continuous_massWeight_on p hσ hdom z hz).mul (hn.continuousWithinAt.pow 2)

/-- A continuous real observable admits a uniform absolute bound on a fixed
closed time interval times a compact spatial set. -/
theorem bounded_on_strip {δ : ℝ} {f : ℝ × Spatial → ℝ} (hK : IsCompact K)
    (hf : ContinuousOn f (strip δ K)) : ∃ M : ℝ, ∀ z ∈ strip δ K, |f z| ≤ M := by
  have hc : IsCompact (strip δ K) := isCompact_Icc.prod hK
  obtain ⟨M, hM⟩ := hc.bddAbove_image hf.abs
  exact ⟨M,fun z hz => hM ⟨z,hz,rfl⟩⟩

/-- All four physical integrands have a common finite bound across the compact
future tube. This controls their whole family of laboratory-time slices. -/
theorem bounded_weights (p : MassiveParameters) {σ δ : ℝ} (hσ : 0 < σ)
    (hK : IsCompact K) (htube : Tube p σ δ K) :
    ∃ M : ℝ, ∀ z ∈ strip δ K, |massWeight p σ z| ≤ M ∧ |dilatationSquare p σ z| ≤ M ∧
      |spatialSquare p σ z| ≤ M ∧ |normalSquare p σ z| ≤ M := by
  obtain ⟨m,hm⟩ := bounded_on_strip hK (continuous_massWeight_on p hσ htube.in_domain)
  obtain ⟨d,hd⟩ := bounded_on_strip hK (continuous_dilatationSquare_on p hσ htube.in_domain)
  obtain ⟨g,hg⟩ := bounded_on_strip hK (continuous_spatialSquare_on p hσ htube.in_domain)
  obtain ⟨n,hn⟩ := bounded_on_strip hK (continuous_normalSquare_on p hσ htube.in_domain)
  refine ⟨max (max m d) (max g n), fun z hz => ?_⟩
  exact ⟨(hm z hz).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hd z hz).trans ((le_max_right _ _).trans (le_max_left _ _)),
    (hg z hz).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hn z hz).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

end FoliationQM.GaussianCompactFutureTube
