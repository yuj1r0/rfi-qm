module

public import FoliationQM.TwoBodySpatialFisherBohm
public import FoliationQM.CompactPerturbation
public import FoliationQM.CompactParameterIntegral

/-!
# The Bohm potential as a derivative of the integrated two-particle Fisher energy

A compact density variation preserves strict positivity for a common interval
of parameters. On that interval the change of the Fisher integrand has compact
support. Differentiating its Lebesgue integral and applying spatial integration
by parts gives the two-body Bohm potential of v13 `eq:Q12_bohm`, both on the
configuration slice and inside the spacetime action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyFisherVariation

open MeasureTheory Filter Set LorentzCoordinates TwoBodyCoordinates TwoBodyActionDensity
open TwoBodyBohmGreen PolarSecondDifferential TwoBodySchrodingerResidual TwoBodySpatialFisherBohm
open TwoParticleFisher TwoBodyBohmFactors
open scoped Topology BigOperators

section General
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def affine (ρ a : X → ℝ) (t : ℝ) (p : X) := ρ p + t*a p

private def changeF (e : Index → X) (h m₁ m₂ : ℝ) (ρ a : X → ℝ) (t : ℝ) (p : X) :=
  fisherOn e h m₁ m₂ (affine ρ a t) p - fisherOn e h m₁ m₂ ρ p

private theorem dir_affine {ρ a : X → ℝ} (hρ : ContDiff ℝ 1 ρ) (ha : ContDiff ℝ 1 a)
    (p : X) (t : ℝ) (v : X) : directionalDerivative (affine ρ a t) v p =
      directionalDerivative ρ v p + t*directionalDerivative a v p := by
  have hdρ := hρ.differentiable (by decide) p
  have hda := ha.differentiable (by decide) p
  unfold affine
  simp only [directionalDerivative, fderiv_fun_add hdρ (hda.const_mul _),
    fderiv_const_mul hda, add_apply, smul_apply, smul_eq_mul]

private theorem continuous_data (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) :
    let U : Set ℝ := {t | ∀ p, 0 < affine ρ a t p}
    ContinuousOn (fun q : ℝ × X => changeF e h m₁ m₂ ρ a q.1 q.2) (U ×ˢ univ) ∧
    ContinuousOn (fun q : ℝ × X => rawVariationOn e h m₁ m₂ (affine ρ a q.1) a q.2) (U ×ˢ univ) := by
  intro U
  have dc (f : X → ℝ) (hf : ContDiff ℝ 1 f) (v : X) :
      Continuous (fun q : ℝ × X => directionalDerivative f v q.2) :=
    ((hf.continuous_fderiv (by decide)).clm_apply continuous_const).comp continuous_snd
  have dr (v : X) : Continuous (fun q : ℝ × X => directionalDerivative (affine ρ a q.1) v q.2) := by
    simp only [dir_affine hρ ha]
    exact (dc ρ hρ v).add (continuous_fst.mul (dc a ha v))
  have cr : Continuous (fun q : ℝ × X => affine ρ a q.1 q.2) :=
    (hρ.continuous.comp continuous_snd).add (continuous_fst.mul (ha.continuous.comp continuous_snd))
  have nz (q : ℝ × X) (hq : q ∈ U ×ˢ (univ : Set X)) : affine ρ a q.1 q.2 ≠ 0 := (hq.1 q.2).ne'
  constructor
  · unfold changeF fisherOn
    apply ContinuousOn.sub
    · exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
        (((dr (e j)).pow 2).continuousOn.div cr.continuousOn nz)
    · exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
        (((dc ρ hρ (e j)).pow 2).continuousOn.div (hρ.continuous.comp continuous_snd).continuousOn
          (fun q _ => (hp q.2).ne'))
  · unfold rawVariationOn
    apply continuousOn_finsetSum
    intro j _
    apply continuousOn_const.mul
    apply ContinuousOn.sub
    · exact ((continuous_const.mul (dr (e j))).mul
        (dc a ha (e j))).continuousOn.div cr.continuousOn nz
    · exact ((ha.continuous.comp continuous_snd).mul ((dr (e j)).pow 2)).continuousOn.div
        (cr.pow 2).continuousOn (fun q hq => pow_ne_zero _ (nz q hq))

private theorem outside (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (ha : ContDiff ℝ 1 a) (t : ℝ) {p : X} (hn : p ∉ tsupport a) :
    changeF e h m₁ m₂ ρ a t p = 0 ∧ rawVariationOn e h m₁ m₂ (affine ρ a t) a p = 0 := by
  have hz := image_eq_zero_of_notMem_tsupport hn
  have hv (v : X) : directionalDerivative a v p = 0 := by
    simp [directionalDerivative, fderiv_of_notMem_tsupport ℝ hn]
  simp [changeF, fisherOn, rawVariationOn, dir_affine hρ ha, affine, hz, hv]

private theorem positive_window {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    {t | ∀ p, 0 < affine ρ a t p} ∈ 𝓝 (0 : ℝ) := by
  obtain ⟨ε, hε, hεp⟩ := CompactPerturbation.exists_pos_affine hρ.continuous hp ha.continuous hc
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 hε)
    (fun t ht => hεp t (by simpa [Real.dist_eq] using ht))

variable [MeasureSpace X] [BorelSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]

omit [NormedSpace ℝ X] [MeasureSpace X] [BorelSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)] in
private theorem continuous_at_parameter {U : Set ℝ} {F : ℝ → X → ℝ}
    (cf : ContinuousOn (fun q : ℝ × X => F q.1 q.2) (U ×ˢ univ)) {t : ℝ} (ht : t ∈ U) :
    Continuous (F t) := by
  apply continuousOn_univ.mp
  exact cf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun p _ => ⟨ht, mem_univ p⟩)

omit [NormedSpace ℝ X] in
private theorem integrable_compact_change {f : X → ℝ} {K : Set X} (hk : IsCompact K)
    (hf : Continuous f) (hs : Function.support f ⊆ K) : Integrable f :=
  (integrableOn_iff_integrable_of_support_subset hs).mp (hf.continuousOn.integrableOn_compact hk)

private theorem integrable_change (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∀ᶠ t in 𝓝 0, Integrable (changeF e h m₁ m₂ ρ a t) := by
  let U := {t | ∀ p, 0 < affine ρ a t p}
  have hU : U ∈ 𝓝 0 := positive_window hρ hp ha hc
  filter_upwards [hU] with t ht
  have cf := (continuous_data e h m₁ m₂ hρ hp ha).1
  have cont := continuous_at_parameter (F := changeF e h m₁ m₂ ρ a) cf ht
  have supp : Function.support (changeF e h m₁ m₂ ρ a t) ⊆ tsupport a := by
    intro p hs
    by_contra hn
    exact hs (outside e h m₁ m₂ hρ ha t hn).1
  exact integrable_compact_change (K := tsupport a) hc cont supp

omit [MeasureSpace X] [BorelSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)] in
private theorem local_derivative (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (ha : ContDiff ℝ 1 a) (t : ℝ) (p : X) (hp : 0 < affine ρ a t p) :
    HasDerivAt (fun s => changeF e h m₁ m₂ ρ a s p)
      (rawVariationOn e h m₁ m₂ (affine ρ a t) a p) t :=
  (hasDerivAt_fisherOn_affine e h m₁ m₂ (hρ.differentiable (by decide) p)
    (ha.differentiable (by decide) p) t hp.ne').sub_const (fisherOn e h m₁ m₂ ρ p)

private theorem relative_derivative (e : Index → X) (h m₁ m₂ : ℝ) {ρ a : X → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    HasDerivAt (fun t => ∫ p, changeF e h m₁ m₂ ρ a t p)
      (∫ p, rawVariationOn e h m₁ m₂ ρ a p) 0 := by
  have hzero : affine ρ a 0 = ρ := by funext z; simp [affine]
  have cf0 : Integrable (changeF e h m₁ m₂ ρ a 0) := by
    unfold changeF
    rw [hzero]
    simp
  have H := CompactParameterIntegral.hasDerivAt_integral_of_compact_support
    (F := changeF e h m₁ m₂ ρ a) (F' := fun t => rawVariationOn e h m₁ m₂ (affine ρ a t) a)
    (positive_window hρ hp ha hc) (continuous_data e h m₁ m₂ hρ hp ha).1
    (continuous_data e h m₁ m₂ hρ hp ha).2 hc
    (fun t _ _ hn => (outside e h m₁ m₂ hρ ha t hn).2)
    (fun t ht p => local_derivative e h m₁ m₂ hρ ha t p (ht p)) cf0
  simpa only [hzero] using H.2
end General

/-- Relative changes in the spacetime Fisher integrand are absolutely integrable near zero. -/
theorem integrable_fisher_change (h m₁ m₂ : ℝ) {ρ a : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∀ᶠ t in 𝓝 0, Integrable (fun p => fisherL h m₁ m₂ (fun z => ρ z + t*a z) p -
      fisherL h m₁ m₂ ρ p) := integrable_change axis h m₁ m₂ hρ hp ha hc

/-- The directional derivative of the integrated relative spacetime Fisher term equals the
compact test paired with the two-body Bohm potential of the square-root amplitude. -/
theorem fisher_relative (h m₁ m₂ : ℝ) {ρ a : Point → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    HasDerivAt (fun t => ∫ p, fisherL h m₁ m₂ (fun z => ρ z + t*a z) p - fisherL h m₁ m₂ ρ p)
      (∫ p, a p * quantum h m₁ m₂ (fun z => √(ρ z)) p) 0 := by
  have hs : (fun p => (√(ρ p))^2) = ρ := funext fun p => Real.sq_sqrt (hp p).le
  have he := integral_rawVariation_sq h m₁ m₂ (hρ.sqrt fun p => (hp p).ne')
    (fun p => Real.sqrt_pos.2 (hp p)) ha hc
  rw [hs] at he
  exact (relative_derivative axis h m₁ m₂ (hρ.of_le (by norm_num)) hp ha hc).congr_deriv he

private theorem spatial_density_eventually (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∀ᶠ t in 𝓝 0, fisherOn spatialAxis h m₁ m₂ (fun z => ρ z + t*a z) =
      jointDensity h m₁ m₂ (fun z => ρ z + t*a z) := by
  obtain ⟨ε, hε, ht⟩ := CompactPerturbation.exists_pos_affine hρ.continuous hp ha.continuous hc
  filter_upwards [Metric.ball_mem_nhds 0 hε] with t h
  exact funext fun p => fisherOn_eq_jointDensity _ _ _
    ((hρ.differentiable (by decide) p).add ((ha.differentiable (by decide) p).const_mul t))
    (ht t (by simpa [Real.dist_eq] using h) p)

/-- Local integrability and the actual relative derivative of the measured
configuration-space score density, even without finite absolute Fisher energy. -/
theorem spatial_relative (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    (∀ᶠ t in 𝓝 0, Integrable (fun p => jointDensity h m₁ m₂ (fun z => ρ z + t*a z) p -
      jointDensity h m₁ m₂ ρ p)) ∧
    HasDerivAt (fun t => ∫ p, jointDensity h m₁ m₂ (fun z => ρ z + t*a z) p -
      jointDensity h m₁ m₂ ρ p)
      (∫ p, a p * configQ h m₁ m₂ (fun z => √(ρ z)) p.1 p.2) 0 := by
  have hr : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hi := integrable_change spatialAxis h m₁ m₂ hr hp ha hc
  have hd := relative_derivative spatialAxis h m₁ m₂ hr hp ha hc
  have he := spatial_density_eventually h m₁ m₂ hr hp ha hc
  have hb : fisherOn spatialAxis h m₁ m₂ ρ = jointDensity h m₁ m₂ ρ :=
    funext fun p => fisherOn_eq_jointDensity _ _ _ (hr.differentiable (by decide) p) (hp p)
  refine ⟨?_, ?_⟩
  · filter_upwards [hi, he] with t ht heq
    change Integrable (fun p => fisherOn spatialAxis h m₁ m₂ (fun z => ρ z + t*a z) p -
      fisherOn spatialAxis h m₁ m₂ ρ p) at ht
    simpa only [heq, hb] using ht
  · apply (hd.congr_deriv (integral_rawVariation_eq_configQ_sqrt h m₁ m₂ hρ hp ha hc)).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    change _ = ∫ p, fisherOn spatialAxis h m₁ m₂ (fun z => ρ z + t*a z) p - fisherOn spatialAxis h m₁ m₂ ρ p
    rw [ht, hb]

/-- For finite background Fisher energy, all sufficiently small affine perturbations
have finite energy and the original physical energy has derivative given by the Bohm potential. -/
theorem jointEnergy_derivative (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hfinite : Integrable (jointDensity h m₁ m₂ ρ)) :
    (∀ᶠ t in 𝓝 0, Integrable (jointDensity h m₁ m₂ (fun z => ρ z + t*a z))) ∧
    HasDerivAt (fun t => jointEnergy h m₁ m₂ (fun z => ρ z + t*a z))
      (∫ p, a p * configQ h m₁ m₂ (fun z => √(ρ z)) p.1 p.2) 0 := by
  obtain ⟨hi, hd⟩ := spatial_relative h m₁ m₂ hρ hp ha hc
  have hj : ∀ᶠ t in 𝓝 0, Integrable (jointDensity h m₁ m₂ (fun z => ρ z + t*a z)) := by
    filter_upwards [hi] with t ht
    simpa only [Pi.add_def, sub_add_cancel] using ht.add hfinite
  refine ⟨hj, ((hd.add_const (jointEnergy h m₁ m₂ ρ))).congr_of_eventuallyEq ?_⟩
  filter_upwards [hj] with t ht
  simp only [jointEnergy, integral_sub ht hfinite, sub_add_cancel]

end FoliationQM.TwoBodyFisherVariation
