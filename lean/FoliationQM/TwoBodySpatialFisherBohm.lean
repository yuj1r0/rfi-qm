module

public import FoliationQM.TwoBodyBohmFactors
public import FoliationQM.TwoBodyBohmGreen

/-!
# Physical Fisher density and Bohm potential in the six spatial directions

A fixed-time pair of positions carries six spatial directions. Restricting
the density and its first two derivatives to either particle identifies
the six-coordinate Green formula with v13's spatial Fisher functional
and the potential from the two particle Laplacians.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodySpatialFisherBohm

open MeasureTheory LorentzCoordinates ObserverGaussianFisher TwoBodyBohmFactors
open TwoParticleFisher JointScoreRegularity FisherNormalization TwoBodyActionDensity
open TwoBodyBohmGreen PolarSecondDifferential
open scoped BigOperators Topology

private theorem slice_first {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : Spatial × Spatial → ℝ} {g : A → Spatial × Spatial} {L : A →L[ℝ] Spatial × Spatial}
    {a : A} (hg : HasFDerivAt g L a) (hf : DifferentiableAt ℝ f (g a)) (v : A) :
    fderiv ℝ (f ∘ g) a v = fderiv ℝ f (g a) (L v) := by
  rw [(hf.hasFDerivAt.comp a hg).fderiv]
  rfl

private theorem slice_second {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : Spatial × Spatial → ℝ} {g : A → Spatial × Spatial} {L : A →L[ℝ] Spatial × Spatial}
    (hg : ∀ a, HasFDerivAt g L a) {a : A} (hf : ContDiffAt ℝ 2 f (g a)) (v : A) :
    fderiv ℝ (fun u => fderiv ℝ (f ∘ g) u v) a v =
      fderiv ℝ (fun z => fderiv ℝ f z (L v)) (g a) (L v) := by
  have hnear := (hg a).continuousAt.eventually (PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf)
  have he : (fun u => fderiv ℝ (f ∘ g) u v) =ᶠ[𝓝 a] (fun z => fderiv ℝ f z (L v)) ∘ g := by
    filter_upwards [hnear] with u hu
    exact slice_first (hg u) hu v
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ f z (L v)) (g a) :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hf (L v)
  rw [he.fderiv_eq]
  exact slice_first (hg a) hd v

/-- The first particle's actual Laplacian uses the full product-space axes with zero
second component. -/
theorem lap_left {R : Spatial × Spatial → ℝ} {x y : Spatial} (hR : ContDiffAt ℝ 2 R (x,y)) :
    lap (fun u => R (u,y)) x =
      ∑ i, fderiv ℝ (fun z => fderiv ℝ R z (axes i,0)) (x,y) (axes i,0) :=
  Finset.sum_congr rfl fun i _ =>
    slice_second (fun u => hasFDerivAt_prodMk_left (𝕜 := ℝ) u y) hR (axes i)

/-- The remote particle Laplacian corresponds to the complementary spatial directions. -/
theorem lap_right {R : Spatial × Spatial → ℝ} {x y : Spatial} (hR : ContDiffAt ℝ 2 R (x,y)) :
    lap (fun v => R (x,v)) y =
      ∑ i, fderiv ℝ (fun z => fderiv ℝ R z (0,axes i)) (x,y) (0,axes i) :=
  Finset.sum_congr rfl fun i _ =>
    slice_second (fun v => hasFDerivAt_prodMk_right (𝕜 := ℝ) x v) hR (axes i)

/-- The two coordinate scores are the corresponding product-space derivatives divided
by the positive joint density. -/
theorem spatial_scores {ρ : Spatial × Spatial → ℝ} {x y : Spatial}
    (hρ : DifferentiableAt ℝ ρ (x,y)) (hp : 0 < ρ (x,y)) (i : Fin 3) :
    firstScore ρ x y (axes i) = fderiv ℝ ρ (x,y) (axes i,0) / ρ (x,y) ∧
    secondScore ρ x y (axes i) = fderiv ℝ ρ (x,y) (0,axes i) / ρ (x,y) := by
  have hl := hasFDerivAt_prodMk_left (𝕜 := ℝ) x y
  have hr := hasFDerivAt_prodMk_right (𝕜 := ℝ) x y
  exact ⟨(score_eq (hρ.comp x hl.differentiableAt) hp (axes i)).trans
    (congrArg (· / ρ (x,y)) (slice_first hl hρ (axes i))),
    (score_eq (hρ.comp y hr.differentiableAt) hp (axes i)).trans
    (congrArg (· / ρ (x,y)) (slice_first hr hρ (axes i)))⟩

/-- The six-axis density-gradient integrand is the score-based physical joint Fisher density. -/
theorem fisherOn_eq_jointDensity (h m₁ m₂ : ℝ) {ρ : Spatial × Spatial → ℝ} {x y : Spatial}
    (hρ : DifferentiableAt ℝ ρ (x,y)) (hp : 0 < ρ (x,y)) :
    fisherOn spatialAxis h m₁ m₂ ρ (x,y) = jointDensity h m₁ m₂ ρ (x,y) := by
  have scalar (u : ℝ) : ρ (x,y) * (u / ρ (x,y))^2 = u^2 / ρ (x,y) := by field_simp
  simp only [fisherOn, Fintype.sum_sum_type, spatialAxis, mass, Sum.elim_inl, Sum.elim_inr,
    directionalDerivative, jointDensity, fun i => (spatial_scores hρ hp i).1,
    fun i => (spatial_scores hρ hp i).2, Finset.mul_sum, scalar, coefficient]

/-- Integrating the six-axis expression gives exactly the source's previously defined
joint energy whenever the density conditions hold almost everywhere. -/
theorem integral_fisherOn_eq_jointEnergy (h m₁ m₂ : ℝ) {ρ : Spatial × Spatial → ℝ}
    (hρ : ∀ᵐ p, DifferentiableAt ℝ ρ p ∧ 0 < ρ p) :
    (∫ p, fisherOn spatialAxis h m₁ m₂ ρ p) = jointEnergy h m₁ m₂ ρ :=
  integral_congr_ae (hρ.mono fun _ hp => fisherOn_eq_jointDensity _ _ _ hp.1 hp.2)

/-- The actual physical score density has the density-coordinate first variation at
each parameter for which the varied density is positive at the selected point. -/
theorem hasDerivAt_jointDensity_affine (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ}
    {p : Spatial × Spatial} (hρ : DifferentiableAt ℝ ρ p) (ha : DifferentiableAt ℝ a p)
    (s : ℝ) (hp : 0 < ρ p + s*a p) :
    HasDerivAt (fun t => jointDensity h m₁ m₂ (fun z => ρ z + t*a z) p)
      (rawVariationOn spatialAxis h m₁ m₂ (fun z => ρ z + s*a z) a p) s := by
  apply (hasDerivAt_fisherOn_affine spatialAxis h m₁ m₂ hρ ha s hp.ne').congr_of_eventuallyEq
  have hc : Continuous (fun t : ℝ => ρ p + t*a p) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hp)] with t ht
  exact (fisherOn_eq_jointDensity h m₁ m₂ (hρ.add (ha.const_mul t)) ht).symm

/-- The six-axis potential agrees with the source's sum of the two three-dimensional
Bohm potentials at each twice continuously differentiable point. -/
theorem quantumOn_eq_configQ (h m₁ m₂ : ℝ) {R : Spatial × Spatial → ℝ} {x y : Spatial}
    (hR : ContDiffAt ℝ 2 R (x,y)) :
    quantumOn spatialAxis h m₁ m₂ R (x,y) = configQ h m₁ m₂ R x y := by
  simp only [quantumOn, Fintype.sum_sum_type, spatialAxis, mass, Sum.elim_inl, Sum.elim_inr,
    secondDirectionalDerivative, directionalDerivative, configQ, one, lap_left hR, lap_right hR,
    ← Finset.mul_sum]
  unfold directionalDerivative
  ring

/-- The six-dimensional compact-test Green identity pairs the density variation
with the actual configuration-space Bohm potential of the positive amplitude. -/
theorem integral_rawVariation_eq_configQ (h m₁ m₂ : ℝ) {R a : Spatial × Spatial → ℝ}
    (hR : ContDiff ℝ 2 R) (hp : ∀ p, 0 < R p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    (∫ p, rawVariationOn spatialAxis h m₁ m₂ (fun z => R z^2) a p) =
      ∫ p, a p * configQ h m₁ m₂ R p.1 p.2 := by
  rw [integral_spatial_rawVariation_sq h m₁ m₂ hR hp ha hc]
  exact integral_congr_ae (.of_forall fun p =>
    congrArg (a p * ·) (quantumOn_eq_configQ h m₁ m₂ (hR.contDiffAt (x := (p.1,p.2)))))

/-- In terms of positive density alone, the compact-test variation pairs with
the physical Bohm potential of its principal square root. -/
theorem integral_rawVariation_eq_configQ_sqrt (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    (∫ p, rawVariationOn spatialAxis h m₁ m₂ ρ a p) =
      ∫ p, a p * configQ h m₁ m₂ (fun z => √(ρ z)) p.1 p.2 := by
  have hs : (fun z => (√(ρ z))^2) = ρ := funext fun z => Real.sq_sqrt (hp z).le
  have he := integral_rawVariation_eq_configQ h m₁ m₂ (hρ.sqrt fun z => (hp z).ne')
    (fun z => Real.sqrt_pos.2 (hp z)) ha hc
  simpa only [hs] using he

/-- Both sides of the density-coordinate Green formula are absolutely integrable
under exactly the compact-test and regularity assumptions of the identity. -/
theorem integrable_rawVariation_and_configQ (h m₁ m₂ : ℝ) {ρ a : Spatial × Spatial → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) :
    Integrable (rawVariationOn spatialAxis h m₁ m₂ ρ a) ∧
      Integrable (fun p => a p * configQ h m₁ m₂ (fun z => √(ρ z)) p.1 p.2) := by
  have hr := hρ.sqrt fun z => (hp z).ne'
  have hs : (fun z => (√(ρ z))^2) = ρ := funext fun z => Real.sq_sqrt (hp z).le
  have hi := integrable_spatial_rawVariation_sq h m₁ m₂ hr (fun z => Real.sqrt_pos.2 (hp z)) ha hc
  refine ⟨by simpa only [hs] using hi.1, hi.2.congr ?_⟩
  exact .of_forall fun p => congrArg (a p * ·)
    (quantumOn_eq_configQ h m₁ m₂ (hr.contDiffAt (x := (p.1,p.2))))

end FoliationQM.TwoBodySpatialFisherBohm
