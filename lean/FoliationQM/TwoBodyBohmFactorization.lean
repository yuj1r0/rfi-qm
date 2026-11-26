module

public import FoliationQM.FisherEquality
public import FoliationQM.TwoBodyBohmFactors

/-!
# Zero Fisher excess and factorization of the two-particle Bohm potential

At a fixed time the smooth positive joint density in v13
`prop:fisher_excess` factorizes when the Fisher excess vanishes. Its
marginals then inherit higher regularity from single joint slices.
The factorization of the positive amplitude splits the two spatial
Bohm potentials in `eq:Q12_bohm`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyBohmFactorization

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity TwoParticleFisher TwoBodyBohmFactors

variable {f : Spatial × Spatial → ℝ} {x y : Spatial}

/-- For a product joint density, each marginal is a slice divided by the other
strictly positive marginal. Thus both marginals inherit the local joint regularity. -/
theorem marginals_contDiffAt_of_factorization {n : WithTop ℕ∞} (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) (hf : ContDiffAt ℝ n f (x,y)) :
    ContDiffAt ℝ n (left f) x ∧ ContDiffAt ℝ n (right f) y := by
  have hl : left f = fun a => f (a,y) / right f y := by
    funext a
    rw [hprod]
    field_simp [show right f y ≠ 0 from (marginal_pos H.swap y).ne']
  have hr : right f = fun b => f (x,b) / left f x := by
    funext b
    rw [hprod]
    field_simp [(marginal_pos H x).ne']
  exact ⟨hl ▸ (hf.comp x (contDiff_prodMk_left y).contDiffAt).div_const _,
    hr ▸ (hf.comp y (contDiff_prodMk_right x).contDiffAt).div_const _⟩

/-- Positive joint density and its principal amplitude have the same local smoothness. -/
theorem contDiffAt_sqrt_iff {n : WithTop ℕ∞} (H : Regular f) :
    ContDiffAt ℝ n (fun z => √(f z)) (x,y) ↔ ContDiffAt ℝ n f (x,y) := by
  constructor
  · intro h
    have he : (fun z => (√(f z))^2) = f := funext fun z => Real.sq_sqrt (H.pos z).le
    exact he ▸ h.pow 2
  · exact fun h => h.sqrt (H.pos (x,y)).ne'

/-- The positive amplitude of the joint product equals the product of the actual marginal
amplitudes as functions on the entire spatial configuration slice. -/
theorem sqrt_joint_of_factorization (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) :
    (fun z => √(f z)) = fun z : Spatial × Spatial => √(left f z.1) * √(right f z.2) := by
  funext z
  rw [hprod z.1 z.2, Real.sqrt_mul (marginal_pos H z.1).le]

/-- Product densities have a conditional amplitude independent of the conditioning position. -/
theorem sqrt_conditional_of_factorization (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) :
    (fun z : Spatial × Spatial => √(conditional f z.1 z.2)) = fun z => √(right f z.2) := by
  funext z
  unfold conditional
  rw [hprod]
  field_simp [(marginal_pos H z.1).ne']

/-- At a product law the conditional amplitude has zero first and second derivatives in
every conditioning direction, including the directions used in the cross-coupling term. -/
theorem conditional_derivatives_of_factorization (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) (x y v : Spatial) :
    fderiv ℝ (fun a => √(conditional f a y)) x v = 0 ∧
    fderiv ℝ (fun a => fderiv ℝ (fun b => √(conditional f b y)) a v) x v = 0 := by
  have he : (fun a => √(conditional f a y)) = fun _ => √(right f y) :=
    funext fun a => congrFun (sqrt_conditional_of_factorization H hprod) (a,y)
  simp [he]

/-- For a factorized density the joint Bohm potential is the sum of the two
one-particle potentials evaluated on the square roots of its actual marginals. -/
theorem configQ_of_factorization (h m₁ m₂ : ℝ) (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) (x y : Spatial) :
    configQ h m₁ m₂ (fun z => √(f z)) x y =
      one h m₁ (fun a => √(left f a)) x + one h m₂ (fun b => √(right f b)) y := by
  have hp : 0 < right f y := marginal_pos H.swap y
  exact (congrArg (fun A => configQ h m₁ m₂ A x y) (sqrt_joint_of_factorization H hprod)).trans
    (separable h m₁ m₂ (fun a => √(left f a)) (fun b => √(right f b)) x y
      (Real.sqrt_pos.2 (marginal_pos H x)).ne' (Real.sqrt_pos.2 hp).ne')

/-- Zero excess supplies regular marginal amplitudes and a separated value at every C²
point. Both marginal potentials therefore use classical second derivatives there. -/
theorem regular_split_of_excess_zero {h m₁ m₂ : ℝ} (H : Regular f)
    (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity h m₁ m₂ f)) (hz : excess h m₁ f = 0)
    (hf : ContDiffAt ℝ 2 f (x,y)) :
    ContDiffAt ℝ 2 (fun a => √(left f a)) x ∧ ContDiffAt ℝ 2 (fun b => √(right f b)) y ∧
    configQ h m₁ m₂ (fun z => √(f z)) x y =
      one h m₁ (fun a => √(left f a)) x + one h m₂ (fun b => √(right f b)) y := by
  have hprod := (FisherEquality.excess_zero_iff_factorization H hh hm₁ hm₂ hJ).mp hz
  obtain ⟨hl, hr⟩ := marginals_contDiffAt_of_factorization H hprod hf
  have hp : 0 < right f y := marginal_pos H.swap y
  exact ⟨hl.sqrt (marginal_pos H x).ne', hr.sqrt hp.ne', configQ_of_factorization h m₁ m₂ H hprod x y⟩

/-- Vanishing of the measured conditional Fisher excess forces additive separation of
the two one-particle Bohm potentials at every C² point of the joint density. -/
theorem configQ_of_excess_zero {h m₁ m₂ : ℝ} (H : Regular f)
    (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity h m₁ m₂ f)) (hz : excess h m₁ f = 0)
    (hf : ContDiffAt ℝ 2 f (x,y)) :
    configQ h m₁ m₂ (fun z => √(f z)) x y =
      one h m₁ (fun a => √(left f a)) x + one h m₂ (fun b => √(right f b)) y :=
  (regular_split_of_excess_zero H hh hm₁ hm₂ hJ hz hf).2.2

/-- The conditional Bohm cross-coupling vanishes for any spatial density that
factorizes into its actual marginals. -/
theorem cross_of_factorization (h m₁ : ℝ) (H : Regular f)
    (hprod : ∀ a b, f (a,b) = left f a * right f b) (x y : Spatial) :
    cross h m₁ (fun a => √(left f a)) (fun z => √(conditional f z.1 z.2)) x y = 0 := by
  exact (congrArg (fun B => cross h m₁ (fun a => √(left f a)) B x y)
    (sqrt_conditional_of_factorization H hprod)).trans
    (cross_separable h m₁ (fun a => √(left f a)) (fun b => √(right f b)) x y)

/-- Zero measured Fisher excess forces the conditional Bohm cross-coupling to vanish. -/
theorem cross_of_excess_zero {h m₁ m₂ : ℝ} (H : Regular f)
    (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (jointDensity h m₁ m₂ f)) (hz : excess h m₁ f = 0) (x y : Spatial) :
    cross h m₁ (fun a => √(left f a)) (fun z => √(conditional f z.1 z.2)) x y = 0 :=
  cross_of_factorization h m₁ H ((FisherEquality.excess_zero_iff_factorization
    H hh hm₁ hm₂ hJ).mp hz) x y

end FoliationQM.TwoBodyBohmFactorization
