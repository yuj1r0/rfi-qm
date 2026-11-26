module
public import FoliationQM.CocycleBundleDensity
public import FoliationQM.CocycleSectionDensity
public import FoliationQM.DensityFrameDifferential

/-!
# Actual invariant-density differential naturality

Source: the invariant density of the supplied smooth cocycle-bundle
interpretation of v13 `prop:takabayasi`. The already constructed genuine
smooth total-space density maps are differentiated with Mathlib's actual
manifold derivative. The chain rule gives their precise compatibility
with actual polar realization, inverse reconstruction, changes of local
matrix frame, and pullback along a supplied smooth base map.

For the represented frame-change law, tangent endpoints are explicitly
identified using their already proved equality of actual density values.
The derivative of the positive-density scalar inclusion is the identity,
so these are also derivatives of the original real bilinear invariant.
Actual graph-defined section densities satisfy the corresponding chain
rules. The differentiability order is explicitly nonzero; no connection,
covariance of a differentiated Dirac equation, or integrated variational
dynamics is inferred from these coordinate identities.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function
namespace FoliationQM.CocycleDensityDifferential
open PolarAmplitudeTopology PolarTransitionCocycle PolarCocycleBundles
open PolarCocycleManifold CocycleBundleDensity

private theorem smooth_density_mfderiv_naturality
    {EA HA A EB HB C : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [TopologicalSpace HA]
    [TopologicalSpace A] [ChartedSpace HA A] {IA : ModelWithCorners ℝ EA HA}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    [TopologicalSpace C] [ChartedSpace HB C] {IC : ModelWithCorners ℝ EB HB}
    {k : WithTop ℕ∞} (hk : k ≠ 0)
    (r : A → PositiveDensity) (t : C → PositiveDensity) (g : A → C) (x : A)
    (he : ∀ a, t (g a) = r a) (ht : ContMDiff IC 𝓘(ℝ, ℝ) k t)
    (hg : ContMDiff IA IC k g) :
    (mfderiv IC 𝓘(ℝ, ℝ) t (g x)).comp (mfderiv IA IC g x) =
      mfderiv IA 𝓘(ℝ, ℝ) r x := by
  have hc := mfderiv_comp x (ht.mdifferentiable hk (g x)) (hg.mdifferentiable hk x)
  have heq : t ∘ g = r := funext he
  rw [heq] at hc
  exact hc.symm

private theorem smooth_density_mfderiv_cast
    {EA HA A EB HB C : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [TopologicalSpace HA]
    [TopologicalSpace A] [ChartedSpace HA A] {IA : ModelWithCorners ℝ EA HA}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    [TopologicalSpace C] [ChartedSpace HB C] {IC : ModelWithCorners ℝ EB HB}
    {k : WithTop ℕ∞} (hk : k ≠ 0)
    (r : A → PositiveDensity) (t : C → PositiveDensity) (g : A → C) (x : A)
    (he : ∀ a, t (g a) = r a) (ht : ContMDiff IC 𝓘(ℝ, ℝ) k t)
    (hg : ContMDiff IA IC k g) :
    (tangentSpaceCast 𝓘(ℝ, ℝ) (t (g x)) (r x)).toContinuousLinearMap.comp
      ((mfderiv IC 𝓘(ℝ, ℝ) t (g x)).comp (mfderiv IA IC g x)) =
      mfderiv IA 𝓘(ℝ, ℝ) r x := by
  ext v
  exact congrArg (fun k => k v) (smooth_density_mfderiv_naturality hk r t g x he ht hg)

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n) [IsManifold I n B] (hn : n ≠ 0)

include hn

/-- The actual total spinor-density derivative composed with actual realization's derivative is precisely the actual polar-density derivative. -/
theorem mfderiv_density_realization (p : PolarTotal D) :
    (mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D) (totalRealization D p)).comp
      (mfderiv (polarModel I) (spinorModel I) (totalRealization D) p) =
      mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D) p := by
  have he : spinorDensity D ∘ totalRealization D = polarDensity D := by
    funext q
    exact spinorDensity_realization D q
  have hc := mfderiv_comp p ((contMDiff_spinorDensity D).mdifferentiable hn _)
    ((contMDiff_totalRealization D).mdifferentiable hn p)
  rw [he] at hc
  exact hc.symm

/-- The actual inverse reconstruction derivative carries the polar-density differential to the same intrinsic spinor-density differential. -/
theorem mfderiv_density_reconstruction (p : SpinorTotal D) :
    (mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D)
      ((totalRealization D).symm p)).comp
      (mfderiv (spinorModel I) (polarModel I) (totalRealization D).symm p) =
      mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D) p := by
  have he : polarDensity D ∘ (totalRealization D).symm = spinorDensity D := by
    funext q
    rfl
  have hc := mfderiv_comp p ((contMDiff_polarDensity D).mdifferentiable hn _)
    ((contMDiff_totalRealization_symm D).mdifferentiable hn p)
  rw [he] at hc
  exact hc.symm

/-- The positive polar-density derivative is unchanged under the actual derivative of a supplied local matrix-frame change, including its base dependence. -/
theorem mfderiv_polarDensity_gauge (h : CocycleGaugeTransform.FrameChange D)
    (p : PolarTotal D) :
    (mfderiv (polarModel I) 𝓘(ℝ, ℝ)
      (polarDensity (CocycleGaugeTransform.transformed D h))
      (CocycleGaugeBundles.polarMap D h p)).comp
      (mfderiv (polarModel I) (polarModel I) (CocycleGaugeBundles.polarMap D h) p) =
      mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D) p := by
  have he : polarDensity (CocycleGaugeTransform.transformed D h) ∘
      CocycleGaugeBundles.polarMap D h = polarDensity D := by
    funext q
    exact polarDensity_gauge D h q
  have hc := mfderiv_comp p
    ((contMDiff_polarDensity (CocycleGaugeTransform.transformed D h)).mdifferentiable hn _)
    ((CocycleGaugeBundles.contMDiff_polarMap D h).mdifferentiable hn p)
  rw [he] at hc
  exact hc.symm

/-- The full derivative of the actual represented frame change preserves the invariant-density differential, with tangent endpoints identified by the already proved equality of their actual positive-density values. -/
theorem mfderiv_spinorDensity_gauge (h : CocycleGaugeTransform.FrameChange D)
    (p : SpinorTotal D) :
    (tangentSpaceCast 𝓘(ℝ, ℝ)
      (spinorDensity (CocycleGaugeTransform.transformed D h) (CocycleGaugeBundles.spinorMap D h p))
      (spinorDensity D p)).toContinuousLinearMap.comp
      ((mfderiv (spinorModel I) 𝓘(ℝ, ℝ)
        (spinorDensity (CocycleGaugeTransform.transformed D h))
        (CocycleGaugeBundles.spinorMap D h p)).comp
        (mfderiv (spinorModel I) (spinorModel I) (CocycleGaugeBundles.spinorMap D h) p)) =
      mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D) p := by
  exact smooth_density_mfderiv_cast hn (spinorDensity D)
    (spinorDensity (CocycleGaugeTransform.transformed D h))
    (CocycleGaugeBundles.spinorMap D h) p (spinorDensity_gauge D h)
    (contMDiff_spinorDensity (CocycleGaugeTransform.transformed D h))
    (CocycleGaugeBundles.contMDiff_spinorMap D h)

/-- The actual real scalar polar-density derivative equals the positive-manifold density derivative, using the genuine identity derivative of scalar inclusion. -/
theorem mfderiv_polarDensity_value (p : PolarTotal D) :
    mfderiv (polarModel I) 𝓘(ℝ, ℝ) (fun q => (polarDensity D q : ℝ)) p =
      mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D) p := by
  have hc := mfderiv_comp p
    ((PolarScalarManifolds.contMDiff_density_value n).mdifferentiable hn (polarDensity D p))
    ((contMDiff_polarDensity D).mdifferentiable hn p)
  rw [DensityFrameDifferential.density_value_mfderiv] at hc
  exact hc.trans (by ext v; rfl)

/-- The actual derivative of the original real bilinear spinor invariant is exactly the derivative of the genuine positive-density bundle map. -/
theorem mfderiv_spinorDensity_value (p : SpinorTotal D) :
    mfderiv (spinorModel I) 𝓘(ℝ, ℝ)
      (fun q : SpinorTotal D => SpinorRegularity.invariantDensity q.2.val) p =
      mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D) p := by
  have he : (fun q : SpinorTotal D => SpinorRegularity.invariantDensity q.2.val) =
      (Subtype.val : PositiveDensity → ℝ) ∘ spinorDensity D := by
    funext q
    exact (DensityFrameFields.density_value_eq_invariantDensity q.2).symm
  rw [he, mfderiv_comp p
    ((PolarScalarManifolds.contMDiff_density_value n).mdifferentiable hn (spinorDensity D p))
    ((contMDiff_spinorDensity D).mdifferentiable hn p),
    DensityFrameDifferential.density_value_mfderiv]
  ext v
  rfl

/-- The derivative of the actual polar section density factors through the genuine smooth total-space section graph and the proved bundle density map. -/
theorem mfderiv_polarSectionDensity (s : PolarCocycleSections.PolarSection D) (x : B) :
    mfderiv I 𝓘(ℝ, ℝ) (CocycleSectionDensity.polarDensityField D s) x =
      (mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D)
        (⟨x, s.val x⟩ : PolarTotal D)).comp
      (mfderiv I (polarModel I) (fun y => (⟨y, s.val y⟩ : PolarTotal D)) x) := by
  exact mfderiv_comp x ((contMDiff_polarDensity D).mdifferentiable hn _)
    (s.property.mdifferentiable hn x)

/-- The actual spinor section-density derivative factors through its independently smooth total-space graph and the actual invariant-density map. -/
theorem mfderiv_spinorSectionDensity (s : PolarCocycleSections.SpinorSection D) (x : B) :
    mfderiv I 𝓘(ℝ, ℝ) (CocycleSectionDensity.spinorDensityField D s) x =
      (mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D)
        (⟨x, s.val x⟩ : SpinorTotal D)).comp
      (mfderiv I (spinorModel I) (fun y => (⟨y, s.val y⟩ : SpinorTotal D)) x) := by
  exact mfderiv_comp x ((contMDiff_spinorDensity D).mdifferentiable hn _)
    (s.property.mdifferentiable hn x)

variable {E' H' B' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B'] [ChartedSpace H' B'] [IsManifold J n B']
  (f : C^n⟮J, B'; I, B⟯)

/-- The actual polar density differential pulls back along the canonical smooth total map over any supplied smooth base map. -/
theorem mfderiv_polarDensity_pullback (p : PolarTotal (CocyclePullback.pullback D f)) :
    (mfderiv (polarModel I) 𝓘(ℝ, ℝ) (polarDensity D)
      (CocyclePullbackBundles.polarMap D f p)).comp
      (mfderiv (polarModel J) (polarModel I) (CocyclePullbackBundles.polarMap D f) p) =
      mfderiv (polarModel J) 𝓘(ℝ, ℝ) (polarDensity (CocyclePullback.pullback D f)) p := by
  have he : polarDensity D ∘ CocyclePullbackBundles.polarMap D f =
      polarDensity (CocyclePullback.pullback D f) := rfl
  have hc := mfderiv_comp p ((contMDiff_polarDensity D).mdifferentiable hn _)
    ((CocyclePullbackBundles.contMDiff_polarMap D f).mdifferentiable hn p)
  rw [he] at hc
  exact hc.symm

/-- The original represented-spinor invariant-density differential obeys the exact chain rule for the canonical base-pullback total map. -/
theorem mfderiv_spinorDensity_pullback (p : SpinorTotal (CocyclePullback.pullback D f)) :
    (mfderiv (spinorModel I) 𝓘(ℝ, ℝ) (spinorDensity D)
      (CocyclePullbackBundles.spinorMap D f p)).comp
      (mfderiv (spinorModel J) (spinorModel I) (CocyclePullbackBundles.spinorMap D f) p) =
      mfderiv (spinorModel J) 𝓘(ℝ, ℝ) (spinorDensity (CocyclePullback.pullback D f)) p := by
  have he : spinorDensity D ∘ CocyclePullbackBundles.spinorMap D f =
      spinorDensity (CocyclePullback.pullback D f) := rfl
  have hc := mfderiv_comp p ((contMDiff_spinorDensity D).mdifferentiable hn _)
    ((CocyclePullbackBundles.contMDiff_spinorMap D f).mdifferentiable hn p)
  rw [he] at hc
  exact hc.symm

/-- The density derivative of a pulled-back actual polar section is the original section-density derivative composed with the supplied base derivative. -/
theorem mfderiv_polarSectionDensity_pullback
    (s : PolarCocycleSections.PolarSection D) (x : B') :
    mfderiv J 𝓘(ℝ, ℝ)
      (CocycleSectionDensity.polarDensityField (CocyclePullback.pullback D f)
        (CocyclePullbackSections.polarSectionPullback D f s)) x =
      (mfderiv I 𝓘(ℝ, ℝ) (CocycleSectionDensity.polarDensityField D s) (f x)).comp
        (mfderiv J I f x) := by
  have he : (CocycleSectionDensity.polarDensityField (CocyclePullback.pullback D f)
        (CocyclePullbackSections.polarSectionPullback D f s) : B' → PositiveDensity) =
      CocycleSectionDensity.polarDensityField D s ∘ f := by
    funext y
    exact CocyclePullbackSections.polarSectionPullback_density D f s y
  rw [he]
  exact mfderiv_comp x
    ((CocycleSectionDensity.polarDensityField D s).contMDiff.mdifferentiable hn _)
    (f.contMDiff.mdifferentiable hn x)

/-- The actual represented-spinor section-density derivative obeys the same genuine base-pullback chain rule without invertibility of the base map. -/
theorem mfderiv_spinorSectionDensity_pullback
    (s : PolarCocycleSections.SpinorSection D) (x : B') :
    mfderiv J 𝓘(ℝ, ℝ)
      (CocycleSectionDensity.spinorDensityField (CocyclePullback.pullback D f)
        (CocyclePullbackSections.spinorSectionPullback D f s)) x =
      (mfderiv I 𝓘(ℝ, ℝ) (CocycleSectionDensity.spinorDensityField D s) (f x)).comp
        (mfderiv J I f x) := by
  have he : (CocycleSectionDensity.spinorDensityField (CocyclePullback.pullback D f)
        (CocyclePullbackSections.spinorSectionPullback D f s) : B' → PositiveDensity) =
      CocycleSectionDensity.spinorDensityField D s ∘ f := by
    funext y
    change DensityFrameFields.density
      ((CocyclePullbackSections.spinorSectionPullback D f s).val y) =
      DensityFrameFields.density (s.val (f y))
    rw [CocyclePullbackSections.spinorSectionPullback_apply]
  rw [he]
  exact mfderiv_comp x
    ((CocycleSectionDensity.spinorDensityField D s).contMDiff.mdifferentiable hn _)
    (f.contMDiff.mdifferentiable hn x)

end FoliationQM.CocycleDensityDifferential
