module
public import FoliationQM.CocycleGaugeBundles
public import FoliationQM.CocyclePullbackBundles
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual tangent maps of cocycle realization, frame change, and base pullback

Source: differential naturality in the supplied smooth cocycle-bundle
interpretation of v13 `prop:takabayasi`. The previously proved actual total
realization and inverse reconstruction diffeomorphisms, and the genuine
polar and represented-spinor frame-change diffeomorphisms, have continuous-
linear tangent equivalences at every stated nonzero differentiability order.
Their underlying maps are identified with the actual manifold Frechet
derivatives, and invertibility is proved for those actual derivatives.

The genuine manifold chain rule differentiates the existing exact bundle
projection laws. It also differentiates the actual realization squares with
frame change and canonical smooth base pullback. One represented gauge
projection formula explicitly identifies tangent spaces at base points
already proved equal by the exact projection law; this retains the literal
existing diffeomorphism and avoids implicit conversion of its large matrix
representation. The identification is not between unrelated base points.

All statements preserve the independently constructed core topologies and
atlases, the supplied cocycle and frame-change hypotheses, the stated base
manifold regularity, and the explicit nonzero derivative order. An arbitrary
smooth base pullback receives its actual chain rules, without an invertibility
claim. No connection, differentiated Dirac covariance, integrated variational
principle, or abstract spacetime Spin classification is inferred.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function
namespace FoliationQM.CocycleBundleDifferential
open PolarTransitionCocycle PolarCocycleBundles PolarCocycleManifold
open CocycleGaugeTransform CocyclePullback

section AbstractChain
variable {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {I₃ : ModelWithCorners ℝ E₃ H₃}
private theorem mfderiv_of_comp_eq {n : WithTop ℕ∞} (hn : n ≠ 0)
    (k : M₁ → M₃) (g : M₂ → M₃) (f : M₁ → M₂) (x : M₁)
    (he : ∀ y, g (f y) = k y)
    (hg : ContMDiff I₂ I₃ n g) (hf : ContMDiff I₁ I₂ n f) :
    (mfderiv I₂ I₃ g (f x)).comp (mfderiv I₁ I₂ f x) = mfderiv I₁ I₃ k x := by
  have hc := mfderiv_comp x (hg.mdifferentiable hn (f x)) (hf.mdifferentiable hn x)
  have heq : g ∘ f = k := funext he
  rw [heq] at hc
  exact hc.symm

private theorem mfderiv_cast_of_comp_eq {n : WithTop ℕ∞} (hn : n ≠ 0)
    (k : M₁ → M₃) (g : M₂ → M₃) (f : M₁ → M₂) (x : M₁)
    (he : ∀ y, g (f y) = k y)
    (hg : ContMDiff I₂ I₃ n g) (hf : ContMDiff I₁ I₂ n f) :
    (tangentSpaceCast I₃ (g (f x)) (k x)).toContinuousLinearMap.comp
      ((mfderiv I₂ I₃ g (f x)).comp (mfderiv I₁ I₂ f x)) = mfderiv I₁ I₃ k x := by
  ext v
  exact congrArg (fun T => T v) (mfderiv_of_comp_eq hn k g f x he hg hf)

end AbstractChain

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n) [IsManifold I n B] (hn : n ≠ 0)
include hn

/-- The actual total realization derivative is a continuous-linear equivalence between the tangent spaces of the independently constructed cocycle bundle manifolds. -/
def realizationTangentEquiv (p : PolarTotal D) :
    TangentSpace (polarModel I) p ≃L[ℝ]
      TangentSpace (spinorModel I) (totalRealization D p) :=
  (totalRealizationDiffeomorph D).mfderivToContinuousLinearEquiv hn p

/-- The total realization tangent equivalence has precisely the actual derivative of the existing total realization homeomorphism as its underlying map. -/
theorem realizationTangentEquiv_toContinuousLinearMap (p : PolarTotal D) :
    (realizationTangentEquiv D hn p).toContinuousLinearMap =
      mfderiv (polarModel I) (spinorModel I) (totalRealization D) p :=
  (totalRealizationDiffeomorph D).mfderivToContinuousLinearEquiv_coe hn

/-- At every point and every stated nonzero order, the actual total realization derivative is invertible. -/
theorem realization_mfderiv_isInvertible (p : PolarTotal D) :
    (mfderiv (polarModel I) (spinorModel I) (totalRealization D) p).IsInvertible :=
  (totalRealizationDiffeomorph D).isInvertible_mfderiv hn

/-- The derivative of actual inverse total polar reconstruction is a continuous-linear tangent equivalence. -/
def inverseRealizationTangentEquiv (q : SpinorTotal D) :
    TangentSpace (spinorModel I) q ≃L[ℝ]
      TangentSpace (polarModel I) ((totalRealization D).symm q) :=
  (totalRealizationDiffeomorph D).symm.mfderivToContinuousLinearEquiv hn q

/-- The inverse reconstruction tangent equivalence is exactly the actual derivative of the existing inverse realization map. -/
theorem inverseRealizationTangentEquiv_toContinuousLinearMap (q : SpinorTotal D) :
    (inverseRealizationTangentEquiv D hn q).toContinuousLinearMap =
      mfderiv (spinorModel I) (polarModel I) (totalRealization D).symm q :=
  (totalRealizationDiffeomorph D).symm.mfderivToContinuousLinearEquiv_coe hn

/-- The actual inverse total reconstruction derivative is invertible at each point for each stated nonzero order. -/
theorem inverseRealization_mfderiv_isInvertible (q : SpinorTotal D) :
    (mfderiv (spinorModel I) (polarModel I) (totalRealization D).symm q).IsInvertible :=
  (totalRealizationDiffeomorph D).symm.isInvertible_mfderiv hn

/-- The genuine chain rule differentiates actual base preservation by total realization, so its tangent map commutes with the two actual bundle projection derivatives. -/
theorem realization_mfderiv_proj (p : PolarTotal D) :
    (mfderiv (spinorModel I) I (spinorCore D).proj (totalRealization D p)).comp
      (mfderiv (polarModel I) (spinorModel I) (totalRealization D) p) =
        mfderiv (polarModel I) I (polarCore D).proj p := by
  exact (mfderiv_comp p
    ((contMDiff_spinor_proj D).mdifferentiable hn (totalRealization D p))
    ((contMDiff_totalRealization D).mdifferentiable hn p)).symm

/-- Actual inverse reconstruction likewise commutes with the genuine tangent bundle projections by differentiating its literal base-preserving formula. -/
theorem inverseRealization_mfderiv_proj (q : SpinorTotal D) :
    (mfderiv (polarModel I) I (polarCore D).proj ((totalRealization D).symm q)).comp
      (mfderiv (spinorModel I) (polarModel I) (totalRealization D).symm q) =
        mfderiv (spinorModel I) I (spinorCore D).proj q := by
  exact (mfderiv_comp q
    ((contMDiff_polar_proj D).mdifferentiable hn ((totalRealization D).symm q))
    ((contMDiff_totalRealization_symm D).mdifferentiable hn q)).symm

variable (h : FrameChange D)

/-- The actual local matrix frame change induces a continuous-linear tangent equivalence on the polar cocycle total manifolds at nonzero differentiability order. -/
def polarGaugeTangentEquiv (p : PolarTotal D) :
    TangentSpace (polarModel I) p ≃L[ℝ]
      TangentSpace (polarModel I) (CocycleGaugeBundles.polarMap D h p) :=
  (CocycleGaugeBundles.polarDiffeomorph D h).mfderivToContinuousLinearEquiv hn p

/-- The polar gauge tangent equivalence has exactly the actual derivative of the directly defined local-matrix bundle map as its underlying map. -/
theorem polarGaugeTangentEquiv_toContinuousLinearMap (p : PolarTotal D) :
    (polarGaugeTangentEquiv D hn h p).toContinuousLinearMap =
      mfderiv (polarModel I) (polarModel I) (CocycleGaugeBundles.polarMap D h) p :=
  (CocycleGaugeBundles.polarDiffeomorph D h).mfderivToContinuousLinearEquiv_coe hn

/-- The actual polar frame-change derivative is invertible, using the proved smooth inverse matrix bundle action. -/
theorem polarGauge_mfderiv_isInvertible (p : PolarTotal D) :
    (mfderiv (polarModel I) (polarModel I) (CocycleGaugeBundles.polarMap D h) p).IsInvertible :=
  (CocycleGaugeBundles.polarDiffeomorph D h).isInvertible_mfderiv hn

/-- The directly represented local matrix frame change likewise has a genuine continuous-linear tangent equivalence on the spinor total manifolds. -/
def spinorGaugeTangentEquiv (q : SpinorTotal D) :
    TangentSpace (spinorModel I) q ≃L[ℝ]
      TangentSpace (spinorModel I) (CocycleGaugeBundles.spinorMap D h q) :=
  (CocycleGaugeBundles.spinorDiffeomorph D h).mfderivToContinuousLinearEquiv hn q

/-- The represented-spinor gauge tangent equivalence is precisely the actual derivative of the directly defined spinor bundle action. -/
theorem spinorGaugeTangentEquiv_toContinuousLinearMap (q : SpinorTotal D) :
    (spinorGaugeTangentEquiv D hn h q).toContinuousLinearMap =
      mfderiv (spinorModel I) (spinorModel I) (CocycleGaugeBundles.spinorMap D h) q :=
  (CocycleGaugeBundles.spinorDiffeomorph D h).mfderivToContinuousLinearEquiv_coe hn

/-- The actual represented-spinor frame-change derivative is invertible at every total-space point. -/
theorem spinorGauge_mfderiv_isInvertible (q : SpinorTotal D) :
    (mfderiv (spinorModel I) (spinorModel I) (CocycleGaugeBundles.spinorMap D h) q).IsInvertible :=
  (CocycleGaugeBundles.spinorDiffeomorph D h).isInvertible_mfderiv hn

/-- Differentiating the literal polar gauge map proves that its actual tangent map preserves the bundle projection derivative. -/
theorem polarGauge_mfderiv_proj (p : PolarTotal D) :
    (mfderiv (polarModel I) I (polarCore (transformed D h)).proj
      (CocycleGaugeBundles.polarMap D h p)).comp
      (mfderiv (polarModel I) (polarModel I) (CocycleGaugeBundles.polarMap D h) p) =
        mfderiv (polarModel I) I (polarCore D).proj p := by
  exact (mfderiv_comp p
    ((contMDiff_polar_proj (transformed D h)).mdifferentiable hn
      (CocycleGaugeBundles.polarMap D h p))
    ((CocycleGaugeBundles.contMDiff_polarMap D h).mdifferentiable hn p)).symm

/-- Actual realization and local frame change commute after differentiation: both compositions are derivatives of the same genuine total-space map. -/
theorem realization_gauge_mfderiv (p : PolarTotal D) :
    (mfderiv (polarModel I) (spinorModel I) (totalRealization (transformed D h))
      (CocycleGaugeBundles.polarMap D h p)).comp
      (mfderiv (polarModel I) (polarModel I) (CocycleGaugeBundles.polarMap D h) p) =
    (mfderiv (spinorModel I) (spinorModel I) (CocycleGaugeBundles.spinorMap D h)
      (totalRealization D p)).comp
      (mfderiv (polarModel I) (spinorModel I) (totalRealization D) p) := by
  have he : (totalRealization (transformed D h)) ∘ CocycleGaugeBundles.polarMap D h =
      CocycleGaugeBundles.spinorMap D h ∘ totalRealization D :=
    funext (CocycleGaugeBundles.realization_commutes D h)
  rw [← mfderiv_comp p
      ((contMDiff_totalRealization (transformed D h)).mdifferentiable hn _)
      ((CocycleGaugeBundles.contMDiff_polarMap D h).mdifferentiable hn p),
    he]
  exact mfderiv_comp p
    ((CocycleGaugeBundles.contMDiff_spinorMap D h).mdifferentiable hn _)
    ((contMDiff_totalRealization D).mdifferentiable hn p)

/-- The actual represented gauge tangent map preserves the genuine bundle projection derivative. The explicit tangent identification is between the equal base points given by the proved literal projection law. -/
theorem spinorGauge_mfderiv_proj (q : SpinorTotal D) :
    (tangentSpaceCast I
      ((spinorCore (transformed D h)).proj (CocycleGaugeBundles.spinorDiffeomorph D h q))
      ((spinorCore D).proj q)).toContinuousLinearMap.comp
      ((mfderiv (spinorModel I) I (spinorCore (transformed D h)).proj
        (CocycleGaugeBundles.spinorDiffeomorph D h q)).comp
        (mfderiv (spinorModel I) (spinorModel I) (CocycleGaugeBundles.spinorDiffeomorph D h) q)) =
      mfderiv (spinorModel I) I (spinorCore D).proj q := by
  exact mfderiv_cast_of_comp_eq hn (spinorCore D).proj
    (spinorCore (transformed D h)).proj (CocycleGaugeBundles.spinorDiffeomorph D h) q
    (CocycleGaugeBundles.spinorDiffeomorph_proj D h)
    (contMDiff_spinor_proj (transformed D h))
    (CocycleGaugeBundles.spinorDiffeomorph D h).contMDiff

section Pullback
variable {E' H' B' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B'] [ChartedSpace H' B'] [IsManifold J n B']
  (f : C^n⟮J, B'; I, B⟯)

/-- The actual polar pullback map differentiates over the supplied base map: composing with the original projection derivative equals the base derivative composed with the pulled projection derivative. -/
theorem polarPullback_mfderiv_proj (p : PolarTotal (pullback D f)) :
    (mfderiv (polarModel I) I (polarCore D).proj
      (CocyclePullbackBundles.polarMap D f p)).comp
      (mfderiv (polarModel J) (polarModel I) (CocyclePullbackBundles.polarMap D f) p) =
    (mfderiv J I f p.proj).comp
      (mfderiv (polarModel J) J (polarCore (pullback D f)).proj p) := by
  rw [← mfderiv_comp p
    ((contMDiff_polar_proj D).mdifferentiable hn _)
    ((CocyclePullbackBundles.contMDiff_polarMap D f).mdifferentiable hn p)]
  exact mfderiv_comp p (f.contMDiff.mdifferentiable hn p.proj)
    ((contMDiff_polar_proj (pullback D f)).mdifferentiable hn p)

/-- The genuine represented-spinor pullback derivative obeys the same projection chain rule for the actual supplied smooth base map. -/
theorem spinorPullback_mfderiv_proj (q : SpinorTotal (pullback D f)) :
    (mfderiv (spinorModel I) I (spinorCore D).proj
      (CocyclePullbackBundles.spinorMap D f q)).comp
      (mfderiv (spinorModel J) (spinorModel I) (CocyclePullbackBundles.spinorMap D f) q) =
    (mfderiv J I f q.proj).comp
      (mfderiv (spinorModel J) J (spinorCore (pullback D f)).proj q) := by
  rw [← mfderiv_comp q
    ((contMDiff_spinor_proj D).mdifferentiable hn _)
    ((CocyclePullbackBundles.contMDiff_spinorMap D f).mdifferentiable hn q)]
  exact mfderiv_comp q (f.contMDiff.mdifferentiable hn q.proj)
    ((contMDiff_spinor_proj (pullback D f)).mdifferentiable hn q)

/-- The tangent square for actual realization and canonical bundle pullback commutes, derived by differentiating the proved actual total-space realization square. -/
theorem realization_pullback_mfderiv (p : PolarTotal (pullback D f)) :
    (mfderiv (polarModel I) (spinorModel I) (totalRealization D)
      (CocyclePullbackBundles.polarMap D f p)).comp
      (mfderiv (polarModel J) (polarModel I) (CocyclePullbackBundles.polarMap D f) p) =
    (mfderiv (spinorModel J) (spinorModel I) (CocyclePullbackBundles.spinorMap D f)
      (totalRealization (pullback D f) p)).comp
      (mfderiv (polarModel J) (spinorModel J) (totalRealization (pullback D f)) p) := by
  have he : totalRealization D ∘ CocyclePullbackBundles.polarMap D f =
      CocyclePullbackBundles.spinorMap D f ∘ totalRealization (pullback D f) :=
    funext (CocyclePullbackBundles.realization_commutes D f)
  rw [← mfderiv_comp p
      ((contMDiff_totalRealization D).mdifferentiable hn _)
      ((CocyclePullbackBundles.contMDiff_polarMap D f).mdifferentiable hn p), he]
  exact mfderiv_comp p
    ((CocyclePullbackBundles.contMDiff_spinorMap D f).mdifferentiable hn _)
    ((contMDiff_totalRealization (pullback D f)).mdifferentiable hn p)
end Pullback
end FoliationQM.CocycleBundleDifferential
