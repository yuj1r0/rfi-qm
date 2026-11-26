module
public import FoliationQM.DensityFrameManifold
public import FoliationQM.PolarCoveringDifferential
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
/-!
# Actual density-frame tangent splitting and field derivatives

Source: the density-separated concrete polar decomposition in v13
`prop:takabayasi`. The existing density-product and regular-spinor
homeomorphisms have already been proved to be genuine diffeomorphisms
for their independent intrinsic atlases. Their actual manifold Frechet
derivatives, including inverse reconstruction, are packaged here as
continuous-linear tangent equivalences at explicit nonzero orders. The
actual seven-dimensional frame covering has the same derivative
invertibility property. All underlying maps remain the literal prior
maps, with exact derivative identifications.

The intrinsic product tangent splitting is verified against the actual
derivatives of the two factor projections. The positive-density value
map has identity derivative because its actual chart is the real
inclusion. Chain rules then identify the first component of inverse
reconstruction with the derivative of the bilinear invariant density.
The statements also cover genuine differentiable fields on manifold
sources and ordinary Frechet derivatives on normed source spaces. No
supplied derivative equality, global individual representative,
positive-definite kinetic claim, or field equation is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.DensityFrameDifferential
open DiracMatrices PolarSignQuotient SourcePolarProductQuotient PolarAmplitudeTopology
open DensityFrameManifold

/-- The actual derivative of the existing density-product diffeomorphism is a tangent continuous-linear equivalence at every nonzero differentiability order. -/
def densityProductTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : SourcePolarQuotient.SourceQuotient) :
    TangentSpace 𝓘(ℝ, Spinor) q ≃L[ℝ]
      TangentSpace model (densityProductHomeomorph q) :=
  (densityProductDiffeomorph n).mfderivToContinuousLinearEquiv hn q

/-- The density-product tangent equivalence has precisely the actual derivative of the existing density-product homeomorphism as its underlying map. -/
theorem densityProductTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : SourcePolarQuotient.SourceQuotient) :
    (densityProductTangentEquiv n hn q).toContinuousLinearMap =
      mfderiv 𝓘(ℝ, Spinor) model densityProductHomeomorph q :=
  (densityProductDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn

/-- The actual manifold derivative of density splitting is invertible at every source class for each stated nonzero order. -/
theorem densityProduct_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : SourcePolarQuotient.SourceQuotient) :
    (mfderiv 𝓘(ℝ, Spinor) model densityProductHomeomorph q).IsInvertible :=
  (densityProductDiffeomorph n).isInvertible_mfderiv hn

/-- The actual derivative of the existing density-frame realization is a continuous-linear equivalence of its intrinsic product and regular-spinor tangent spaces. -/
def productRegularTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (p : Product) :
    TangentSpace model p ≃L[ℝ] TangentSpace 𝓘(ℝ, Spinor) (productRegularHomeomorph p) :=
  (productRegularDiffeomorph n).mfderivToContinuousLinearEquiv hn p

/-- The product-realization tangent equivalence is exactly the actual manifold derivative of the pre-existing regular-spinor realization map. -/
theorem productRegularTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0)
    (p : Product) :
    (productRegularTangentEquiv n hn p).toContinuousLinearMap =
      mfderiv model 𝓘(ℝ, Spinor) productRegularHomeomorph p :=
  (productRegularDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn

/-- The actual derivative of density-frame realization is invertible at every product point for each stated nonzero order. -/
theorem productRegular_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (p : Product) :
    (mfderiv model 𝓘(ℝ, Spinor) productRegularHomeomorph p).IsInvertible :=
  (productRegularDiffeomorph n).isInvertible_mfderiv hn

/-- The actual derivative of inverse regular-spinor reconstruction is a continuous-linear equivalence into the intrinsic density-frame tangent space. -/
def inverseRegularTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (q : RegularSpinor) :
    TangentSpace 𝓘(ℝ, Spinor) q ≃L[ℝ]
      TangentSpace model (productRegularHomeomorph.symm q) :=
  (productRegularDiffeomorph n).symm.mfderivToContinuousLinearEquiv hn q

/-- The inverse reconstruction tangent equivalence has exactly the actual derivative of the existing inverse homeomorphism as its underlying map. -/
theorem inverseRegularTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : RegularSpinor) :
    (inverseRegularTangentEquiv n hn q).toContinuousLinearMap =
      mfderiv 𝓘(ℝ, Spinor) model productRegularHomeomorph.symm q :=
  (productRegularDiffeomorph n).symm.mfderivToContinuousLinearEquiv_coe hn

/-- The actual derivative of the seven-dimensional frame sign projection is a continuous-linear tangent equivalence for each stated nonzero order. -/
def frameTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (p : FrameDatum) :
    TangentSpace FrameDatumManifold.model p ≃L[ℝ]
      TangentSpace FrameDatumManifold.model (Quotient.mk frameSetoid p) :=
  (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn p

/-- The frame-covering tangent equivalence is exactly the actual derivative of the literal angle-matrix quotient projection. -/
theorem frameTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0)
    (p : FrameDatum) :
    (frameTangentEquiv n hn p).toContinuousLinearMap =
      mfderiv FrameDatumManifold.model FrameDatumManifold.model
        (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) p :=
  (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn p

/-- The actual derivative of the seven-dimensional frame covering projection is invertible at every representative for each stated nonzero order. -/
theorem frame_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (p : FrameDatum) :
    (mfderiv FrameDatumManifold.model FrameDatumManifold.model
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) p).IsInvertible :=
  (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n).isInvertible_mfderiv hn p

/-- The intrinsic product tangent space splits canonically into the positive-density and frame-quotient tangent spaces under the actual product atlas. -/
def productTangentSplit (p : Product) : TangentSpace model p ≃L[ℝ]
    (TangentSpace 𝓘(ℝ, ℝ) p.1 × TangentSpace FrameDatumManifold.model p.2) :=
  ContinuousLinearEquiv.refl ℝ _

/-- The canonical product tangent splitting evaluates to the actual manifold derivatives of the density and frame projection maps. -/
theorem productTangentSplit_apply (p : Product) (v : TangentSpace model p) :
    productTangentSplit p v =
      (mfderiv model 𝓘(ℝ, ℝ) (Prod.fst : Product → PositiveDensity) p v,
        mfderiv model FrameDatumManifold.model (Prod.snd : Product → FrameQuotient) p v) := by
  rw [mfderiv_fst, mfderiv_snd]
  rfl

/-- The actual positive-density scalar value map has identity derivative because its intrinsic chart is precisely the real inclusion. -/
theorem density_value_mfderiv (rho : PositiveDensity) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : PositiveDensity → ℝ) rho =
      ContinuousLinearMap.id ℝ ℝ := by
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) rho) rho = _
  exact mfderiv_extChartAt_self

/-- The density component of the actual inverse reconstruction derivative is exactly the manifold derivative of the bilinear invariant density. -/
theorem inverse_density_derivative (n : WithTop ℕ∞) (hn : n ≠ 0)
    (q : RegularSpinor) (v : TangentSpace 𝓘(ℝ, Spinor) q) :
    (productTangentSplit (productRegularHomeomorph.symm q)
      (inverseRegularTangentEquiv n hn q v)).1 =
      mfderiv 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ)
        (fun r : RegularSpinor => SpinorRegularity.invariantDensity r.val) q v := by
  have hR : MDifferentiableAt 𝓘(ℝ, Spinor) model productRegularHomeomorph.symm q :=
    (productRegularDiffeomorph n).symm.contMDiff.mdifferentiable hn q
  have hfst := mdifferentiableAt_fst.comp q hR
  have hval := (PolarScalarManifolds.contMDiff_density_value n).mdifferentiable hn
    (productRegularHomeomorph.symm q).1
  have heq : (fun r : RegularSpinor => SpinorRegularity.invariantDensity r.val) =
      (Subtype.val : PositiveDensity → ℝ) ∘ Prod.fst ∘ productRegularHomeomorph.symm := by
    funext r
    exact (productRegularHomeomorph_symm_density r).symm
  rw [heq, mfderiv_comp q hval hfst, density_value_mfderiv]
  change (inverseRegularTangentEquiv n hn q v).1 =
    mfderiv 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ) (Prod.fst ∘ productRegularHomeomorph.symm) q v
  rw [mfderiv_comp q mdifferentiableAt_fst hR, mfderiv_fst]
  change (inverseRegularTangentEquiv n hn q v).1 =
    (mfderiv 𝓘(ℝ, Spinor) model productRegularHomeomorph.symm q v).1
  rw [← inverseRegularTangentEquiv_toContinuousLinearMap n hn q]
  rfl

/-- The actual frame quotient tangent space has seven real dimensions at every class. -/
theorem frame_tangent_finrank (q : FrameQuotient) :
    Module.finrank ℝ (TangentSpace FrameDatumManifold.model q) = 7 := by
  change Module.finrank ℝ FrameDatumManifold.Model = 7
  exact FrameDatumManifold.model_finrank

/-- The intrinsic density-frame product tangent space has eight real dimensions at every product point. -/
theorem product_tangent_finrank (p : Product) :
    Module.finrank ℝ (TangentSpace model p) = 8 := by
  change Module.finrank ℝ Model = 8
  exact DensityFrameManifold.model_finrank

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Inverse reconstruction of an actual differentiable regular-spinor field obeys the genuine manifold chain rule with the proved tangent equivalence. -/
theorem mfderiv_reconstruction_comp (n : WithTop ℕ∞) (hn : n ≠ 0)
    {psi : M → RegularSpinor} {x : M}
    (hpsi : MDifferentiableAt I 𝓘(ℝ, Spinor) psi x) :
    mfderiv I model (productRegularHomeomorph.symm ∘ psi) x =
      (inverseRegularTangentEquiv n hn (psi x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, Spinor) psi x) := by
  rw [inverseRegularTangentEquiv_toContinuousLinearMap]
  have hR : MDifferentiableAt 𝓘(ℝ, Spinor) model productRegularHomeomorph.symm (psi x) :=
    (productRegularDiffeomorph n).symm.contMDiff.mdifferentiable hn (psi x)
  exact mfderiv_comp x hR hpsi

/-- Realization of an actual differentiable density-frame field obeys the genuine manifold chain rule with the proved realization tangent equivalence. -/
theorem mfderiv_realization_comp (n : WithTop ℕ∞) (hn : n ≠ 0)
    {p : M → Product} {x : M} (hp : MDifferentiableAt I model p x) :
    mfderiv I 𝓘(ℝ, Spinor) (productRegularHomeomorph ∘ p) x =
      (productRegularTangentEquiv n hn (p x)).toContinuousLinearMap.comp
        (mfderiv I model p x) := by
  rw [productRegularTangentEquiv_toContinuousLinearMap]
  have hR : MDifferentiableAt model 𝓘(ℝ, Spinor) productRegularHomeomorph (p x) :=
    (productRegularDiffeomorph n).contMDiff.mdifferentiable hn (p x)
  exact mfderiv_comp x hR hp

/-- For an actual differentiable field on any charted source, the reconstructed first tangent component equals the derivative of its actual invariant density field. -/
theorem inverse_density_derivative_comp (n : WithTop ℕ∞) (hn : n ≠ 0)
    {psi : M → RegularSpinor} {x : M}
    (hpsi : MDifferentiableAt I 𝓘(ℝ, Spinor) psi x) (v : TangentSpace I x) :
    (productTangentSplit (productRegularHomeomorph.symm (psi x))
      (inverseRegularTangentEquiv n hn (psi x)
        (mfderiv I 𝓘(ℝ, Spinor) psi x v))).1 =
      mfderiv I 𝓘(ℝ, ℝ)
        (fun y => SpinorRegularity.invariantDensity (psi y).val) x v := by
  rw [inverse_density_derivative]
  have hrho : MDifferentiableAt 𝓘(ℝ, Spinor) 𝓘(ℝ, ℝ)
      (fun q : RegularSpinor => SpinorRegularity.invariantDensity q.val) (psi x) :=
    ((SpinorMatrixSmooth.contDiffAt_invariantDensity n (psi x).property).contMDiffAt.mdifferentiableAt hn).comp
      (x := psi x) ((RegularSpinorManifold.contMDiff_value n).mdifferentiable hn (psi x))
  exact (mfderiv_comp_apply x hrho hpsi v).symm

end Fields

/-- On a real normed source, the reconstructed first tangent component equals the ordinary Frechet derivative of the actual invariant density field. -/
theorem inverse_density_fderiv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : WithTop ℕ∞) (hn : n ≠ 0) {psi : E → RegularSpinor} {x : E}
    (hpsi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Spinor) psi x) (v : E) :
    (productTangentSplit (productRegularHomeomorph.symm (psi x))
      (inverseRegularTangentEquiv n hn (psi x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Spinor) psi x
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v)))).1 =
      fderiv ℝ (fun y => SpinorRegularity.invariantDensity (psi y).val) x v := by
  rw [inverse_density_derivative_comp n hn hpsi]
  rw [mfderiv_eq_fderiv]
  rfl

end FoliationQM.DensityFrameDifferential
