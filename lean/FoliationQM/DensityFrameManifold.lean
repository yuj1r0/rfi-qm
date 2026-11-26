module
public import FoliationQM.FrameQuotientManifold
public import FoliationQM.SourceDatumManifold
public import FoliationQM.SmoothLocalDescent

/-!
# Smooth compatibility of the literal density and frame quotient

Source: v13 `prop:takabayasi`. Positive density and the natural seven-dimensional
angle/matrix sign quotient carry their independently specified intrinsic
factor atlases. Smoothness of the already constructed density splitting and
its inverse is derived by descent along the actual local diffeomorphisms.
Thus the result uses the existing product topology and product atlas, and
retains exactly the earlier homeomorphisms and polar realization formula.
Abstract Spin classification and twisted spin-bundle identification remain
separate from this concrete finite-dimensional compatibility theorem.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.DensityFrameManifold
open SourcePolarProductQuotient SourcePolarDatum PolarAmplitudeTopology
open DiracMatrices PolarSignQuotient

/-- The literal positive-density times natural frame-sign quotient. -/
abbrev Product := PositiveDensity × FrameQuotient
/-- The intrinsic product model has one density coordinate and seven frame coordinates. -/
abbrev Model := ℝ × FrameDatumManifold.Model
/-- The actual product chart codomain retains Mathlib's product tag. -/
abbrev ChartModel := ModelProd ℝ FrameDatumManifold.ChartModel
/-- The independent density and frame quotient models form the literal product model. -/
abbrev model : ModelWithCorners ℝ Model ChartModel :=
  (𝓘(ℝ, ℝ)).prod FrameDatumManifold.model

/-- The literal density-frame product is a smooth manifold of every order for its intrinsic factor atlases. -/
theorem isManifold_product (n : WithTop ℕ∞) : IsManifold model n Product := inferInstance

/-- The intrinsic density-frame product model has real dimension eight. -/
theorem model_finrank : Module.finrank ℝ Model = 8 := by
  simp [Model, Module.finrank_prod, SpecialLinearManifold.model_finrank]

/-- The actual source-to-density/frame projection is a local diffeomorphism for the intrinsic product atlases. -/
theorem splitCoordinates_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph SourceDatumManifold.model model n splitCoordinates :=
  SmoothLocalDescent.isLocalDiffeomorph_id_prodMap
    (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n)

/-- Every positive density and frame class has an actual literal source representative. -/
theorem splitCoordinates_surjective : Surjective splitCoordinates := by
  rintro ⟨rho, q⟩
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
  exact ⟨(rho, p), rfl⟩

/-- The actual existing density splitting is smooth by descent along the literal source quotient local diffeomorphism. -/
theorem contMDiff_densityProductHomeomorph (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) model n densityProductHomeomorph := by
  apply (SmoothLocalDescent.contMDiff_comp_iff
    (SourceDatumManifold.quotient_mk_isLocalDiffeomorph n) Quotient.mk_surjective).mp
  exact (splitCoordinates_isLocalDiffeomorph n).contMDiff

/-- The inverse of the actual existing density splitting is smooth by descent along the independent product of density identity and frame quotient projection. -/
theorem contMDiff_densityProductHomeomorph_symm (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, Spinor) n densityProductHomeomorph.symm := by
  apply (SmoothLocalDescent.contMDiff_comp_iff
    (splitCoordinates_isLocalDiffeomorph n) splitCoordinates_surjective).mp
  have he : densityProductHomeomorph.symm ∘ splitCoordinates =
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) := by
    funext d
    exact densityProductHomeomorph.symm_apply_apply (Quotient.mk _ d)
  rw [he]
  exact SourceDatumManifold.contMDiff_quotient_mk n

/-- The independently constructed density-product homeomorphism is a genuine diffeomorphism for the natural source quotient and intrinsic product atlases. -/
def densityProductDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Spinor) model SourcePolarQuotient.SourceQuotient Product n where
  toEquiv := densityProductHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_densityProductHomeomorph n
  contMDiff_invFun := contMDiff_densityProductHomeomorph_symm n

/-- The smooth density-product equivalence has exactly the prior natural-topology homeomorphism as its underlying map. -/
theorem densityProductDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (densityProductDiffeomorph n).toHomeomorph = densityProductHomeomorph := rfl

/-- The genuine diffeomorphism separates precisely the original density and literal angle-matrix sign class. -/
theorem densityProductDiffeomorph_mk (n : WithTop ℕ∞) (d : SourceDatum) :
    densityProductDiffeomorph n (Quotient.mk SourcePolarQuotient.signSetoid d) =
      (d.1, Quotient.mk frameSetoid d.2) := rfl

/-- The literal intrinsic density-frame product and strict regular spinors are diffeomorphic through the existing actual polar realization. -/
def productRegularDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model 𝓘(ℝ, Spinor) Product RegularSpinor n :=
  (densityProductDiffeomorph n).symm.trans (SourceQuotientManifold.regularDiffeomorph n)

/-- The product regular-spinor diffeomorphism retains exactly the earlier genuine product realization homeomorphism. -/
theorem productRegularDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (productRegularDiffeomorph n).toHomeomorph = productRegularHomeomorph := rfl

/-- Each literal density and frame representative is sent to its actual source polar realization. -/
theorem productRegularDiffeomorph_mk (n : WithTop ℕ∞) (rho : PositiveDensity) (p : FrameDatum) :
    productRegularDiffeomorph n (rho, Quotient.mk frameSetoid p) =
      SourcePolarRealization.realizeSource (rho, p) := productRegularHomeomorph_mk rho p

/-- On a real full-angle representative, the intrinsic product diffeomorphism is exactly the manuscript's polar spinor formula. -/
theorem productRegularDiffeomorph_mk_real (n : WithTop ℕ∞)
    (rho : PositiveDensity) (beta : ℝ) (A : SpecialLinearMatrix) :
    (productRegularDiffeomorph n
      (rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), A))).val =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) := by
  rw [productRegularDiffeomorph_mk]
  exact SourcePolarRealization.realizeSource_coe rho beta A

/-- Inverse smooth reconstruction recovers the invariant bilinear density, rather than the positive Hilbert norm. -/
theorem productRegularDiffeomorph_symm_density (n : WithTop ℕ∞) (q : RegularSpinor) :
    (((productRegularDiffeomorph n).symm q).1 : ℝ) =
      SpinorRegularity.invariantDensity q.val := productRegularHomeomorph_symm_density q

end FoliationQM.DensityFrameManifold
