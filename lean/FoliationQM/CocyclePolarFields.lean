module
public import FoliationQM.PolarTransitionCocycle

/-!
# Compatible smooth local polar and spinor families

Source: the supplied-transition interpretation of v13 `prop:takabayasi`
and the literal formula `eq:takabayasi_polar`. Each local field is a
bundled smooth map on the actual open subtype of its cover domain.
Polar compatibility and represented-spinor compatibility are defined
independently using their already constructed actual matrix actions.
Their genuine equivalence follows from actual realization equivariance,
with the original bilinear invariant density recovered pointwise.

The results concern compatible local families for the supplied smooth
transition cocycle. They do not choose global individual angle or matrix
representatives, construct a spacetime Spin structure, or assert a
classification of arbitrary twisted bundles.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocyclePolarFields
open DiracMatrices PolarSignQuotient PolarAmplitudeTopology SourcePolarDatum
open SourcePolarProductQuotient

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞} (D : PolarTransitionCocycle.Data I B ι n)

/-- A family of genuine bundled smooth polar fields, each defined only on its actual open chart domain. -/
abbrev RawPolarFamily := ∀ i : ι,
  C^n⟮I, ↥(D.domain i); DensityFrameManifold.model, DensityFrameManifold.Product⟯

/-- A family of genuine bundled smooth regular-spinor fields on the actual open chart domains. -/
abbrev RawSpinorFamily := ∀ i : ι,
  C^n⟮I, ↥(D.domain i); 𝓘(ℝ, Spinor), RegularSpinor⟯

/-- Independent polar compatibility means that the later chart value is the actual left matrix action of the supplied transition on the earlier chart value. -/
def PolarCompatible (f : RawPolarFamily D) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j),
    f j ⟨x, hj⟩ = DensityFrameAction.productAction (D.transition i j x) (f i ⟨x, hi⟩)

/-- Independent spinor compatibility uses the actual represented matrix action on the original spinor, with the same chart-change orientation. -/
def SpinorCompatible (psi : RawSpinorFamily D) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j),
    psi j ⟨x, hj⟩ = RegularSpinorAction.act (D.transition i j x) (psi i ⟨x, hi⟩)

/-- Smooth polar local families satisfying the independently stated transition compatibility. -/
def SmoothPolarFamily := {f : RawPolarFamily D // PolarCompatible D f}

/-- Smooth regular-spinor local families satisfying the independently stated represented transition compatibility. -/
def SmoothSpinorFamily := {psi : RawSpinorFamily D // SpinorCompatible D psi}

/-- Pointwise actual polar realization preserves the independently defined compatibility relation. -/
theorem realization_compatible {f : RawPolarFamily D} (hf : PolarCompatible D f) :
    SpinorCompatible D (fun i => DensityFrameFields.fieldEquiv n (f i)) := by
  intro i j x hi hj
  change productRegularHomeomorph (f j ⟨x, hj⟩) =
    RegularSpinorAction.act (D.transition i j x) (productRegularHomeomorph (f i ⟨x, hi⟩))
  rw [hf i j x hi hj]
  exact RegularSpinorAction.realization_equivariant _ _

/-- Actual inverse polar reconstruction preserves compatibility, by its proved equivariance under the represented transition matrices. -/
theorem reconstruction_compatible {psi : RawSpinorFamily D} (hpsi : SpinorCompatible D psi) :
    PolarCompatible D (fun i => (DensityFrameFields.fieldEquiv n).symm (psi i)) := by
  intro i j x hi hj
  change productRegularHomeomorph.symm (psi j ⟨x, hj⟩) =
    DensityFrameAction.productAction (D.transition i j x)
      (productRegularHomeomorph.symm (psi i ⟨x, hi⟩))
  rw [hpsi i j x hi hj]
  exact RegularSpinorAction.reconstruction_equivariant _ _

/-- Actual fiber realization is an equivalence of compatible bundled smooth local families on the supplied open cover. -/
def realizationEquiv : SmoothPolarFamily D ≃ SmoothSpinorFamily D where
  toFun f := ⟨fun i => DensityFrameFields.fieldEquiv n (f.val i),
    realization_compatible D f.property⟩
  invFun psi := ⟨fun i => (DensityFrameFields.fieldEquiv n).symm (psi.val i),
    reconstruction_compatible D psi.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact (DensityFrameFields.fieldEquiv n).symm_apply_apply (f.val i)
  right_inv psi := by
    apply Subtype.ext
    funext i
    exact (DensityFrameFields.fieldEquiv n).apply_symm_apply (psi.val i)

/-- The family equivalence realizes the exact pre-existing density-frame product at each point of each open chart. -/
theorem realizationEquiv_apply (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    (realizationEquiv D f).val i x = productRegularHomeomorph (f.val i x) := rfl

/-- The inverse family equivalence is exactly the pre-existing inverse product realization at every local point. -/
theorem realizationEquiv_symm_apply (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    ((realizationEquiv D).symm psi).val i x = productRegularHomeomorph.symm (psi.val i x) := rfl

/-- Reconstructing after realization returns the same compatible polar family, including its actual local domains. -/
theorem realizationEquiv_symm_apply_apply (f : SmoothPolarFamily D) :
    (realizationEquiv D).symm (realizationEquiv D f) = f :=
  (realizationEquiv D).symm_apply_apply f

/-- Realizing the reconstructed compatible polar family returns the original compatible spinor family. -/
theorem realizationEquiv_apply_symm_apply (psi : SmoothSpinorFamily D) :
    realizationEquiv D ((realizationEquiv D).symm psi) = psi :=
  (realizationEquiv D).apply_symm_apply psi

/-- Actual local realization recovers exactly the positive-density coordinate as the spinor's bilinear invariant density. -/
theorem realizationEquiv_density (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    SpinorRegularity.invariantDensity ((realizationEquiv D f).val i x).val =
      ((f.val i x).1 : ℝ) :=
  density_productRegularHomeomorph (f.val i x)

/-- Actual inverse local reconstruction has real density equal to the original spinor's bilinear invariant density. -/
theorem realizationEquiv_symm_density (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    ((((realizationEquiv D).symm psi).val i x).1 : ℝ) =
      SpinorRegularity.invariantDensity (psi.val i x).val :=
  productRegularHomeomorph_symm_density (psi.val i x)

/-- Compatible polar fields have equal actual positive-density coordinates on every overlap. -/
theorem polar_density_overlap (f : SmoothPolarFamily D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (f.val j ⟨x, hj⟩).1 = (f.val i ⟨x, hi⟩).1 := by
  rw [f.property i j x hi hj]
  rfl

/-- Compatible represented-spinor fields have equal actual bilinear invariant densities on overlaps. -/
theorem spinor_density_overlap (psi : SmoothSpinorFamily D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    SpinorRegularity.invariantDensity (psi.val j ⟨x, hj⟩).val =
      SpinorRegularity.invariantDensity (psi.val i ⟨x, hi⟩).val := by
  rw [psi.property i j x hi hj]
  exact RegularSpinorAction.invariantDensity_act _ _

/-- At any literal local real-angle representative, actual family realization equals the source polar-spinor expression. -/
theorem realizationEquiv_mk_real (f : SmoothPolarFamily D) (i : ι) (x : D.domain i)
    (rho : PositiveDensity) (beta : ℝ) (A : SpecialLinearMatrix)
    (hx : f.val i x = (rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), A))) :
    ((realizationEquiv D f).val i x).val =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) := by
  rw [realizationEquiv_apply, hx]
  exact DensityFrameManifold.productRegularDiffeomorph_mk_real n rho beta A

/-- Each compatible smooth spinor family has one and only one compatible quotient-valued polar family with the same actual local realizations. -/
theorem existsUnique_polarFamily (psi : SmoothSpinorFamily D) :
    ∃! f : SmoothPolarFamily D, ∀ (i : ι) (x : D.domain i),
      productRegularHomeomorph (f.val i x) = psi.val i x := by
  refine ⟨(realizationEquiv D).symm psi, ?_, ?_⟩
  · intro i x
    exact productRegularHomeomorph.apply_symm_apply (psi.val i x)
  · intro f hf
    apply (realizationEquiv D).injective
    rw [realizationEquiv_apply_symm_apply]
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    exact hf i x

end FoliationQM.CocyclePolarFields
