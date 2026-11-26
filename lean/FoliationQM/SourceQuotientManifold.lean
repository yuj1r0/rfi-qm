module
public import FoliationQM.RegularSpinorManifold
public import FoliationQM.SourcePolarSmooth
public import FoliationQM.PolarManifoldCharts
public import FoliationQM.PolarQuotientManifold
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The literal source quotient as a real smooth manifold

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The literal
positive-density, four-pi-angle and determinant-one matrix sign quotient
retains its established natural quotient topology. Its actual realization
is an open embedding into the real eight-dimensional spinor space. The
resulting explicit singleton atlas gives a Hausdorff, second-countable
manifold to every differentiability order. Its exact range is the strict
invariant-regular domain, and real representatives evaluate to the genuine
polar spinor expression.

The existing source realization and amplitude-quotient homeomorphisms
become genuine bundled diffeomorphisms for the specified atlases. For
normed source domains, manifold smoothness is proved equivalent to the
independently defined local smooth density, real angle and matrix
representative condition. The real angle is reduced modulo four pi in
the literal source class, with positivity and determinant one required
throughout a neighborhood. Global and open-domain criteria preserve
these local representative conditions.

This module specifies the quotient atlas and verifies its compatibility
with the independent source-coordinate criterion. It does not assign an
atlas to the separate density-times-frame-quotient product, construct an
intrinsic determinant-one matrix atlas, choose a global representative,
or identify the concrete representation with an abstract Spin group.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.SourceQuotientManifold
open DiracMatrices PolarSignQuotient SourcePolarQuotient

/-- The natural source quotient is nonempty because its actual homeomorphism has a nonempty regular-spinor target. -/
instance instNonemptySourceQuotient : Nonempty SourceQuotient :=
  Nonempty.map regularHomeomorph.symm inferInstance

/-- The independently established natural source quotient topology is Hausdorff by its actual regular-spinor embedding. -/
instance instT2SpaceSourceQuotient : T2Space SourceQuotient :=
  regularHomeomorph.isEmbedding.t2Space

/-- The natural source quotient topology is second countable through its existing homeomorphism to the regular-spinor subtype. -/
instance instSecondCountableTopologySourceQuotient : SecondCountableTopology SourceQuotient :=
  regularHomeomorph.secondCountableTopology

/-- The actual ambient spinor of a literal source quotient class, using the previously constructed realization. -/
def value (q : SourceQuotient) : Spinor := (regularHomeomorph q).val

/-- The actual source realization is an open embedding for the existing natural quotient topology. -/
theorem isOpenEmbedding_value : IsOpenEmbedding value :=
  RegularSpinorManifold.isOpenEmbedding_value.comp regularHomeomorph.isOpenEmbedding

/-- The actual realization range consists exactly of the strict invariant-regular spinors. -/
theorem range_value : Set.range value = {psi : Spinor | SpinorRegularity.Regular psi} := by
  ext psi
  constructor
  · rintro ⟨q, rfl⟩
    exact (regularHomeomorph q).property
  · intro hpsi
    exact ⟨regularHomeomorph.symm ⟨psi, hpsi⟩,
      congrArg Subtype.val (regularHomeomorph.apply_symm_apply ⟨psi, hpsi⟩)⟩

/-- A literal positive-density, real-angle and determinant-one matrix representative evaluates to the genuine polar spinor with its angle reduced modulo four pi. -/
theorem value_mk_real (rho : PolarAmplitudeTopology.PositiveDensity) (beta : ℝ)
    (A : SourcePolarDatum.SpecialLinearMatrix) :
    value (Quotient.mk SourcePolarQuotient.signSetoid (rho, (beta : ChiralAngleCircle.Angle), A)) =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) :=
  SourcePolarRealization.realizeSource_coe rho beta A

/-- The actual open realization supplies an explicit singleton atlas on the existing natural source quotient topology. -/
instance instChartedSpaceSourceQuotient : ChartedSpace Spinor SourceQuotient :=
  isOpenEmbedding_value.singletonChartedSpace

/-- The actual source quotient atlas is a real manifold to every differentiability order, with the real eight-dimensional spinor model. -/
instance instIsManifoldSourceQuotient (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ, Spinor) n SourceQuotient :=
  isOpenEmbedding_value.isManifold_singleton

/-- Every preferred source quotient chart is the actual realized-spinor map. -/
theorem chartAt_value (q : SourceQuotient) :
    (chartAt Spinor q : SourceQuotient → Spinor) = value := rfl

/-- The actual source quotient chart is defined on the entire source quotient. -/
theorem chartAt_source (q : SourceQuotient) :
    (chartAt Spinor q).source = Set.univ := rfl

/-- The target of every actual source quotient chart is precisely the strict invariant-regular spinor domain. -/
theorem chartAt_target (q : SourceQuotient) :
    (chartAt Spinor q).target = {psi : Spinor | SpinorRegularity.Regular psi} := by
  change (isOpenEmbedding_value.toOpenPartialHomeomorph value).target = _
  rw [isOpenEmbedding_value.toOpenPartialHomeomorph_target value]
  exact range_value

/-- The actual ambient realization of a source quotient class is manifold-smooth to every order. -/
theorem contMDiff_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n value :=
  contMDiff_isOpenEmbedding isOpenEmbedding_value

/-- The actual source realization and its previously constructed inverse form a bundled diffeomorphism for the stated source quotient and regular-spinor atlases. -/
def regularDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) SourceQuotient RegularSpinor n where
  toEquiv := regularHomeomorph.toEquiv
  contMDiff_toFun := by
    apply ContMDiff.of_comp_isOpenEmbedding RegularSpinorManifold.isOpenEmbedding_value
    exact contMDiff_value n
  contMDiff_invFun := by
    apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_value
    have he : value ∘ regularHomeomorph.symm = (Subtype.val : RegularSpinor → Spinor) := by
      funext q
      exact congrArg Subtype.val (regularHomeomorph.apply_symm_apply q)
    change ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n (value ∘ regularHomeomorph.symm)
    rw [he]
    exact RegularSpinorManifold.contMDiff_value n

/-- The bundled source diffeomorphism evaluates to the existing actual source realization homeomorphism. -/
theorem regularDiffeomorph_apply (n : WithTop ℕ∞) (q : SourceQuotient) :
    regularDiffeomorph n q = regularHomeomorph q := rfl

/-- The inverse bundled source diffeomorphism evaluates to the existing reconstructed literal source class. -/
theorem regularDiffeomorph_symm_apply (n : WithTop ℕ∞) (q : RegularSpinor) :
    (regularDiffeomorph n).symm q = regularHomeomorph.symm q := rfl

/-- The bundled source diffeomorphism has exactly the earlier natural source realization homeomorphism as its underlying map. -/
theorem regularDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (regularDiffeomorph n).toHomeomorph = regularHomeomorph := rfl

/-- The literal source quotient and amplitude sign quotient are genuinely diffeomorphic through their actual realized-spinor diffeomorphisms. -/
def amplitudeDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) SourceQuotient PolarQuotient n :=
  (regularDiffeomorph n).trans (PolarQuotientManifold.regularDiffeomorph n).symm

/-- The source-to-amplitude diffeomorphism is the independently constructed coordinate quotient homeomorphism on every class. -/
theorem amplitudeDiffeomorph_apply (n : WithTop ℕ∞) (q : SourceQuotient) :
    amplitudeDiffeomorph n q = quotientHomeomorph q := by
  change ofRegular (toRegular (quotientHomeomorph q)) = quotientHomeomorph q
  exact ofRegular_toRegular _

/-- The bundled source-to-amplitude diffeomorphism has exactly the previously proved natural coordinate quotient homeomorphism as its underlying map. -/
theorem amplitudeDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (amplitudeDiffeomorph n).toHomeomorph = quotientHomeomorph := by
  ext q
  exact amplitudeDiffeomorph_apply n q

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For arbitrary source subsets, manifold smoothness into the source quotient is exactly ordinary real smoothness of its actual realized-spinor coordinates. -/
theorem contMDiffWithinAt_iff_contDiffWithinAt (n : WithTop ℕ∞)
    (f : E → SourceQuotient) (s : Set E) (x : E) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f s x ↔
      ContDiffWithinAt ℝ n (value ∘ f) s x :=
  PolarManifoldCharts.contMDiffWithinAt_iff_contDiffWithinAt isOpenEmbedding_value

/-- Pointwise manifold smoothness into the source quotient is exactly actual ambient real smoothness of the realized spinor. -/
theorem contMDiffAt_iff_contDiffAt (n : WithTop ℕ∞)
    (f : E → SourceQuotient) (x : E) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f x ↔
      ContDiffAt ℝ n (value ∘ f) x :=
  PolarManifoldCharts.contMDiffAt_iff_contDiffAt isOpenEmbedding_value

/-- Pointwise manifold smoothness is equivalent to the independent existence of local smooth real density, real angle and matrix fields representing the literal source class. -/
theorem contMDiffAt_iff_sourceRepresentative (n : WithTop ℕ∞)
    (f : E → SourceQuotient) (x : E) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f x ↔
      SourcePolarSmooth.HasSmoothSourceRepresentativeAt n f x := by
  rw [contMDiffAt_iff_contDiffAt]
  exact (SourcePolarSmooth.hasSmoothSourceRepresentativeAt_iff n f x).symm

/-- Global manifold smoothness into the source quotient is equivalent to independent local smooth literal source representatives at every point. -/
theorem contMDiff_iff_sourceRepresentatives (n : WithTop ℕ∞)
    (f : E → SourceQuotient) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f ↔
      ∀ x, SourcePolarSmooth.HasSmoothSourceRepresentativeAt n f x := by
  constructor
  · intro h x
    exact (contMDiffAt_iff_sourceRepresentative n f x).mp h.contMDiffAt
  · intro h x
    exact (contMDiffAt_iff_sourceRepresentative n f x).mpr (h x)

/-- On an open normed domain, manifold smoothness into the source quotient is equivalent to independent local smooth literal source representatives at every point of that domain. -/
theorem contMDiffOn_iff_sourceRepresentatives (n : WithTop ℕ∞)
    (f : E → SourceQuotient) {U : Set E} (hU : IsOpen U) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f U ↔
      ∀ x ∈ U, SourcePolarSmooth.HasSmoothSourceRepresentativeAt n f x := by
  exact (PolarManifoldCharts.contMDiffOn_iff_contDiffOn (n := n) (g := f) (t := U)
    isOpenEmbedding_value).trans
      (SourcePolarSmooth.hasSmoothSourceRepresentativeAt_on_iff n f hU).symm

end FoliationQM.SourceQuotientManifold
