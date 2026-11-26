module
public import FoliationQM.CliffordSpinLorentzSmooth
public import FoliationQM.QuotientManifoldAtlas
public import FoliationQM.SmoothLocalDescent

/-!
# Independent smooth actual Clifford Spin sign quotient

Source scope: the actual Spin/Lorentz identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The original group quotient
by the genuine two-sign kernel keeps its natural quotient topology.
Its charts are constructed from actual quotient local inverses followed
by the independently established Spin charts. The upstairs overlap
maps are locally identity or actual multiplication by the negative
central unit, so their regularity follows from the Spin Lie group.
No Lorentz chart is used to define this quotient atlas.

Only after constructing the quotient manifold, the existing quotient
homeomorphism is proved smooth in both directions by descent along the
two genuine local diffeomorphisms. This identifies the source-driven
sign quotient with the independently constructed Lorentz Cayley
manifold, retaining exact representative formulas and the actual
smooth two-sheeted quotient projection. No global individual Spin
representative or universal-cover assertion is inferred.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Filter Topology
namespace FoliationQM.CliffordSpinSignManifold
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup

/-- The quotient uses the genuine six-dimensional real Spin manifold model. -/
abbrev Model := CliffordSpinManifold.Model

/-- The quotient chart codomain is the same intrinsic chart space as its actual Spin covering space. -/
abbrev ChartModel := Model

/-- The source-driven sign quotient model is the independently fixed actual Spin model. -/
abbrev model := CliffordSpinLorentzSmooth.spinModel

/-- The actual quotient projection takes a genuine Clifford Spin element to its class modulo the proved sign kernel. -/
abbrev projection : Spin → SignQuotient := QuotientGroup.mk

/-- The actual central sign change is multiplication by the negative Clifford unit. -/
def signShift (s : Spin) : Spin := CliffordSpinEquivalence.negativeOne * s

/-- Multiplication by the actual negative central unit is smooth to every order in the existing Spin atlas. -/
theorem contMDiff_signShift (n : WithTop ℕ∞) : ContMDiff model model n signShift :=
  (CliffordSpinManifold.contMDiff_mul n).comp (contMDiff_const.prodMk contMDiff_id)

/-- Actual central sign multiplication leaves the genuine quotient class unchanged. -/
theorem projection_signShift (s : Spin) : projection (signShift s) = projection s :=
  (quotient_mk_eq_iff _ _).mpr (Or.inr rfl)

/-- The literal sign projection is a covering in its original quotient topology. -/
theorem projection_isCoveringMap : IsCoveringMap projection := by
  have h := lorentzHom_isCoveringMap.homeomorph_comp quotientMulHomeomorph.toHomeomorph.symm
  have he : quotientMulHomeomorph.toHomeomorph.symm ∘ lorentzHom = projection := by
    funext s
    exact quotientMulHomeomorph_symm_image s
  rwa [he] at h

/-- The literal sign projection is a local homeomorphism before any quotient atlas is selected. -/
theorem projection_isLocalHomeomorph : IsLocalHomeomorph projection :=
  projection_isCoveringMap.isLocalHomeomorph

/-- The natural actual Spin sign quotient is Hausdorff, as witnessed by its already proved topology-compatible Lorentz homeomorphism. -/
instance instT2SpaceSignQuotient : T2Space SignQuotient :=
  quotientMulHomeomorph.toHomeomorph.isEmbedding.t2Space

/-- The natural actual Spin sign quotient is second countable in its unchanged quotient topology. -/
instance instSecondCountableTopologySignQuotient : SecondCountableTopology SignQuotient := by
  let _ : SecondCountableTopology ProperFutureLorentz :=
    LorentzMatrixTopology.isClosedEmbedding_properMatrix.isEmbedding.secondCountableTopology
  exact quotientMulHomeomorph.toHomeomorph.secondCountableTopology

private theorem eventually_eq_lifts {X : Type*} [TopologicalSpace X]
    {f g : X → Spin} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h₀ : f x = g x)
    (he : (fun y => projection (f y)) =ᶠ[𝓝 x] (fun y => projection (g y))) :
    f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hx, hinj⟩ := projection_isLocalHomeomorph.isLocallyInjective (f x)
  have hfy := hf.tendsto.eventually (hU.mem_nhds hx)
  have hgx : g x ∈ U := h₀ ▸ hx
  have hgy := hg.tendsto.eventually (hU.mem_nhds hgx)
  filter_upwards [hfy, hgy, he] with y hy hz heq
  exact hinj hy hz heq

/-- Each actual local inverse followed by projection is locally identity or genuine central sign multiplication; continuity prevents arbitrary sign changes near a point. -/
theorem localInverse_comp_eventually_eq_or_shift (a x : Spin)
    (hx : projection x ∈ (projection_isLocalHomeomorph.localInverseAt a).source) :
    ((projection_isLocalHomeomorph.localInverseAt a) ∘ projection) =ᶠ[𝓝 x] id ∨
    ((projection_isLocalHomeomorph.localInverseAt a) ∘ projection) =ᶠ[𝓝 x] signShift := by
  let e := projection_isLocalHomeomorph.localInverseAt a
  let f : Spin → Spin := e ∘ projection
  have hc : ContinuousAt f x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).comp
      QuotientGroup.continuous_mk.continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, projection y ∈ e.source :=
    QuotientGroup.continuous_mk.continuousAt.tendsto.eventually (e.open_source.mem_nhds hx)
  have he : (fun y => projection (f y)) =ᶠ[𝓝 x] (fun y => projection y) := by
    filter_upwards [hnear] with y hy
    exact projection_isLocalHomeomorph.apply_localInverseAt_of_mem hy
  have h₀ : projection (f x) = projection x := he.self_of_nhds
  rcases (quotient_mk_eq_iff (f x) x).mp h₀ with h | h
  · exact Or.inl (eventually_eq_lifts hc continuousAt_id h he)
  · apply Or.inr
    apply eventually_eq_lifts hc (contMDiff_signShift 0).continuous.continuousAt h
    filter_upwards [he] with y hy
    exact hy.trans (projection_signShift y).symm

/-- The actual upstairs local-inverse transitions are smooth on their exact domains, by their locally fixed genuine sign branch. -/
theorem localInverse_comp_contMDiffOn (n : WithTop ℕ∞) (a : Spin) :
    ContMDiffOn model model n
      ((projection_isLocalHomeomorph.localInverseAt a) ∘ projection)
      (projection ⁻¹' (projection_isLocalHomeomorph.localInverseAt a).source) := by
  intro x hx
  rcases localInverse_comp_eventually_eq_or_shift a x hx with he | he
  · exact (contMDiffAt_id.congr_of_eventuallyEq he).contMDiffWithinAt
  · exact ((contMDiff_signShift n x).congr_of_eventuallyEq he).contMDiffWithinAt

/-- The actual sign quotient carries local quotient inverses followed by Spin charts, with arbitrary representatives used only to choose chart centers. -/
instance instChartedSpaceSignQuotient : ChartedSpace ChartModel SignQuotient :=
  projection_isLocalHomeomorph.chartedSpaceOfRightInverse
    (show Function.RightInverse Quotient.out projection from Quotient.out_eq)

/-- Each preferred quotient chart is exactly a genuine quotient inverse followed by the independent Spin chart at its selected representative. -/
theorem chartAt_eq (q : SignQuotient) :
    chartAt ChartModel q = (projection_isLocalHomeomorph.localInverseAt q.out).trans
      (chartAt ChartModel q.out) := rfl

/-- The actual sign-overlap proofs make the source-driven quotient atlas a real manifold to every differentiability order. -/
instance instIsManifoldSignQuotient (n : WithTop ℕ∞) : IsManifold model n SignQuotient :=
  QuotientManifoldAtlas.isManifold_of_localInverse_comp model projection_isLocalHomeomorph
    (show Function.RightInverse Quotient.out projection from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n)

/-- The independently constructed actual Spin sign quotient has real model dimension six. -/
theorem model_finrank : Module.finrank ℝ Model = 6 := CliffordSpinManifold.model_finrank

/-- The actual quotient projection is a genuine local diffeomorphism for the source-driven quotient atlas. -/
theorem projection_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph model model n projection :=
  QuotientManifoldAtlas.isLocalDiffeomorph_of_localInverse_comp model projection_isLocalHomeomorph
    (show Function.RightInverse Quotient.out projection from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n)

/-- The literal group quotient constructor is a local diffeomorphism in the genuine Spin and sign-quotient atlases. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph model model n (QuotientGroup.mk : Spin → SignQuotient) :=
  projection_isLocalDiffeomorph n

/-- The actual quotient projection is smooth to every order. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) : ContMDiff model model n projection :=
  (projection_isLocalDiffeomorph n).contMDiff

/-- Every existing topological local quotient inverse is smooth on its genuine open source. -/
theorem contMDiffOn_quotient_localInverse (n : WithTop ℕ∞) (s : Spin) :
    ContMDiffOn model model n (projection_isLocalHomeomorph.localInverseAt s)
      (projection_isLocalHomeomorph.localInverseAt s).source :=
  QuotientManifoldAtlas.contMDiffOn_localInverse_of_localInverse_comp model projection_isLocalHomeomorph
    (show Function.RightInverse Quotient.out projection from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n) s

/-- Every actual sign-projection fiber has exactly two elements, independently of the quotient atlas. -/
theorem projection_fiber_card (q : SignQuotient) : Nat.card (projection ⁻¹' {q}) = 2 := by
  have he : projection ⁻¹' {q} = lorentzHom ⁻¹' {quotientMulHomeomorph q} := by
    ext s
    change projection s = q ↔ lorentzHom s = quotientMulHomeomorph q
    exact quotientMulHomeomorph.injective.eq_iff.symm
  rw [he]
  exact lorentz_fiber_card _

/-- The original sign projection is simultaneously a natural covering, an all-order local diffeomorphism, and exactly two-to-one. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap projection ∧ IsLocalDiffeomorph model model n projection ∧
      ∀ q : SignQuotient, Nat.card (projection ⁻¹' {q}) = 2 :=
  ⟨projection_isCoveringMap, projection_isLocalDiffeomorph n, projection_fiber_card⟩

/-- The existing quotient homeomorphism is smooth by descent along the independently constructed quotient local diffeomorphism. -/
theorem contMDiff_quotientMulHomeomorph (n : WithTop ℕ∞) :
    ContMDiff model LorentzManifold.model n quotientMulHomeomorph := by
  apply (SmoothLocalDescent.contMDiff_comp_iff
    (projection_isLocalDiffeomorph n) QuotientGroup.mk_surjective).mp
  exact CliffordSpinLorentzSmooth.contMDiff_lorentzHom n

/-- The inverse quotient homeomorphism is smooth by descent along the independently proved actual Spin-to-Lorentz local diffeomorphism. -/
theorem contMDiff_quotientMulHomeomorph_symm (n : WithTop ℕ∞) :
    ContMDiff LorentzManifold.model model n quotientMulHomeomorph.symm := by
  apply (SmoothLocalDescent.contMDiff_comp_iff
    (CliffordSpinLorentzSmooth.lorentzHom_isLocalDiffeomorph n) lorentzHom_surjective).mp
  have he : quotientMulHomeomorph.symm ∘ lorentzHom = projection := by
    funext s
    exact quotientMulHomeomorph_symm_image s
  rw [he]
  exact contMDiff_quotient_mk n

/-- The source-driven actual Spin sign quotient and independent Lorentz Cayley manifold are genuinely diffeomorphic via the original quotient homeomorphism. -/
def quotientDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model LorentzManifold.model SignQuotient ProperFutureLorentz n where
  toEquiv := quotientMulHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_quotientMulHomeomorph n
  contMDiff_invFun := contMDiff_quotientMulHomeomorph_symm n

/-- The quotient diffeomorphism has exactly the original natural quotient homeomorphism underneath. -/
theorem quotientDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (quotientDiffeomorph n).toHomeomorph = quotientMulHomeomorph.toHomeomorph := rfl

/-- The diffeomorphism has the original actual Lorentz value on every sign class. -/
theorem quotientDiffeomorph_apply (n : WithTop ℕ∞) (q : SignQuotient) :
    quotientDiffeomorph n q = quotientMulHomeomorph q := rfl

/-- The smooth inverse is exactly the original sign-class-valued inverse, without choosing an individual lift. -/
theorem quotientDiffeomorph_symm_apply (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    (quotientDiffeomorph n).symm L = quotientMulHomeomorph.symm L := rfl

/-- A represented actual Spin sign class maps to precisely its original Clifford Lorentz image. -/
theorem quotientDiffeomorph_mk (n : WithTop ℕ∞) (s : Spin) :
    quotientDiffeomorph n (projection s) = lorentzHom s := rfl

/-- Inverse smooth reconstruction of a displayed actual Lorentz lift returns exactly its genuine sign class. -/
theorem quotientDiffeomorph_symm_image (n : WithTop ℕ∞) (s : Spin) :
    (quotientDiffeomorph n).symm (lorentzHom s) = projection s :=
  quotientMulHomeomorph_symm_image s

end FoliationQM.CliffordSpinSignManifold
