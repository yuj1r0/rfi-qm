module
public import FoliationQM.FrameDatumManifold
public import FoliationQM.FrameQuotientCovering
public import FoliationQM.QuotientManifoldAtlas
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
/-!
# The intrinsic seven-dimensional frame sign quotient

Source: the density-separated angle/matrix factor in v13
`prop:takabayasi` and `eq:takabayasi_polar`. The existing natural frame
quotient topology is unchanged. Its actual covering projection supplies
local inverse maps, which are followed by the independently constructed
intrinsic angle-matrix charts. Arbitrary quotient representatives choose
chart centers only; no globally continuous representative is assumed.

The transition regularity is derived from the actual sign fibers. Every
local-inverse/projection overlap is locally the identity or the genuine
smooth simultaneous two-pi shift and matrix negation. Continuity and
local injectivity prove that the sign cannot vary arbitrarily near the
point. The resulting actual overlap maps are therefore smooth, supplying
a real manifold to every order with the seven-dimensional intrinsic
frame model. No eight-dimensional full-quotient chart is transported.

The actual quotient projection and its genuine local inverse maps are
smooth, so the projection is a local diffeomorphism. Its established
natural covering property and exactly two-point fibers are retained.
Hausdorffness and second countability are the independently derived
natural-topology instances from `FrameQuotientCovering`. No abstract
Spin classification, global representative, or dynamical assertion is
used in the construction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Filter Topology
namespace FoliationQM.FrameQuotientManifold
open SourcePolarProductQuotient FrameQuotientCovering
/-- The quotient uses the actual seven-dimensional real normed angle-matrix model. -/
abbrev Model := FrameDatumManifold.Model
/-- The quotient uses the same intrinsic angle-matrix chart codomain as its actual covering space. -/
abbrev ChartModel := FrameDatumManifold.ChartModel
/-- The quotient model with corners is the independently specified intrinsic angle-matrix product model. -/
abbrev model := FrameDatumManifold.model

private theorem eventually_eq_lifts {X : Type*} [TopologicalSpace X]
    {f g : X → FrameDatum} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h₀ : f x = g x)
    (he : (fun y => Quotient.mk frameSetoid (f y)) =ᶠ[𝓝 x]
      (fun y => Quotient.mk frameSetoid (g y))) : f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hx, hinj⟩ := frame_mk_isLocalHomeomorph.isLocallyInjective (f x)
  have hfy := hf.tendsto.eventually (hU.mem_nhds hx)
  have hgx : g x ∈ U := h₀ ▸ hx
  have hgy := hg.tendsto.eventually (hU.mem_nhds hgx)
  filter_upwards [hfy, hgy, he] with y hy hz heq
  exact hinj hy hz heq

/-- At every point in its actual domain, a local inverse followed after the quotient projection is locally exactly the identity or the literal simultaneous sign shift. -/
theorem localInverse_comp_eventually_eq_or_shift (a x : FrameDatum)
    (hx : Quotient.mk frameSetoid x ∈ (frame_mk_isLocalHomeomorph.localInverseAt a).source) :
    ((frame_mk_isLocalHomeomorph.localInverseAt a) ∘ Quotient.mk frameSetoid) =ᶠ[𝓝 x] id ∨
    ((frame_mk_isLocalHomeomorph.localInverseAt a) ∘ Quotient.mk frameSetoid) =ᶠ[𝓝 x] frameShift := by
  let e := frame_mk_isLocalHomeomorph.localInverseAt a
  let f : FrameDatum → FrameDatum := e ∘ Quotient.mk frameSetoid
  have hc : ContinuousAt f x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).comp
      continuous_quotient_mk'.continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, Quotient.mk frameSetoid y ∈ e.source :=
    continuous_quotient_mk'.continuousAt.tendsto.eventually (e.open_source.mem_nhds hx)
  have he : (fun y => Quotient.mk frameSetoid (f y)) =ᶠ[𝓝 x]
      (fun y => Quotient.mk frameSetoid y) := by
    filter_upwards [hnear] with y hy
    exact frame_mk_isLocalHomeomorph.apply_localInverseAt_of_mem hy
  have h₀ : Quotient.mk frameSetoid (f x) = Quotient.mk frameSetoid x := he.self_of_nhds
  rcases (frame_mk_eq_iff (f x) x).mp h₀ with h | h
  · exact Or.inl (eventually_eq_lifts hc continuousAt_id h he)
  · apply Or.inr
    apply eventually_eq_lifts hc continuous_frameShift.continuousAt h
    filter_upwards [he] with y hy
    exact hy.trans (frame_mk_shift y).symm

/-- Every actual local-inverse/projection overlap is smooth on its exact natural domain, derived from its locally constant sign branch and genuine smooth shift. -/
theorem localInverse_comp_contMDiffOn (n : WithTop ℕ∞)
    (a : FrameDatum) :
    ContMDiffOn model model n
      ((frame_mk_isLocalHomeomorph.localInverseAt a) ∘ Quotient.mk frameSetoid)
      ((Quotient.mk frameSetoid) ⁻¹' (frame_mk_isLocalHomeomorph.localInverseAt a).source) := by
  intro x hx
  rcases localInverse_comp_eventually_eq_or_shift a x hx with he | he
  · exact (contMDiffAt_id.congr_of_eventuallyEq he).contMDiffWithinAt
  · exact ((FrameDatumManifold.contMDiff_frameShift n x).congr_of_eventuallyEq he).contMDiffWithinAt

/-- The natural frame quotient carries the actual local covering inverses followed by intrinsic frame charts, with arbitrary representatives used only to choose chart centers. -/
instance instChartedSpaceFrameQuotient : ChartedSpace ChartModel FrameQuotient :=
  frame_mk_isLocalHomeomorph.chartedSpaceOfRightInverse
    (show Function.RightInverse Quotient.out (Quotient.mk frameSetoid) from Quotient.out_eq)

/-- Every chosen quotient chart is literally an actual local inverse of its projection followed by an intrinsic chart at its selected representative. -/
theorem chartAt_eq (q : FrameQuotient) :
    chartAt ChartModel q = (frame_mk_isLocalHomeomorph.localInverseAt q.out).trans
      (chartAt ChartModel q.out) := rfl

/-- The actual quotient atlas is a real manifold to every differentiability order because its concrete sign-overlap maps are smooth. -/
instance instIsManifoldFrameQuotient (n : WithTop ℕ∞) : IsManifold model n FrameQuotient :=
  QuotientManifoldAtlas.isManifold_of_localInverse_comp model frame_mk_isLocalHomeomorph
    (show Function.RightInverse Quotient.out (Quotient.mk frameSetoid) from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n)

/-- The actual intrinsic frame quotient model has real dimension seven. -/
theorem model_finrank : Module.finrank ℝ Model = 7 := FrameDatumManifold.model_finrank

/-- The existing natural frame sign projection is a genuine local diffeomorphism for the intrinsic seven-dimensional covering and quotient atlases. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph model model n (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  QuotientManifoldAtlas.isLocalDiffeomorph_of_localInverse_comp model frame_mk_isLocalHomeomorph
    (show Function.RightInverse Quotient.out (Quotient.mk frameSetoid) from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n)

/-- The actual natural frame sign projection is manifold-smooth to every differentiability order. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) :
    ContMDiff model model n (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  (quotient_mk_isLocalDiffeomorph n).contMDiff

/-- Every genuine topological local inverse of the frame projection is manifold-smooth on its actual open source. -/
theorem contMDiffOn_quotient_localInverse (n : WithTop ℕ∞) (p : FrameDatum) :
    ContMDiffOn model model n (frame_mk_isLocalHomeomorph.localInverseAt p)
      (frame_mk_isLocalHomeomorph.localInverseAt p).source :=
  QuotientManifoldAtlas.contMDiffOn_localInverse_of_localInverse_comp model frame_mk_isLocalHomeomorph
    (show Function.RightInverse Quotient.out (Quotient.mk frameSetoid) from Quotient.out_eq)
    (localInverse_comp_contMDiffOn n) p

/-- The actual frame projection retains its natural covering property and exactly two-point fibers while becoming a genuine local diffeomorphism for the intrinsic atlases. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ∧
      IsLocalDiffeomorph model model n (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ∧
      ∀ q : FrameQuotient, Nat.card
        ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) = 2 :=
  ⟨frame_mk_isCoveringMap, quotient_mk_isLocalDiffeomorph n, frame_fiber_card⟩

end FoliationQM.FrameQuotientManifold
