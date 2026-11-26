module
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth quotient charts from actual local inverse transitions

Sources: smooth-atlas infrastructure for the concrete sign quotient in
v13 `prop:takabayasi`. The source atlas and both natural topologies are
supplied independently. A genuine local homeomorphism and an actual
right inverse determine Mathlib's explicit target atlas: each target
chart is a local inverse followed by a preferred source chart.

The additional hypothesis is smoothness of the actual upstairs maps
`localInverseAt a ∘ f` on their exact inverse-image domains. For the
polar sign covering, these maps are proved separately to be locally
identity or the smooth sign shift. No target smoothness or local
diffeomorphism conclusion is included in that hypothesis.

The target chart transitions are actual compositions of source charts
with those upstairs transitions. This proves the target manifold
condition. Independent direct chart calculations prove that the actual
map and its actual local inverses are smooth, and their existing open
partial homeomorphisms therefore give genuine local diffeomorphisms.
No topology is replaced and no global smooth right inverse is assumed.
-/

@[expose] public section
noncomputable section
open scoped Manifold ContDiff
open Function Set Topology
namespace FoliationQM.QuotientManifoldAtlas
variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
  {f : M → N} (hf : IsLocalHomeomorph f) {g : N → M}
  (hg : Function.RightInverse g f) {n : WithTop ℕ∞} [IsManifold I n M]
  (hdeck : ∀ a : M, ContMDiffOn I I n (hf.localInverseAt a ∘ f)
    (f ⁻¹' (hf.localInverseAt a).source))

include hdeck

omit [IsManifold I n M] in
private theorem inverse_transition_smooth (a b : M) :
    ContMDiffOn I I n ((hf.localInverseAt a).symm.trans (hf.localInverseAt b))
      ((hf.localInverseAt a).symm.trans (hf.localInverseAt b)).source := by
  have h := (hdeck b).mono (show
      ((hf.localInverseAt a).symm.trans (hf.localInverseAt b)).source ⊆
        f ⁻¹' (hf.localInverseAt b).source from by
    intro x hx
    have hx' := hx.2
    change (hf.localInverseAt a).symm x ∈ (hf.localInverseAt b).source at hx'
    rwa [show (hf.localInverseAt a).symm x = f x from congrFun (hf.localInverseAt_symm a) x] at hx')
  simpa only [OpenPartialHomeomorph.coe_trans, hf.localInverseAt_symm] using h

/-- If the actual upstairs local-inverse composites are smooth on their precise domains, the explicit local-homeomorphism target atlas is a manifold to the same order as the source atlas. -/
theorem isManifold_of_localInverse_comp :
    let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
    IsManifold I n N := by
  let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ }
  rintro e e' ⟨q, rfl⟩ ⟨r, rfl⟩
  have hh := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := n) (g q))
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := n) (g r))
    (inverse_transition_smooth I hf hdeck (g q) (g r))
    (inverse_transition_smooth I hf hdeck (g r) (g q))
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using hh

omit [IsManifold I n M] in
/-- The actual local homeomorphism is smooth for its explicit target atlas, derived by writing its preferred target chart through the given smooth upstairs transition. -/
theorem contMDiff_of_localInverse_comp :
    let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
    ContMDiff I I n f := by
  let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
  change ContMDiff I I n f
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨hf.continuous.continuousAt, ?_⟩
  have he : hf.localInverseAt (g (f x)) (f x) = g (f x) := by
    calc
      hf.localInverseAt (g (f x)) (f x) = hf.localInverseAt (g (f x)) (f (g (f x))) :=
        congrArg (hf.localInverseAt (g (f x))) (hg (f x)).symm
      _ = g (f x) := hf.localInverseAt_apply_self
  have hs : x ∈ f ⁻¹' (hf.localInverseAt (g (f x))).source := by
    change f x ∈ (hf.localInverseAt (g (f x))).source
    have ht := hf.apply_self_mem_localInverseAt_source (x := g (f x))
    rwa [hg (f x)] at ht
  have hd := (hdeck (g (f x))).contMDiffAt
    (((hf.localInverseAt (g (f x))).open_source.preimage hf.continuous).mem_nhds hs)
  have hc : ContMDiffAt I 𝓘(ℝ, E) n (extChartAt I (g (f x)))
      (hf.localInverseAt (g (f x)) (f x)) := by
    rw [he]
    exact contMDiffAt_extChartAt
  have hcomp := hc.comp x hd
  exact hcomp

omit [IsManifold I n M] in
/-- Every actual local inverse is smooth on its actual open source, by composing the independently smooth upstairs transition with the preferred source chart inverse. -/
theorem contMDiffOn_localInverse_of_localInverse_comp (a : M) :
    let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
    ContMDiffOn I I n (hf.localInverseAt a) (hf.localInverseAt a).source := by
  let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
  change ContMDiffOn I I n (hf.localInverseAt a) (hf.localInverseAt a).source
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hs : g q ∈ f ⁻¹' (hf.localInverseAt a).source := by
    change f (g q) ∈ (hf.localInverseAt a).source
    rw [hg q]
    exact hq
  have hd := (hdeck a).contMDiffAt
    (((hf.localInverseAt a).open_source.preimage hf.continuous).mem_nhds hs)
  have hc := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) (g q)
  have hd' : ContMDiffAt I I n (hf.localInverseAt a ∘ f)
      ((extChartAt I (g q)).symm (extChartAt I (g q) (g q))) := by
    simpa only [extChartAt_to_inv] using hd
  have hcomp := hd'.comp_contMDiffWithinAt (extChartAt I (g q) (g q)) hc
  have hpoint : extChartAt I q q = extChartAt I (g q) (g q) := by
    change I (chartAt H (g q) (hf.localInverseAt (g q) q)) = _
    have he : hf.localInverseAt (g q) q = g q := by
      calc
        hf.localInverseAt (g q) q = hf.localInverseAt (g q) (f (g q)) :=
          congrArg (hf.localInverseAt (g q)) (hg q).symm
        _ = g q := hf.localInverseAt_apply_self
    rw [he]
    rfl
  rw [hpoint]
  convert hcomp using 1
  funext z
  change hf.localInverseAt a ((hf.localInverseAt (g q)).symm
    ((chartAt H (g q)).symm (I.symm z))) =
    hf.localInverseAt a (f ((chartAt H (g q)).symm (I.symm z)))
  rw [hf.localInverseAt_symm]

omit [IsManifold I n M] in
/-- The actual local homeomorphism is a genuine local diffeomorphism for the explicit target atlas; its existing partial inverses supply both smooth directions. -/
theorem isLocalDiffeomorph_of_localInverse_comp :
    let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
    IsLocalDiffeomorph I I n f := by
  let : ChartedSpace H N := hf.chartedSpaceOfRightInverse hg
  change IsLocalDiffeomorph I I n f
  intro a
  let e := hf.localInverseAt a
  let p : PartialDiffeomorph I I M N n := {
    toPartialEquiv := e.symm.toPartialEquiv
    open_source := e.open_target
    open_target := e.open_source
    contMDiffOn_toFun := by
      change ContMDiffOn I I n e.symm e.target
      rw [show (e.symm : M → N) = f from hf.localInverseAt_symm a]
      exact (contMDiff_of_localInverse_comp I hf hg hdeck).contMDiffOn
    contMDiffOn_invFun := contMDiffOn_localInverse_of_localInverse_comp I hf hg hdeck a }
  have hp := p.isLocalDiffeomorphAt I I n
    (hf.self_mem_localInverseAt_target (x := a))
  have heq : (p : M → N) = f := hf.localInverseAt_symm a
  rw [heq] at hp
  exact hp

end FoliationQM.QuotientManifoldAtlas
