module
public import FoliationQM.CliffordSpinPolarQuotient
public import FoliationQM.FrameQuotientManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Compatible smooth structure on the genuine Clifford Spin frame quotient

Source scope: the seven-dimensional frame quotient in v13
`prop:takabayasi` and `eq:takabayasi_polar`. The actual full-angle/Spin
sign quotient retains its independently specified equivalence relation
and natural quotient topology. Its proved quotient homeomorphism pulls
back the independently constructed angle/matrix quotient atlas. Actual
chart transitions are therefore the established smooth quotient chart
transitions. No regular-spinor realization defines this frame atlas.

The actual quotient projection is a covering and a local diffeomorphism
for the genuine angle/Spin product atlas and the compatible quotient
atlas. Its fibers are explicitly identified with Fin 2 and every chosen
source representative has a genuine anchored smooth local inverse. These
are sign-quotient statements and do not identify the seven-dimensional
chiral frame quotient with the six-dimensional Lorentz group, choose a
global individual representative, or derive dynamics.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinPolarManifold
open CliffordSpinPolarDatum CliffordSpinPolarQuotient

/-- The genuine frame quotient has the intrinsic one-angle and six-Spin-coordinate real model. -/
abbrev Model := FrameDatumManifold.Model

/-- The actual frame quotient charts use the intrinsic tagged angle/Spin product chart space. -/
abbrev ChartModel := FrameDatumManifold.ChartModel

/-- The frame quotient uses the same independently specified model as its genuine angle/Spin covering space. -/
abbrev model := CliffordSpinPolarDatum.frameModel

/-- The genuine frame sign quotient is Hausdorff in its natural quotient topology through the actual quotient homeomorphism. -/
instance instT2SpaceFrameQuotient : T2Space FrameQuotient :=
  frameQuotientHomeomorph.isEmbedding.t2Space

/-- The genuine frame sign quotient is second countable in its natural quotient topology. -/
instance instSecondCountableTopologyFrameQuotient : SecondCountableTopology FrameQuotient :=
  frameQuotientHomeomorph.secondCountableTopology

/-- The genuine natural frame quotient carries the explicit pullback of the independently constructed matrix-frame quotient atlas. -/
instance instChartedSpaceFrameQuotient : ChartedSpace ChartModel FrameQuotient where
  atlas := {e | ∃ e' ∈ atlas ChartModel SourcePolarProductQuotient.FrameQuotient,
    e = frameQuotientHomeomorph.transOpenPartialHomeomorph e'}
  chartAt q := frameQuotientHomeomorph.transOpenPartialHomeomorph
    (chartAt ChartModel (frameQuotientHomeomorph q))
  mem_chart_source q := mem_chart_source ChartModel (frameQuotientHomeomorph q)
  chart_mem_atlas q := ⟨_, chart_mem_atlas ChartModel (frameQuotientHomeomorph q), rfl⟩

/-- Every preferred actual frame quotient chart is exactly an independent matrix-quotient chart composed with the proved quotient homeomorphism. -/
theorem chartAt_eq (q : FrameQuotient) :
    chartAt ChartModel q = frameQuotientHomeomorph.transOpenPartialHomeomorph
      (chartAt ChartModel (frameQuotientHomeomorph q)) := rfl

/-- Actual Clifford frame quotient transitions equal the independently verified matrix-quotient transitions, giving a real manifold to every order. -/
instance instIsManifoldFrameQuotient (n : WithTop ℕ∞) : IsManifold model n FrameQuotient where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n model).compatible ha hb

/-- The actual chiral frame quotient model has real dimension seven. -/
theorem model_finrank : Module.finrank ℝ Model = 7 :=
  FrameDatumManifold.model_finrank

/-- The genuine quotient identification is smooth for the specified actual Spin and independently constructed matrix quotient atlases. -/
theorem contMDiff_frameQuotientHomeomorph (n : WithTop ℕ∞) :
    ContMDiff model FrameQuotientManifold.model n frameQuotientHomeomorph := by
  intro q
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun q : SourcePolarProductQuotient.FrameQuotient => q))
      (frameQuotientHomeomorph q)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨frameQuotientHomeomorph.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The inverse genuine quotient identification is smooth in the same independently specified quotient atlases. -/
theorem contMDiff_frameQuotientHomeomorph_symm (n : WithTop ℕ∞) :
    ContMDiff FrameQuotientManifold.model model n frameQuotientHomeomorph.symm := by
  intro q
  have hh := (contMDiff_id (I := model) (n := n) :
    ContMDiff model model n (fun q : SourcePolarProductQuotient.FrameQuotient => q)) q
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨frameQuotientHomeomorph.symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [chartAt_eq, Function.comp_def]

/-- The actual Clifford frame quotient and the independently constructed matrix frame quotient are diffeomorphic through their exact quotient identification. -/
def frameQuotientDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model FrameQuotientManifold.model
      FrameQuotient SourcePolarProductQuotient.FrameQuotient n where
  toEquiv := frameQuotientHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_frameQuotientHomeomorph n
  contMDiff_invFun := contMDiff_frameQuotientHomeomorph_symm n

/-- The frame quotient diffeomorphism evaluates to the previously proved actual quotient homeomorphism. -/
theorem frameQuotientDiffeomorph_apply (n : WithTop ℕ∞) (q : FrameQuotient) :
    frameQuotientDiffeomorph n q = frameQuotientHomeomorph q := rfl

/-- The inverse frame quotient diffeomorphism is exactly the inverse actual quotient homeomorphism. -/
theorem frameQuotientDiffeomorph_symm_apply (n : WithTop ℕ∞)
    (q : SourcePolarProductQuotient.FrameQuotient) :
    (frameQuotientDiffeomorph n).symm q = frameQuotientHomeomorph.symm q := rfl

/-- The frame quotient diffeomorphism retains the natural quotient homeomorphism exactly. -/
theorem frameQuotientDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (frameQuotientDiffeomorph n).toHomeomorph = frameQuotientHomeomorph := rfl

/-- The actual frame projection is the inverse quotient identification applied to the independently specified matrix frame projection of its actual Pauli coordinates. -/
theorem quotient_mk_eq_matrix (p : FrameDatum) :
    Quotient.mk frameSetoid p = frameQuotientHomeomorph.symm
      (Quotient.mk SourcePolarProductQuotient.frameSetoid (frameHomeomorph p)) := by
  rw [← frameQuotientHomeomorph_mk, frameQuotientHomeomorph.symm_apply_apply]

/-- The literal actual angle/Spin sign projection is a covering for its natural product and quotient topologies. -/
theorem quotient_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
  have h := (FrameQuotientCovering.frame_mk_isCoveringMap.comp_homeomorph frameHomeomorph).homeomorph_comp
    frameQuotientHomeomorph.symm
  have he : frameQuotientHomeomorph.symm ∘
      (Quotient.mk SourcePolarProductQuotient.frameSetoid) ∘ frameHomeomorph =
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
    funext p
    exact (quotient_mk_eq_matrix p).symm
  rw [he] at h
  exact h

/-- The actual angle/Spin quotient projection is a local homeomorphism in the natural topologies. -/
theorem quotient_mk_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  quotient_mk_isCoveringMap.isLocalHomeomorph

/-- The actual Pauli frame-coordinate homeomorphism identifies the genuine sign fiber with the corresponding independently specified matrix sign fiber. -/
def quotientFiberHomeomorph (q : FrameQuotient) :
    ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) ≃ₜ
      ((Quotient.mk SourcePolarProductQuotient.frameSetoid :
        SourcePolarProductQuotient.FrameDatum → SourcePolarProductQuotient.FrameQuotient)
        ⁻¹' {frameQuotientHomeomorph q}) :=
  frameHomeomorph.subtype (by
    intro p
    change Quotient.mk frameSetoid p = q ↔
      Quotient.mk SourcePolarProductQuotient.frameSetoid (frameHomeomorph p) =
        frameQuotientHomeomorph q
    rw [← frameQuotientHomeomorph_mk]
    exact frameQuotientHomeomorph.injective.eq_iff.symm)

/-- Every actual Clifford frame quotient fiber is explicitly equivalent to the two-element type. -/
def quotientFiberEquiv (q : FrameQuotient) :
    ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) ≃ Fin 2 :=
  (quotientFiberHomeomorph q).toEquiv.trans
    (FrameQuotientCovering.frameFiberEquiv (frameQuotientHomeomorph q))

/-- Every genuine Clifford frame sign class has exactly two actual full-angle/Spin representatives. -/
theorem quotient_fiber_card (q : FrameQuotient) :
    Nat.card ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (quotientFiberEquiv q)

/-- Every actual Clifford frame sign class has an evenly covered neighborhood with the discrete two-point fiber Fin 2. -/
theorem quotient_mk_isEvenlyCovered_two (q : FrameQuotient) :
    IsEvenlyCovered (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) q (Fin 2) := by
  let := (quotient_mk_isCoveringMap q).discreteTopology_fiber
  exact (quotient_mk_isCoveringMap q).of_fiber_homeomorph
    (quotientFiberEquiv q).toHomeomorphOfDiscrete

/-- The actual angle/Spin quotient projection is a local diffeomorphism for its independently specified product atlas and compatible quotient atlas. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph frameModel model n
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
  intro p
  have h := ((frameDiffeomorph n).isLocalDiffeomorph p).comp
    FrameQuotientManifold.model SourcePolarProductQuotient.FrameQuotient
    (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n (frameDiffeomorph n p))
  have h' := h.comp model FrameQuotient
    ((frameQuotientDiffeomorph n).symm.isLocalDiffeomorph
      (Quotient.mk SourcePolarProductQuotient.frameSetoid (frameDiffeomorph n p)))
  have he : (frameQuotientDiffeomorph n).symm ∘
      (Quotient.mk SourcePolarProductQuotient.frameSetoid) ∘ frameDiffeomorph n =
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
    funext p
    exact (quotient_mk_eq_matrix p).symm
  rw [he] at h'
  exact h'

/-- The literal actual frame quotient projection is manifold-smooth to every order. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) :
    ContMDiff frameModel model n (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  (quotient_mk_isLocalDiffeomorph n).contMDiff

/-- The actual frame sign projection simultaneously has its natural covering property, all-order local smooth inverses, and exactly two points in every fiber. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ∧
      IsLocalDiffeomorph frameModel model n
        (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ∧
      ∀ q : FrameQuotient, Nat.card
        ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) = 2 :=
  ⟨quotient_mk_isCoveringMap, quotient_mk_isLocalDiffeomorph n, quotient_fiber_card⟩

/-- A genuine smooth local inverse of the actual frame quotient projection through any chosen full-angle/Spin representative. -/
def localInverse (n : WithTop ℕ∞) (p : FrameDatum) :
    PartialDiffeomorph model frameModel FrameQuotient FrameDatum n :=
  (quotient_mk_isLocalDiffeomorph n p).localInverse

/-- The actual class of the chosen representative belongs to the genuine open local-inverse domain. -/
theorem quotient_mem_localInverse_source (n : WithTop ℕ∞) (p : FrameDatum) :
    Quotient.mk frameSetoid p ∈ (localInverse n p).source :=
  (quotient_mk_isLocalDiffeomorph n p).localInverse_mem_source

/-- The actual smooth quotient inverse returns its prescribed full-angle/Clifford-Spin representative at the anchor. -/
theorem localInverse_quotient (n : WithTop ℕ∞) (p : FrameDatum) :
    localInverse n p (Quotient.mk frameSetoid p) = p :=
  (quotient_mk_isLocalDiffeomorph n p).localInverse_left_inv
    (quotient_mk_isLocalDiffeomorph n p).localInverse_mem_target

/-- Every actual class in the genuine local-inverse domain is exactly the class of the locally recovered representative. -/
theorem quotient_localInverse {n : WithTop ℕ∞} {p : FrameDatum} {q : FrameQuotient}
    (hq : q ∈ (localInverse n p).source) :
    Quotient.mk frameSetoid (localInverse n p q) = q :=
  (quotient_mk_isLocalDiffeomorph n p).localInverse_right_inv hq

/-- Every chosen actual frame quotient inverse is smooth on its genuine open source. -/
theorem contMDiffOn_localInverse (n : WithTop ℕ∞) (p : FrameDatum) :
    ContMDiffOn model frameModel n (localInverse n p) (localInverse n p).source :=
  (quotient_mk_isLocalDiffeomorph n p).contMDiffOn_localInverse

end FoliationQM.CliffordSpinPolarManifold
