module
public import FoliationQM.PrincipalAtlasCrossGauge
public import FoliationQM.IntrinsicPathGauge

/-!
# The gauge between actual principal atlases on their intersection cover

For the frame-bundle component of v13 `prop:takabayasi`, the intersections
of two actual atlases cover the original base and refine both covers.
The coordinate of the original unit section supplies a continuous chart
gauge on this joint cover. Its conjugation formula compares the two
restricted transition presentations at every point in a true overlap.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PrincipalAtlasJointGauge
open GeometricPrincipalAtlas PrincipalAtlasCrossGauge CliffordSpinCoverRefinement

variable {B P G ι κ : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G] {proj : P → B}
  (A : GeometricPrincipalAtlas.Data (G := G) proj ι)
  (C : GeometricPrincipalAtlas.Data (G := G) proj κ)

/-- Each joint chart is the intersection of its two original geometric chart domains. -/
def domain (a : ι × κ) : TopologicalSpace.Opens B := (data A).domain a.1 ⊓ (data C).domain a.2

/-- Every point belongs to an actual chart of each atlas and hence to a joint chart. -/
theorem covers (x : B) : ∃ a : ι × κ, x ∈ domain A C a := by
  obtain ⟨i, hi⟩ := A.covers x
  obtain ⟨u, hu⟩ := C.covers x
  exact ⟨(i, u), hi, hu⟩

/-- The joint cover refines the first atlas by taking the first parent index. -/
def left : Refinement (data A).domain (ι × κ) where
  parent := Prod.fst
  domain := domain A C
  covers := covers A C
  subset _ _ hx := hx.1

/-- The same joint cover refines the second atlas by taking the second parent index. -/
def right : Refinement (data C).domain (ι × κ) where
  parent := Prod.snd
  domain := domain A C
  covers := covers A C
  subset _ _ hx := hx.2

/-- The two refinements use the same open domains throughout. -/
theorem domain_eq : (left A C).domain = (right A C).domain := rfl

/-- On each joint chart the gauge is the actual second-atlas coordinate of the
first-atlas unit section. Its continuity follows from the two trivializations. -/
def gauge : IntrinsicPathGauge.Gauge (IntrinsicPathRestriction.data (data A) (left A C)) where
  value a := cross A C a.1 a.2
  continuous_value a := continuousOn_cross A C a.1 a.2

/-- Evaluating the joint gauge returns the cross-chart coordinate in the original total space. -/
theorem gauge_value (a : ι × κ) (x : B) :
    (gauge A C).value a x = (C.triv a.2 (A.localSection a.1 x)).2 := rfl

/-- With a common geometric right action, the actual transitions of the two joint
presentations satisfy the ordered gauge formula on each true pair overlap. -/
theorem transition_conjugate (hr : A.right = C.right) (a b : ι × κ) (x : B)
    (ha : x ∈ domain A C a) (hb : x ∈ domain A C b) :
    (IntrinsicPathRestriction.data (data C) (right A C)).transition a b x =
      (gauge A C).value b x * (IntrinsicPathRestriction.data (data A) (left A C)).transition a b x *
        ((gauge A C).value a x)⁻¹ :=
  PrincipalAtlasCrossGauge.transition_conjugate A C hr a.1 b.1 a.2 b.2 x ha.1 hb.1 ha.2 hb.2

end FoliationQM.PrincipalAtlasJointGauge
