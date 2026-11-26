module
public import FoliationQM.GeometricAtlasObstruction
public import FoliationQM.RefinedGeometricPrincipalAtlas
public import FoliationQM.SpinRefinementComposition

/-!
# Transferring transition paths to a refinement of another frame atlas

For the geometric frame component of v13 `prop:takabayasi`, a single
reference atlas with joint Lorentz transition paths supplies such paths
on a refinement of another atlas of the same projected right-action
space. The cross-chart gauges and their actual local joint paths transform
the reference paths. Their endpoints are the second atlas's original parent
transitions throughout each true overlap of the refinement.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AtlasPathTransfer
open LorentzMatrixGroup PathTransitionData PrincipalAtlasCrossGauge
open CliffordSpinCoverRefinement BasedPathGroup GlobalIntrinsicPathObstruction

variable {B T ι κ : Type*} [TopologicalSpace B] [TopologicalSpace T] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
  (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ)

/-- Shrink the intersection charts to domains on which their genuine cross gauges have joint paths. -/
def jointRefinement : Refinement (PrincipalAtlasJointGauge.domain A C) B :=
  LorentzGaugeRefinement.refinement (PrincipalAtlasJointGauge.gauge A C)

/-- Each final domain retains its designated parent chart from the first atlas. -/
def sourceRefinement : Refinement (data A).domain B :=
  SpinRefinementComposition.compose (PrincipalAtlasJointGauge.left A C) (jointRefinement A C)

/-- Each final domain also retains its designated original chart of the second atlas. -/
def refinement : Refinement (data C).domain B :=
  SpinRefinementComposition.compose (PrincipalAtlasJointGauge.right A C) (jointRefinement A C)

/-- Every base point belongs to its own designated target chart on the final cover. -/
theorem mem_refinement (a : B) : a ∈ (refinement A C).domain a :=
  LorentzGaugeRefinement.mem_domain (PrincipalAtlasJointGauge.gauge A C) a

/-- Both original atlases restrict to the same point-indexed open domains. -/
theorem same_domains : (sourceRefinement A C).domain = (refinement A C).domain := rfl

/-- The geometric target retains the original projection and restricts the second atlas's actual charts. -/
def atlas : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj B :=
  RefinedGeometricPrincipalAtlas.restrictedAtlas C (refinement A C)

/-- The geometric target has the original right action of the second atlas. -/
theorem atlas_right : (atlas A C).right = C.right := rfl

/-- Every target transition is the original second-atlas transition for its two parent indices. -/
theorem atlas_transition (a b : B) : (atlas A C).transition a b =
    C.transition ((refinement A C).parent a) ((refinement A C).parent b) := rfl

/-- The source paths transformed by the joint gauge before identifying their geometric endpoints. -/
def gauged (P : Family (data A)) : Family (IntrinsicPathGauge.gaugedData
    (LorentzGaugeRefinement.gauge (PrincipalAtlasJointGauge.gauge A C))) :=
  IntrinsicPathGauge.gaugedFamily (IntrinsicPathRestriction.family P (sourceRefinement A C))
    (LorentzGaugeRefinement.paths (PrincipalAtlasJointGauge.gauge A C))

/-- Transport the source family's actual joint paths by the cross-chart gauge paths.
The geometric conjugation law supplies exactly the endpoints in the restricted target atlas. -/
def family (hr : A.right = C.right) (P : Family (data A)) : Family (data (atlas A C)) where
  homotopy := (gauged A C P).homotopy
  source := (gauged A C P).source
  diagonal := (gauged A C P).diagonal
  target a b x := ((gauged A C P).target a b x).trans
    (PrincipalAtlasJointGauge.transition_conjugate A C hr
      ((jointRefinement A C).parent a) ((jointRefinement A C).parent b) x
      ((jointRefinement A C).subset a x.property.1) ((jointRefinement A C).subset b x.property.2)).symm

/-- At every time the transferred map is the ordered product of the target chart gauge path,
the original source transition path, and the inverse source chart gauge path. -/
theorem family_value (hr : A.right = C.right) (P : Family (data A)) (a b : B)
    (t : unitInterval) (x : pairOverlap (data (atlas A C)) a b) :
    (family A C hr P).homotopy a b (t, x) =
      (LorentzGaugeRefinement.paths (PrincipalAtlasJointGauge.gauge A C)).homotopy b
          (t, ⟨x, x.property.2⟩) *
        P.homotopy ((sourceRefinement A C).parent a) ((sourceRefinement A C).parent b)
          (t, ⟨x.val, (sourceRefinement A C).subset a x.property.1,
            (sourceRefinement A C).subset b x.property.2⟩) *
        ((LorentzGaugeRefinement.paths (PrincipalAtlasJointGauge.gauge A C)).homotopy a
          (t, ⟨x, x.property.1⟩))⁻¹ := rfl

/-- Each transferred path ends at the parent transition of the original second atlas. -/
theorem family_target (hr : A.right = C.right) (P : Family (data A)) (a b : B)
    (x : pairOverlap (data (atlas A C)) a b) :
    (family A C hr P).homotopy a b (1, x) =
      C.transition ((refinement A C).parent a) ((refinement A C).parent b) x :=
  (family A C hr P).target a b x

variable [LocallyPathConnectedSpace B]

/-- On the final cover the transferred class is the actual restriction of the source class. -/
theorem class_family (hr : A.right = C.right)
    (e : (projection (G := ProperFutureLorentz)).ker →* Multiplicative (ZMod 2))
    (P : Family (data A)) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e (family A C hr P)) =
      ModTwoRestriction.restrictHom (sourceRefinement A C)
        (ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P)) :=
  (IntrinsicPathGauge.class_gauged e (IntrinsicPathRestriction.family P (sourceRefinement A C))
    (LorentzGaugeRefinement.paths (PrincipalAtlasJointGauge.gauge A C))).trans
    (IntrinsicPathRestriction.class_restrict e P (sourceRefinement A C))

/-- The transferred target paths reproduce the reference all-cover obstruction for every intrinsic character. -/
theorem obstruction_family (hr : A.right = C.right)
    (e : (projection (G := ProperFutureLorentz)).ker →* Multiplicative (ZMod 2))
    (P : Family (data A)) : obstruction e (family A C hr P) = obstruction e P :=
  (IntrinsicPathGauge.obstruction_gauged e (IntrinsicPathRestriction.family P (sourceRefinement A C))
    (LorentzGaugeRefinement.paths (PrincipalAtlasJointGauge.gauge A C))).trans
    (restrict e P (sourceRefinement A C))

/-- Any independent normalized family on the constructed target refinement gives the reference class. -/
theorem obstruction_any (hr : A.right = C.right)
    (e : (projection (G := ProperFutureLorentz)).ker →* Multiplicative (ZMod 2))
    (P : Family (data A)) (Q : Family (data (atlas A C))) : obstruction e Q = obstruction e P :=
  (independent e Q (family A C hr P)).trans (obstruction_family A C hr e P)

end FoliationQM.AtlasPathTransfer
