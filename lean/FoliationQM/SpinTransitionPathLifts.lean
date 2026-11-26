module
public import FoliationQM.LorentzTransitionPaths
public import FoliationQM.CliffordSpinPathLifting
public import FoliationQM.CliffordSpinLorentzFields
public import FoliationQM.CliffordSpinTransitionLifts

/-!
# Actual smooth Spin transition lifts constructed from Lorentz paths

For the Spin-frame component of v13 `prop:takabayasi`, the covering
homotopy theorem lifts each supplied joint Lorentz path family from
the genuine Clifford unit. Joint continuity gives a continuous endpoint
field. Its given smooth Lorentz projection then proves its smoothness.
The resulting normalized pair lifts use no supplied Spin endpoint or
connectivity assumption on the pair overlap.
-/

@[expose] public section
noncomputable section
open Set
open scoped Topology Manifold
namespace FoliationQM.SpinTransitionPathLifts
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth CliffordSpinCovering
open LorentzTransitionPaths

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The actual jointly continuous covering lift, anchored at the Clifford unit at time zero. -/
def lifted (P : Family D) (i j : ι) : C(unitInterval × ↥(pairOverlap D i j), Spin) :=
  lorentzHom_isCoveringMap.liftHomotopy (P.homotopy i j) (.const _ 1)
    (fun x => (P.source i j x).trans (map_one lorentzHom).symm)

/-- The jointly lifted family projects to the exact supplied Lorentz family at every time and point. -/
theorem lifted_projects (P : Family D) (i j : ι) (t : unitInterval) (x : pairOverlap D i j) :
    lorentzHom (lifted P i j (t, x)) = P.homotopy i j (t, x) :=
  congrFun (lorentzHom_isCoveringMap.liftHomotopy_lifts _ _ _) (t, x)

/-- Every joint lift starts at the actual Clifford identity. -/
theorem lifted_zero (P : Family D) (i j : ι) (x : pairOverlap D i j) :
    lifted P i j (0, x) = 1 := lorentzHom_isCoveringMap.liftHomotopy_zero _ _ _ x

/-- Every time slice is exactly the unique actual path lift from the Clifford identity. -/
theorem lifted_pathLift (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (t : unitInterval) :
    lifted P i j (t, ⟨x, hi, hj⟩) =
      CliffordSpinPathLifting.pathLift (path P i j x hi hj) 1
        ((path P i j x hi hj).source.trans (map_one lorentzHom).symm) t := rfl

/-- Lifting a diagonal identity homotopy retains the genuine identity at every time. -/
theorem lifted_diagonal (P : Family D) (i : ι) (t : unitInterval) (x : pairOverlap D i i) :
    lifted P i i (t, x) = 1 := by
  have he : (ContinuousMap.const (unitInterval × ↥(pairOverlap D i i)) (1 : Spin)) =
      lifted P i i := by
    apply (lorentzHom_isCoveringMap.eq_liftHomotopy_iff' _ _).mpr
    constructor
    · funext y
      exact (map_one lorentzHom).trans (P.diagonal i y.1 y.2).symm
    · intro y
      rfl
  exact (congrArg (fun f : C(unitInterval × ↥(pairOverlap D i i), Spin) => f (t, x)) he).symm

/-- The continuous endpoint field on the actual open pair intersection. -/
def endpoint (P : Family D) (i j : ι) : C(↥(pairOverlap D i j), Spin) :=
  (lifted P i j).comp ((ContinuousMap.const _ (1 : unitInterval)).prodMk (ContinuousMap.id _))

/-- The constructed endpoint projects to the exact given Lorentz transition. -/
theorem endpoint_projects (P : Family D) (i j : ι) (x : pairOverlap D i j) :
    lorentzHom (endpoint P i j x) = D.transition i j x :=
  (lifted_projects P i j 1 x).trans (P.target i j x)

/-- Continuity of the actual endpoint and smoothness of its given projection prove endpoint smoothness. -/
theorem endpoint_contMDiff (P : Family D) (i j : ι) :
    ContMDiff I spinModel n (endpoint P i j) := by
  apply CliffordSpinLorentzFields.continuous_lift_contMDiff (endpoint P i j).continuous
    ((D.smooth_transition i j).comp_contMDiff contMDiff_subtype_val (fun x => x.property))
  funext x
  exact endpoint_projects P i j x

/-- Extend an actual Spin field on an open subset by the Clifford identity off that subset. -/
def extendOne {U : TopologicalSpace.Opens B} (f : U → Spin) (x : B) : Spin := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 1

/-- The extension retains the field on its original subset. -/
theorem extendOne_eq {U : TopologicalSpace.Opens B} (f : U → Spin) (x : B) (hx : x ∈ U) :
    extendOne f x = f ⟨x, hx⟩ := by
  classical
  exact dite_eq_left hx

/-- A smooth field on an actual open subtype remains smooth there after extension. -/
theorem contMDiffOn_extendOne {U : TopologicalSpace.Opens B} (f : U → Spin)
    (hf : ContMDiff I spinModel n f) :
    ContMDiffOn I spinModel n (extendOne f) (U : Set B) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (I := I) (I' := spinModel)
    (f := extendOne f) (x := ⟨x, hx⟩)).mp
  have he : (fun y : U => extendOne f y) = f := by
    funext y
    exact extendOne_eq f y y.property
  rw [he]
  exact hf ⟨x, hx⟩

/-- Actual smooth normalized Spin pair lifts constructed solely from the supplied Lorentz path families. -/
def pairLifts (P : Family D) : CliffordSpinTransitionLifts.PairLifts D where
  transition i j := extendOne (endpoint P i j)
  smooth_transition i j := contMDiffOn_extendOne _ (endpoint_contMDiff P i j)
  identity i x hi := by
    rw [extendOne_eq (U := pairOverlap D i i) _ x ⟨hi, hi⟩]
    exact lifted_diagonal P i 1 ⟨x, hi, hi⟩
  projection i j x hi hj := by
    rw [extendOne_eq (U := pairOverlap D i j) _ x ⟨hi, hj⟩]
    exact endpoint_projects P i j ⟨x, hi, hj⟩

/-- On a true pair overlap the constructed transition is exactly the actual anchored path-lift endpoint. -/
theorem pairLifts_transition (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (pairLifts P).transition i j x =
      CliffordSpinPathLifting.pathLift (path P i j x hi hj) 1
        ((path P i j x hi hj).source.trans (map_one lorentzHom).symm) 1 := by
  change extendOne (endpoint P i j) x = _
  rw [extendOne_eq (U := pairOverlap D i j) _ x ⟨hi, hj⟩]
  exact lifted_pathLift P i j x hi hj 1

/-- The constructed pair transition projects to the original Lorentz transition on the actual overlap. -/
theorem pairLifts_projection (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    lorentzHom ((pairLifts P).transition i j x) = D.transition i j x :=
  (pairLifts P).projection i j x hi hj

/-- Outside a true pair overlap the total transition extension is the Clifford unit. -/
theorem pairLifts_outside (P : Family D) (i j : ι) (x : B)
    (hx : x ∉ pairOverlap D i j) : (pairLifts P).transition i j x = 1 := by
  classical
  exact dite_eq_right hx

/-- The constructed diagonal transition is the genuine identity throughout the entire base. -/
theorem pairLifts_diagonal (P : Family D) (i : ι) (x : B) :
    (pairLifts P).transition i i x = 1 := by
  by_cases hx : x ∈ D.domain i
  · exact (pairLifts P).identity i x hx
  · exact pairLifts_outside P i i x (fun h => hx h.1)

end FoliationQM.SpinTransitionPathLifts
