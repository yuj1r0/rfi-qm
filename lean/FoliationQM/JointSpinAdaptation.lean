module
public import FoliationQM.GeometricSpinObstruction

/-!
# A common adapted cover for two independently charted Spin lifts

For the global Spin-frame component of v13 `prop:takabayasi`, choose the
same target Lorentz chart for both maps at each base point. The two
source charts and the two physical inverse anchors can be chosen
independently. Intersecting the resulting neighborhoods adapts both
original maps to exactly the same target chart and unit section.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.JointSpinAdaptation
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas GeometricSpinObstruction

variable {E EP H HP B P ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace HP] [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ E H} {KP : ModelWithCorners ℝ EP HP}
  {frameProj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι}
  {n : WithTop ℕ∞}

/-- Each base point selects a containing Lorentz chart shared by all the compared source atlases. -/
def targetChart (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι)
    (x : B) : ι := Classical.choose (L.covers x)

/-- Select a source chart and a physical inverse anchor over the shared Lorentz chart at the base point. -/
def charts (A : SmoothLift I KP L n) (x : B) : A.Index × ι × Spin :=
  let i := Classical.choose (A.atlas.covers x)
  let j := targetChart L x
  (i, j, Classical.choose (lorentzHom_surjective (A.map.localCoefficient i j x)))

variable (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The adapted source neighborhood with the common Lorentz parent and this source's own inverse anchor. -/
def neighborhood (A : SmoothLift I KP L n) (x : B) : TopologicalSpace.Opens B :=
  (SmoothSpinLiftRefinement.refinementOfMap A.map LM).domain (charts A x)

/-- The chosen physical inverse and both containing charts put the indexing point inside its adapted neighborhood. -/
theorem mem_neighborhood (A : SmoothLift I KP L n) (x : B) : x ∈ neighborhood LM A x :=
  GeometricSpinAdaptedCharts.mem_domain A.map n _ _ _ x
    (Classical.choose_spec (A.atlas.covers x)) (Classical.choose_spec (L.covers x))
    (Classical.choose_spec (lorentzHom_surjective (A.map.localCoefficient
      (Classical.choose (A.atlas.covers x)) (targetChart L x) x))).symm

/-- The two map-specific adapted neighborhoods intersect in a covering family with their common Lorentz parent. -/
def common (A T : SmoothLift I KP L n) : Refinement (domains L) B where
  parent := targetChart L
  domain x := neighborhood LM A x ⊓ neighborhood LM T x
  covers x := ⟨x, mem_neighborhood LM A x, mem_neighborhood LM T x⟩
  subset _ _ hx := hx.1.1.2

/-- Each base-indexed common open contains its anchor point. -/
theorem mem_common (A T : SmoothLift I KP L n) (x : B) : x ∈ (common LM A T).domain x :=
  ⟨mem_neighborhood LM A x, mem_neighborhood LM T x⟩

/-- A common chart lies inside the chosen adapted neighborhood for the first map. -/
theorem common_subset_left (A T : SmoothLift I KP L n) (x : B) :
    ((common LM A T).domain x : Set B) ⊆ neighborhood LM A x := fun _ hx => hx.1

/-- The same common chart lies inside the adapted neighborhood for the second map. -/
theorem common_subset_right (A T : SmoothLift I KP L n) (x : B) :
    ((common LM A T).domain x : Set B) ⊆ neighborhood LM T x := fun _ hx => hx.2

/-- Restrict the independently adapted Spin atlas to smaller opens with the same assigned Lorentz parent in each chart. -/
def adaptOn (A : SmoothLift I KP L n) (R : Refinement (domains L) B)
    (hparent : ∀ i, R.parent i = targetChart L i)
    (hsub : ∀ i, (R.domain i : Set B) ⊆ neighborhood LM A i) :
    GeometricSpinStructure.Lift I (restrictedAtlas L R) n := by
  let S := GeometricSpinAdaptedCharts.refinedSpinAtlas A.map n A.smoothAtlas LM A.smooth_map
  let r : Refinement (domains S) B :=
    { parent := charts A, domain := R.domain, covers := R.covers, subset := hsub }
  exact
    { Carrier := A.Carrier
      proj := A.proj
      atlas := restrictedAtlas S r
      smoothAtlas := restrictedSmoothAtlas
        (GeometricSpinAdaptedCharts.refinedSpinSmoothAtlas A.map n A.smoothAtlas LM A.smooth_map) r
      map :=
        { toFun := A.map
          continuous_toFun := A.map.continuous_toFun
          proj := A.map.proj
          equivariant := A.map.equivariant }
      adapted :=
        { domain_eq := fun _ => rfl
          unit := fun i x hx => by
            change A.map (S.localSection (charts A i) x) = L.localSection (R.parent i) x
            rw [hparent i]
            exact GeometricSpinAdaptedCharts.refined_unit A.map n A.smoothAtlas LM A.smooth_map
              (charts A i) x (hsub i hx) } }

/-- The first original smooth lift with its source atlas adapted to the shared target charts. -/
def leftLift (A T : SmoothLift I KP L n) :
    GeometricSpinStructure.Lift I (restrictedAtlas L (common LM A T)) n :=
  adaptOn LM A (common LM A T) (fun _ => rfl) (common_subset_left LM A T)

/-- The second original smooth lift adapted to exactly those same target charts. -/
def rightLift (A T : SmoothLift I KP L n) :
    GeometricSpinStructure.Lift I (restrictedAtlas L (common LM A T)) n :=
  adaptOn LM T (common LM A T) (fun _ => rfl) (common_subset_right LM A T)

/-- The first adapted carrier is the original Spin total space. -/
theorem leftLift_carrier (A T : SmoothLift I KP L n) : (leftLift LM A T).Carrier = A.Carrier := rfl

/-- The second adapted carrier is the original second Spin total space. -/
theorem rightLift_carrier (A T : SmoothLift I KP L n) : (rightLift LM A T).Carrier = T.Carrier := rfl

/-- Joint adaptation retains the entire original first physical map. -/
theorem leftLift_map (A T : SmoothLift I KP L n) (q : A.Carrier) :
    (leftLift LM A T).map q = A.map q := rfl

/-- Joint adaptation retains the entire original second physical map. -/
theorem rightLift_map (A T : SmoothLift I KP L n) (q : T.Carrier) :
    (rightLift LM A T).map q = T.map q := rfl

/-- The first jointly adapted principal right action is the original action. -/
theorem leftLift_right (A T : SmoothLift I KP L n) :
    (leftLift LM A T).atlas.right = A.atlas.right := rfl

/-- The second jointly adapted principal right action is the original action. -/
theorem rightLift_right (A T : SmoothLift I KP L n) :
    (rightLift LM A T).atlas.right = T.atlas.right := rfl

end FoliationQM.JointSpinAdaptation
