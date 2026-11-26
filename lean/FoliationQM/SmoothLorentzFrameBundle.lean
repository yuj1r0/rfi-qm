module
public import FoliationQM.GeometricLorentzFrameBundle
public import FoliationQM.GeometricPrincipalManifold
public import FoliationQM.PrincipalAtlasReconstruction
public import FoliationQM.PrincipalCocycleEquivalence

/-!
# The direct smooth atlas of actual geometric Lorentz frames

The actual geometric frame total space retains the topology induced by the
base and four original vector-bundle points. Its smooth atlas is constructed
directly from the proved genuine tetrad trivializations and the independent
base and Lorentz group atlases. Manifold compatibility follows from the
smooth transition matrices already derived from the metric and tetrads.

The resulting geometric principal bundle is then identified by a genuine
diffeomorphism with the original tetrad-derived Lorentz cocycle core. This
uses equality only on true overlaps; arbitrary off-domain transition fillers
and independent pointwise chart choices are never required to agree. Exact
local coordinates and actual reconstructed vector formulas are retained.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle Function
open scoped Manifold Topology Matrix.Norms.Operator
namespace FoliationQM.SmoothLorentzFrameBundle
open GeometricLorentzFrameBundle LorentzMatrixGroup

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzTetrad.Data (F := F) I V ι n)

/-- The actual geometric frame total uses the direct tetrad-trivialization atlas, with its independent vector-point topology unchanged. -/
instance instChartedSpaceTotal : ChartedSpace (ModelProd H LorentzManifold.ChartModel) (Total D) :=
  GeometricPrincipalManifold.chartedSpace H LorentzManifold.ChartModel (principalAtlas D)

/-- The transitions extracted from actual geometric frame charts are smooth by the previously proved metric-and-tetrad transition calculation. -/
theorem contMDiffOn_atlasTransition (i j : ι) :
    ContMDiffOn I LorentzManifold.model n ((principalAtlas D).transition i j)
      (((principalAtlas D).triv i).baseSet ∩ ((principalAtlas D).triv j).baseSet) := by
  apply (SmoothLorentzTetrad.contMDiffOn_transition D i j).congr
  intro x hx
  exact principalAtlas_transition D i j x hx.1 hx.2

variable [IsManifold I n B]

/-- Actual metric/tetrad transition regularity makes the direct geometric frame atlas a manifold to the stated base order. -/
instance instIsManifoldTotal : IsManifold (I.prod LorentzManifold.model) n (Total D) :=
  GeometricPrincipalManifold.isManifold I LorentzManifold.model (principalAtlas D)
    (contMDiffOn_atlasTransition D)

/-- Both original geometric tetrad chart directions are smooth for the direct frame atlas, as derived from actual overlap compatibility. -/
theorem smoothAtlas : GeometricPrincipalSmoothAtlas.Data I LorentzManifold.model
    (I.prod LorentzManifold.model) (principalAtlas D) n :=
  GeometricPrincipalManifold.smoothAtlas I LorentzManifold.model (principalAtlas D)
    (contMDiffOn_atlasTransition D)

/-- Each genuine geometric frame trivialization is smooth on its actual source. -/
theorem contMDiffOn_localTriv (i : ι) :
    ContMDiffOn (I.prod LorentzManifold.model) (I.prod LorentzManifold.model) n
      (localTriv D i) (localTriv D i).source := (smoothAtlas D).smooth_triv i

/-- Each actual inverse geometric frame trivialization is smooth on its genuine product domain. -/
theorem contMDiffOn_localTriv_symm (i : ι) :
    ContMDiffOn (I.prod LorentzManifold.model) (I.prod LorentzManifold.model) n
      (localTriv D i).toOpenPartialHomeomorph.symm (localTriv D i).target :=
  (smoothAtlas D).smooth_symm i

/-- The original projection of actual geometric frames is smooth in the directly constructed tetrad atlas. -/
theorem contMDiff_proj :
    ContMDiff (I.prod LorentzManifold.model) I n (Bundle.TotalSpace.proj : Total D → B) :=
  (smoothAtlas D).contMDiff_proj

/-- The actual right Lorentz action on geometric bases is jointly smooth for the independent frame topology and direct atlas. -/
theorem contMDiff_rightAction :
    ContMDiff ((I.prod LorentzManifold.model).prod LorentzManifold.model)
      (I.prod LorentzManifold.model) n
      (fun z : Total D × ProperFutureLorentz => rightAction D z.1 z.2) :=
  (smoothAtlas D).contMDiff_right

/-- The original tetrad-derived Lorentz data, viewed as generic principal group cocycle data without changing any field or transition value. -/
def principalData : PrincipalCocycleBundle.Data I LorentzManifold.model B ProperFutureLorentz ι n where
  domain := (SmoothLorentzTetrad.lorentzData D).domain
  covers := (SmoothLorentzTetrad.lorentzData D).covers
  transition := (SmoothLorentzTetrad.lorentzData D).transition
  smooth_transition := (SmoothLorentzTetrad.lorentzData D).smooth_transition
  identity := (SmoothLorentzTetrad.lorentzData D).identity
  comp := (SmoothLorentzTetrad.lorentzData D).comp

omit [IsManifold I n B] in
/-- The generic principal cocycle uses the literal original geometric tetrad transition. -/
theorem principalData_transition (i j : ι) (x : B) :
    (principalData D).transition i j x = SmoothLorentzTetrad.transition D i j x := rfl

/-- Extracted geometric chart transitions agree with the original tetrad cocycle on precisely the genuine overlaps, which suffices for principal bundle identification. -/
theorem overlapIdentification : PrincipalCocycleMorphism.Data
    (PrincipalAtlasReconstruction.cocycleData (smoothAtlas D)) (principalData D)
    (MonoidHom.id ProperFutureLorentz) :=
  PrincipalCocycleEquivalence.ofOverlap rfl (fun i j x hi hj => principalAtlas_transition D i j x hi hj)

/-- The directly charted actual geometric frame bundle is diffeomorphic to the genuine core of the original tetrad-derived Lorentz cocycle. -/
def frameDiffeomorph :
    Total D ≃ₘ^n⟮I.prod LorentzManifold.model, I.prod LorentzManifold.model⟯
      PrincipalCocycleBundle.Total (principalData D) :=
  (PrincipalAtlasReconstruction.reconstructionDiffeomorph (smoothAtlas D)).trans
    (PrincipalCocycleEquivalence.diffeomorph (overlapIdentification D))

/-- The actual geometric-to-cocycle diffeomorphism preserves the original base point. -/
theorem frameDiffeomorph_proj (p : Total D) : (frameDiffeomorph D p).proj = p.proj := by
  change (PrincipalCocycleEquivalence.diffeomorph (overlapIdentification D)
    (PrincipalAtlasReconstruction.reconstructionDiffeomorph (smoothAtlas D) p)).proj = _
  rw [PrincipalCocycleEquivalence.diffeomorph_proj,
    PrincipalAtlasReconstruction.reconstructionDiffeomorph_proj]

/-- The actual geometric-to-cocycle diffeomorphism intertwines the original basis action and genuine principal-core right multiplication. -/
theorem frameDiffeomorph_rightAction (p : Total D) (L : ProperFutureLorentz) :
    frameDiffeomorph D (rightAction D p L) =
      PrincipalCocycleBundle.rightAct (principalData D) (frameDiffeomorph D p) L := by
  change PrincipalCocycleEquivalence.diffeomorph (overlapIdentification D)
    (PrincipalAtlasReconstruction.reconstructionDiffeomorph (smoothAtlas D) ((principalAtlas D).right p L)) = _
  rw [PrincipalAtlasReconstruction.reconstructionDiffeomorph_right,
    PrincipalCocycleEquivalence.diffeomorph_right]
  rfl

/-- Every genuine local coordinate of the actual geometric frame is preserved by the cocycle diffeomorphism. -/
theorem frameDiffeomorph_localTriv (i : ι) (p : Total D) (hp : p.proj ∈ D.domain i) :
    (PrincipalCocycleBundle.core (principalData D)).localTriv i (frameDiffeomorph D p) = localTriv D i p := by
  change (PrincipalCocycleBundle.core (principalData D)).localTriv i
    (PrincipalCocycleEquivalence.diffeomorph (overlapIdentification D)
      (PrincipalAtlasReconstruction.reconstructionDiffeomorph (smoothAtlas D) p)) = _
  rw [PrincipalCocycleEquivalence.diffeomorph_localTriv _ i _ hp,
    PrincipalAtlasReconstruction.reconstructionDiffeomorph_localTriv _ i p hp]
  rfl

/-- The inverse diffeomorphism reconstructs actual geometric frames over the unchanged base point. -/
theorem frameDiffeomorph_symm_proj (q : PrincipalCocycleBundle.Total (principalData D)) :
    ((frameDiffeomorph D).symm q).proj = q.proj := by
  have h := frameDiffeomorph_proj D ((frameDiffeomorph D).symm q)
  rw [(frameDiffeomorph D).apply_symm_apply] at h
  exact h.symm

/-- Reconstructing a geometric frame reads exactly the original cocycle coordinate in every containing tetrad chart. -/
theorem frameDiffeomorph_symm_localTriv (i : ι)
    (q : PrincipalCocycleBundle.Total (principalData D)) (hq : q.proj ∈ D.domain i) :
    localTriv D i ((frameDiffeomorph D).symm q) =
      (PrincipalCocycleBundle.core (principalData D)).localTriv i q := by
  have h := frameDiffeomorph_localTriv D i ((frameDiffeomorph D).symm q)
    (by rw [frameDiffeomorph_symm_proj]; exact hq)
  rw [(frameDiffeomorph D).apply_symm_apply] at h
  exact h.symm

/-- The inverse cocycle identification is the actual geometric inverse tetrad chart on every true chart domain. -/
theorem frameDiffeomorph_symm_eq (i : ι)
    (q : PrincipalCocycleBundle.Total (principalData D)) (hq : q.proj ∈ D.domain i) :
    (frameDiffeomorph D).symm q = localFromProd D i
      ((PrincipalCocycleBundle.core (principalData D)).localTriv i q) := by
  calc
    _ = localFromProd D i (localToProd D i ((frameDiffeomorph D).symm q)) :=
      (localFromProd_localToProd D i _).symm
    _ = _ := congrArg (localFromProd D i) (frameDiffeomorph_symm_localTriv D i q hq)

end FoliationQM.SmoothLorentzFrameBundle
