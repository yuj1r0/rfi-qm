module
public import FoliationQM.SmoothLorentzTetrad
public import FoliationQM.GeometricPrincipalAtlas

/-!
# The actual geometric Lorentz frame bundle

The fiber consists of the actual oriented future Lorentz bases of the supplied
vector-bundle fiber. The total topology is induced by its base point and its
four actual vector-bundle points. It is specified before, and independently of,
any Lorentz cocycle reconstruction or Spin representation.

Supplied smooth tetrads give genuine local trivializations for this topology.
Continuity of their coordinates follows from continuous Hom-bundle evaluation
of the signed metric pairings. Inverse coordinates are actual finite linear
combinations of the original tetrad sections. The principal right action and
its local multiplication law are then derived on this genuine frame total space.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle Matrix Function Topology
open scoped Manifold Bundle Topology Matrix.Norms.Operator
namespace FoliationQM.GeometricLorentzFrameBundle
open GeometricLorentzFrame LorentzMatrixGroup RealLorentzFrame

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzTetrad.Data (F := F) I V ι n)

/-- The actual geometric oriented future Lorentz frames in the original vector-bundle fiber. -/
abbrev Fiber (x : B) :=
  Frame (D.metric x).toLinearMap₁₂ (D.orientation x) (D.future x)

/-- The literal dependent total space of actual geometric frames. -/
abbrev Total := Bundle.TotalSpace ProperFutureLorentz (Fiber D)

/-- The independent geometric embedding records the base point and four actual vector-bundle points. -/
def pointEmbedding (p : Total D) : B × (Fin 4 → TotalSpace F V) :=
  (p.proj, fun a => ⟨p.proj, p.snd.basis a⟩)

/-- The actual frame total topology is induced from the original base and four original vector-bundle points, not from any desired Lorentz or Spin equivalence. -/
instance instTopologicalSpaceTotal : TopologicalSpace (Total D) :=
  TopologicalSpace.induced (pointEmbedding D) inferInstance

/-- The independent vector-point map induces exactly the declared geometric total topology. -/
theorem isInducing_pointEmbedding : IsInducing (pointEmbedding D) := ⟨rfl⟩

/-- The base and four actual vectors uniquely determine an actual geometric frame point. -/
theorem pointEmbedding_injective : Injective (pointEmbedding D) := by
  rintro ⟨x,e⟩ ⟨y,f⟩ h
  have hb : x = y := congrArg Prod.fst h
  subst y
  apply congrArg (fun w : Fiber D x => (⟨x,w⟩ : Total D))
  apply frame_ext
  apply DFunLike.ext
  intro a
  have hv := congrArg (fun z => z.2 a) h
  exact Bundle.TotalSpace.mk_injective x hv

/-- The independent actual vector-point map is a genuine topological embedding. -/
theorem isEmbedding_pointEmbedding : IsEmbedding (pointEmbedding D) :=
  ⟨isInducing_pointEmbedding D, pointEmbedding_injective D⟩

/-- The original base projection is continuous in the actual vector-point topology. -/
theorem continuous_proj : Continuous (Bundle.TotalSpace.proj : Total D → B) :=
  (isInducing_pointEmbedding D).continuous.fst

/-- Each actual vector of a geometric frame is continuous as a point of the original vector bundle. -/
theorem continuous_vector (a : Fin 4) :
    Continuous (fun p : Total D => (⟨p.proj, p.snd.basis a⟩ : TotalSpace F V)) :=
  (continuous_apply a).comp (isInducing_pointEmbedding D).continuous.snd

/-- A pointwise geometric reference exists by the supplied local tetrad cover; no continuity of its choice is asserted. -/
def selectedFrame (x : B) : Fiber D x :=
  SmoothLorentzTetrad.frameAt D (Classical.choose (D.covers x)) x (Classical.choose_spec (D.covers x))

/-- A chart reference equals its actual tetrad on the chart and uses an arbitrary pointwise frame only outside that domain. -/
def referenceFrame (i : ι) (x : B) : Fiber D x := by
  classical
  exact if hx : x ∈ D.domain i then SmoothLorentzTetrad.frameAt D i x hx else selectedFrame D x

/-- On a true chart domain the reference is exactly the geometric frame derived from its original tetrad. -/
theorem referenceFrame_eq (i : ι) (x : B) (hx : x ∈ D.domain i) :
    referenceFrame D i x = SmoothLorentzTetrad.frameAt D i x hx := by
  simp [referenceFrame, hx]

/-- The vectors of a chart reference are precisely its original tetrad sections on that chart. -/
theorem referenceFrame_basis (i : ι) (x : B) (hx : x ∈ D.domain i) (a : Fin 4) :
    (referenceFrame D i x).basis a = D.tetrad i a x := by
  rw [referenceFrame_eq D i x hx, SmoothLorentzTetrad.frameAt_basis]

/-- Actual local group coordinates of a geometric frame are its change to the reference tetrad. -/
def localToProd (i : ι) (p : Total D) : B × ProperFutureLorentz :=
  (p.proj, GeometricLorentzFrame.change p.snd (referenceFrame D i p.proj))

/-- Actual inverse local coordinates reconstruct the geometric frame by the proved right Lorentz action on the reference tetrad. -/
def localFromProd (i : ι) (z : B × ProperFutureLorentz) : Total D :=
  ⟨z.1, GeometricLorentzFrame.rightAction (referenceFrame D i z.1) z.2⟩

/-- Reconstructing and then reading local coordinates returns the supplied actual group coordinate. -/
theorem localToProd_localFromProd (i : ι) (z : B × ProperFutureLorentz) :
    localToProd D i (localFromProd D i z) = z := by
  apply Prod.ext
  · rfl
  · exact change_rightAction _ _

/-- Reading and reconstructing local coordinates returns the original actual geometric frame. -/
theorem localFromProd_localToProd (i : ι) (p : Total D) :
    localFromProd D i (localToProd D i p) = p := by
  exact congrArg (fun w : Fiber D p.proj => (⟨p.proj,w⟩ : Total D))
    (rightAction_change p.snd (referenceFrame D i p.proj))

/-- Each local coordinate matrix entry is an actual signed metric pairing with a geometric frame vector. -/
theorem localToProd_matrix_entry (i : ι) (p : Total D) (hp : p.proj ∈ D.domain i)
    (a b : Fin 4) :
    matrix (localToProd D i p).2.val a b = sign a * D.metric p.proj (D.tetrad i a p.proj) (p.snd.basis b) := by
  rw [localToProd, change_matrix_entry, referenceFrame_basis D i p.proj hp]
  rfl

/-- The inverse chart's actual frame vectors are finite real linear combinations of the original tetrad sections. -/
theorem localFromProd_vector (i : ι) (z : B × ProperFutureLorentz) (hz : z.1 ∈ D.domain i)
    (a : Fin 4) :
    (localFromProd D i z).snd.basis a = ∑ b : Fin 4, matrix z.2.val b a • D.tetrad i b z.1 := by
  change (GeometricLorentzFrame.rightAction (referenceFrame D i z.1) z.2).basis a = _
  rw [GeometricLorentzFrame.rightAction_basis, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [referenceFrame_basis D i z.1 hz]

private theorem continuousOn_pairing (i : ι) (a b : Fin 4) :
    ContinuousOn (fun p : Total D => D.metric p.proj (D.tetrad i a p.proj) (p.snd.basis b))
      (Bundle.TotalSpace.proj ⁻¹' (D.domain i : Set B)) := by
  have hm := D.smooth_metric.continuous.comp (continuous_proj D)
  have ht := ((D.local_frame i).contMDiffOn a).continuousOn.comp
    (continuous_proj D).continuousOn (fun _ hp => hp)
  have hp : ContinuousOn (fun p : Total D =>
      (⟨p.proj, D.metric p.proj (D.tetrad i a p.proj) (p.snd.basis b)⟩ :
        TotalSpace ℝ (Bundle.Trivial B ℝ)))
      (Bundle.TotalSpace.proj ⁻¹' (D.domain i : Set B)) :=
    hm.continuousOn.clm_bundle_apply₂ ht (continuous_vector D b).continuousOn
  exact ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp_continuousOn hp).snd

/-- The actual forward tetrad coordinates are continuous on their genuine source for the independent geometric total topology. -/
theorem continuousOn_localToProd (i : ι) :
    ContinuousOn (localToProd D i) (Bundle.TotalSpace.proj ⁻¹' (D.domain i : Set B)) := by
  apply (continuous_proj D).continuousOn.prodMk
  apply LorentzManifold.isEmbedding_value.isInducing.continuousOn_iff.mpr
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  apply (continuousOn_const.mul (continuousOn_pairing D i a b)).congr
  intro p hp
  exact localToProd_matrix_entry D i p hp a b

private theorem continuousAt_combination (i : ι) (a : Fin 4) (z : B × ProperFutureLorentz)
    (hz : z.1 ∈ D.domain i) :
    ContinuousAt (fun y : B × ProperFutureLorentz =>
      (⟨y.1, ∑ b : Fin 4, matrix y.2.val b a • D.tetrad i b y.1⟩ : TotalSpace F V)) z := by
  let t := trivializationAt F V z.1
  have hb : ContinuousAt (Prod.fst : B × ProperFutureLorentz → B) z := continuous_fst.continuousAt
  have hc (b : Fin 4) : Continuous (fun y : B × ProperFutureLorentz => matrix y.2.val b a) :=
    (continuous_apply a).comp ((continuous_apply b).comp
      ((LorentzMatrixGroup.continuous_matrix.comp continuous_subtype_val).comp continuous_snd))
  have hs (b : Fin 4) : ContinuousAt (fun y : B × ProperFutureLorentz =>
      (⟨y.1, D.tetrad i b y.1⟩ : TotalSpace F V)) z :=
    ((D.local_frame i).contMDiffAt (D.domain i).isOpen hz b).continuousAt.comp hb
  have ht (b : Fin 4) : ContinuousAt (fun y : B × ProperFutureLorentz =>
      (t (⟨y.1, D.tetrad i b y.1⟩ : TotalSpace F V)).2) z :=
    ((t.toOpenPartialHomeomorph.continuousAt
      (show (⟨z.1, D.tetrad i b z.1⟩ : TotalSpace F V) ∈ t.source from
        t.mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt F V z.1))).comp
          (f := fun y : B × ProperFutureLorentz => (⟨y.1,D.tetrad i b y.1⟩ : TotalSpace F V)) (hs b)).snd
  have hsum : ContinuousAt (fun y : B × ProperFutureLorentz =>
      ∑ b : Fin 4, matrix y.2.val b a • (t (⟨y.1,D.tetrad i b y.1⟩ : TotalSpace F V)).2) z := by
    exact tendsto_finsetSum Finset.univ (fun b _ => (hc b).continuousAt.smul (ht b))
  apply (FiberBundle.continuousAt_totalSpace F _).mpr
  refine ⟨hb, hsum.congr_of_eventuallyEq ?_⟩
  filter_upwards [hb.preimage_mem_nhds
    (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V z.1))] with y hy
  change (t (⟨y.1, ∑ b : Fin 4, matrix y.2.val b a • D.tetrad i b y.1⟩ : TotalSpace F V)).2 = _
  let c : Fin 4 → ℝ := fun b => matrix y.2.val b a
  let A : V y.1 →ₗ[ℝ] F := t.linearMapAt ℝ y.1
  have hA (v : V y.1) : A v = (t (⟨y.1,v⟩ : TotalSpace F V)).2 :=
    congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hy) v
  change (t (⟨y.1, ∑ b : Fin 4, c b • D.tetrad i b y.1⟩ : TotalSpace F V)).2 =
    ∑ b : Fin 4, c b • (t (⟨y.1,D.tetrad i b y.1⟩ : TotalSpace F V)).2
  rw [← hA, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul, hA]

/-- The actual inverse tetrad coordinates are continuous in the independent vector-point topology on their genuine product domain. -/
theorem continuousOn_localFromProd (i : ι) :
    ContinuousOn (localFromProd D i) ((D.domain i : Set B) ×ˢ (univ : Set ProperFutureLorentz)) := by
  apply (isInducing_pointEmbedding D).continuousOn_iff.mpr
  apply continuous_fst.continuousOn.prodMk
  apply continuousOn_pi.mpr
  intro a
  apply (show ContinuousOn (fun y : B × ProperFutureLorentz =>
      (⟨y.1, ∑ b : Fin 4, matrix y.2.val b a • D.tetrad i b y.1⟩ : TotalSpace F V))
      ((D.domain i : Set B) ×ˢ (univ : Set ProperFutureLorentz)) from
    fun z hz => (continuousAt_combination D i a z hz.1).continuousWithinAt).congr
  intro z hz
  exact congrArg (fun v : V z.1 => (⟨z.1,v⟩ : TotalSpace F V))
    (localFromProd_vector D i z hz.1 a)

/-- The tetrad maps are genuine local trivializations of the original geometric frame projection and its independently induced total topology. -/
def localTriv (i : ι) : Bundle.Trivialization ProperFutureLorentz
    (Bundle.TotalSpace.proj : Total D → B) where
  toFun := localToProd D i
  invFun := localFromProd D i
  source := Bundle.TotalSpace.proj ⁻¹' (D.domain i : Set B)
  target := (D.domain i : Set B) ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hz := hz.1
  left_inv' p _ := localFromProd_localToProd D i p
  right_inv' z _ := localToProd_localFromProd D i z
  open_source := (D.domain i).isOpen.preimage (continuous_proj D)
  open_target := (D.domain i).isOpen.prod isOpen_univ
  continuousOn_toFun := continuousOn_localToProd D i
  continuousOn_invFun := continuousOn_localFromProd D i
  baseSet := D.domain i
  open_baseSet := (D.domain i).isOpen
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The geometric principal right action acts on the actual basis in its original vector-bundle fiber. -/
def rightAction (p : Total D) (L : ProperFutureLorentz) : Total D :=
  ⟨p.proj, GeometricLorentzFrame.rightAction p.snd L⟩

/-- The actual geometric principal right action preserves the original base point. -/
theorem rightAction_proj (p : Total D) (L : ProperFutureLorentz) :
    (rightAction D p L).proj = p.proj := rfl

/-- Every actual tetrad chart reads the geometric right action as literal right Lorentz multiplication. -/
theorem localTriv_rightAction (i : ι) (p : Total D) (L : ProperFutureLorentz) :
    localTriv D i (rightAction D p L) = (p.proj, (localTriv D i p).2 * L) := by
  apply Prod.ext
  · rfl
  · have hc := change_comp (GeometricLorentzFrame.rightAction p.snd L) p.snd
      (referenceFrame D i p.proj)
    rw [change_rightAction] at hc
    exact hc.symm

/-- Actual tetrad trivializations and the geometric basis action define a genuine principal atlas on the independently topologized frame total space. -/
def principalAtlas : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz)
    (Bundle.TotalSpace.proj : Total D → B) ι where
  triv := localTriv D
  covers := D.covers
  right := rightAction D
  proj_right := rightAction_proj D
  right_local i p L _ := congrArg Prod.snd (localTriv_rightAction D i p L)

/-- The actual geometric frame projection is surjective by the supplied tetrad cover. -/
theorem proj_surjective : Surjective (Bundle.TotalSpace.proj : Total D → B) :=
  (principalAtlas D).proj_surjective

/-- The actual geometric right action is jointly continuous for the independent vector-point topology. -/
theorem continuous_rightAction :
    Continuous (fun z : Total D × ProperFutureLorentz => rightAction D z.1 z.2) :=
  (principalAtlas D).continuous_right

/-- On each chart, its canonical principal unit section is the actual supplied local tetrad frame. -/
theorem localSection_eq (i : ι) (x : B) (hx : x ∈ D.domain i) :
    (principalAtlas D).localSection i x = ⟨x, SmoothLorentzTetrad.frameAt D i x hx⟩ := by
  apply congrArg (fun w : Fiber D x => (⟨x,w⟩ : Total D))
  change GeometricLorentzFrame.rightAction (referenceFrame D i x) 1 = _
  rw [GeometricLorentzFrame.rightAction_one, referenceFrame_eq D i x hx]

/-- The transition extracted from actual geometric principal charts is exactly the original tetrad-derived Lorentz transition on every true overlap. -/
theorem principalAtlas_transition (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (principalAtlas D).transition i j x = SmoothLorentzTetrad.transition D i j x := by
  unfold GeometricPrincipalAtlas.Data.transition
  rw [localSection_eq D i x hi]
  change GeometricLorentzFrame.change (SmoothLorentzTetrad.frameAt D i x hi)
    (referenceFrame D j x) = _
  rw [referenceFrame_eq D j x hj, SmoothLorentzTetrad.transition_eq_change D i j x hi hj]

end FoliationQM.GeometricLorentzFrameBundle
