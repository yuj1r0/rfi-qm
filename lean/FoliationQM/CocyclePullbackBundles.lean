module
public import FoliationQM.PolarCocycleManifold
public import FoliationQM.CocyclePullback
/-!
# Genuine smooth pullback maps and universal lifts for the actual cocycle bundles

Source: base-change infrastructure for the supplied-cocycle interpretation
of v13 `prop:takabayasi`. The total spaces retain their actual independently
constructed core topologies and smooth atlases. A bundled smooth base map
induces the literal total map sending a base point to its image and retaining
the selected fiber coordinate. Exact preimage-cover, selected-index, and
transition identities give its genuine local-trivialization expression and
prove smoothness without a regularity assumption on the selected index.

For an arbitrary charted source, smooth base and original-total maps satisfying
the actual projection square have an explicitly constructed smooth lift to
the pulled-back total space. Both projection equations and uniqueness among
all competing maps are proved before bundling the smooth universal property.
The construction applies separately to polar and represented-spinor fibers,
and commutes with their actual total realization. It requires no invertibility
or surjectivity of the supplied base map. No identification with an unproved
standard pullback atlas interface or global individual polar lift is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CocyclePullbackBundles
attribute [local instance] SmoothCocycleBundle.totalChartedSpace
section Generic
variable {B B' F ι M : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace F] (Z : FiberBundleCore ι B F) (W : FiberBundleCore ι B' F)
  (f : B' → B)

private def mapTotal (p : W.TotalSpace) : Z.TotalSpace := ⟨f p.proj, p.2⟩

private theorem localTriv_mapTotal
    (hind : ∀ x, W.indexAt x = Z.indexAt (f x))
    (hcoord : ∀ i j x v, W.coordChange i j x v = Z.coordChange i j (f x) v)
    (i : ι) (p : W.TotalSpace) :
    Z.localTriv i (mapTotal Z W f p) = (f p.proj, (W.localTriv i p).2) := by
  simp only [FiberBundleCore.localTriv_apply, mapTotal, hind, hcoord]

private def liftTotal (a : M → B') (b : M → Z.TotalSpace) (x : M) : W.TotalSpace :=
  ⟨a x, (b x).2⟩

private theorem localTriv_liftTotal
    (hind : ∀ x, W.indexAt x = Z.indexAt (f x))
    (hcoord : ∀ i j x v, W.coordChange i j x v = Z.coordChange i j (f x) v)
    (a : M → B') (b : M → Z.TotalSpace) (hp : ∀ x, (b x).proj = f (a x))
    (i : ι) (x : M) :
    W.localTriv i (liftTotal Z W a b x) = (a x, (Z.localTriv i (b x)).2) := by
  simp only [FiberBundleCore.localTriv_apply, liftTotal, hind, hcoord, hp]

private theorem mapTotal_liftTotal (a : M → B') (b : M → Z.TotalSpace)
    (hp : ∀ x, (b x).proj = f (a x)) (x : M) :
    mapTotal Z W f (liftTotal Z W a b x) = b x := by
  change (⟨f (a x), (b x).2⟩ : Z.TotalSpace) = b x
  rw [← hp x]

private theorem liftTotal_unique (a : M → B') (b : M → Z.TotalSpace)
    (r : M → W.TotalSpace) (hproj : ∀x, (r x).proj = a x)
    (hmap : ∀x, mapTotal Z W f (r x) = b x) : r = liftTotal Z W a b := by
  funext x
  apply Bundle.TotalSpace.ext (hproj x)
  have hv := congrArg (fun p : Z.TotalSpace => (p.2 : F)) (hmap x)
  exact heq_of_eq hv
end Generic
section GenericSmooth
variable {E E' EF H H' HF B B' F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B']
  [TopologicalSpace F] [ChartedSpace HF F]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  (K : ModelWithCorners ℝ EF HF)
  (Z : FiberBundleCore ι B F) (W : FiberBundleCore ι B' F)
  {n : WithTop ℕ∞} [IsManifold I n B] [IsManifold J n B'] [IsManifold K n F]
  (f : B' → B)
  (hbase : ∀i x, x ∈ W.baseSet i ↔ f x ∈ Z.baseSet i)
  (hind : ∀x, W.indexAt x = Z.indexAt (f x))
  (hcoord : ∀i j x v, W.coordChange i j x v = Z.coordChange i j (f x) v)
  (hZ : ∀i j, ContMDiffOn (I.prod K) K n
    (fun p : B × F => Z.coordChange i j p.1 p.2)
    ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ))
  (hW : ∀i j, ContMDiffOn (J.prod K) K n
    (fun p : B' × F => W.coordChange i j p.1 p.2)
    ((W.baseSet i ∩ W.baseSet j) ×ˢ univ))

include hbase hind hcoord hZ hW in
private theorem contMDiff_mapTotal (hf : ContMDiff J I n f) :
    ContMDiff (J.prod K) (I.prod K) n (mapTotal Z W f) := by
  intro p
  let i := W.indexAt p.proj
  have hp : p ∈ (W.localTriv i).source := W.mem_baseSet_at p.proj
  have hq : mapTotal Z W f p ∈ (Z.localTriv i).source :=
    (hbase i p.proj).mp hp
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I K Z hZ i hq).mpr
  have ht := SmoothCocycleBundle.contMDiffAt_localTriv J K W hW i p hp
  have hc := (hf.contMDiffAt.comp p ht.fst).prodMk ht.snd
  exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun q => localTriv_mapTotal Z W f hind hcoord i q))

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] (L : ModelWithCorners ℝ EM HM)
  [TopologicalSpace M] [ChartedSpace HM M]

include hbase hind hcoord hZ hW in
private theorem contMDiff_liftTotal (a : M → B') (b : M → Z.TotalSpace)
    (hp : ∀x, (b x).proj = f (a x))
    (ha : ContMDiff L J n a) (hb : ContMDiff L (I.prod K) n b) :
    ContMDiff L (J.prod K) n (liftTotal Z W a b) := by
  intro x
  let i := W.indexAt (a x)
  have hx : liftTotal Z W a b x ∈ (W.localTriv i).source := W.mem_baseSet_at (a x)
  have hy : b x ∈ (Z.localTriv i).source := by
    change (b x).proj ∈ Z.baseSet i
    rw [hp x]
    exact (hbase i (a x)).mp hx
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv J K W hW i hx).mpr
  have ht := SmoothCocycleBundle.contMDiffAt_localTriv I K Z hZ i (b x) hy
  have hc := (ha x).prodMk ((ht.comp x (hb x)).snd)
  exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun y => localTriv_liftTotal Z W f hind hcoord a b hp i y))
end GenericSmooth


open DiracMatrices PolarSignQuotient PolarTransitionCocycle PolarCocycleBundles
open PolarCocycleManifold CocyclePullback
variable {E E' H H' B B' ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B'] {n : WithTop ℕ∞}
  (D : Data I B ι n) (f : C^n⟮J, B'; I, B⟯)

/-- The actual polar pullback bundle map applies the supplied smooth base map and retains the actual selected fiber coordinate. -/
def polarMap (p : PolarTotal (pullback D f)) : PolarTotal D := ⟨f p.proj, p.2⟩

/-- The actual represented-spinor pullback bundle map applies the supplied base map and retains the original regular-spinor fiber coordinate. -/
def spinorMap (p : SpinorTotal (pullback D f)) : SpinorTotal D := ⟨f p.proj, p.2⟩

/-- In every actual polar trivialization, the canonical pullback map acts by the base map and identity on the fiber coordinate. -/
theorem localTriv_polarMap (i : ι) (p : PolarTotal (pullback D f)) :
    (polarCore D).localTriv i (polarMap D f p) =
      (f p.proj, ((polarCore (pullback D f)).localTriv i p).2) :=
  localTriv_mapTotal (polarCore D) (polarCore (pullback D f)) f
    (fun _ => rfl) (fun _ _ _ _ => rfl) i p

/-- In every actual spinor trivialization, the canonical pullback map is the base map paired with the identity fiber map. -/
theorem localTriv_spinorMap (i : ι) (p : SpinorTotal (pullback D f)) :
    (spinorCore D).localTriv i (spinorMap D f p) =
      (f p.proj, ((spinorCore (pullback D f)).localTriv i p).2) :=
  localTriv_mapTotal (spinorCore D) (spinorCore (pullback D f)) f
    (fun _ => rfl) (fun _ _ _ _ => rfl) i p

/-- The polar canonical map covers exactly the supplied base map. -/
theorem polarMap_proj (p : PolarTotal (pullback D f)) :
    (polarMap D f p).proj = f p.proj := rfl

/-- The represented-spinor canonical map covers exactly the supplied base map. -/
theorem spinorMap_proj (p : SpinorTotal (pullback D f)) :
    (spinorMap D f p).proj = f p.proj := rfl

section Lift
variable {M : Type*}

/-- The explicit actual polar pullback lift pairs the prescribed new-base value with the original total-map fiber value. -/
def polarLift (a : M → B') (b : M → PolarTotal D) (x : M) :
    PolarTotal (pullback D f) := ⟨a x, (b x).2⟩

/-- The explicit actual represented-spinor pullback lift uses the same base-and-fiber pairing. -/
def spinorLift (a : M → B') (b : M → SpinorTotal D) (x : M) :
    SpinorTotal (pullback D f) := ⟨a x, (b x).2⟩

/-- The constructed polar lift has exactly the prescribed base map. -/
theorem polarLift_proj (a : M → B') (b : M → PolarTotal D) (x : M) :
    (polarLift D f a b x).proj = a x := rfl

/-- The constructed spinor lift has exactly the prescribed base map. -/
theorem spinorLift_proj (a : M → B') (b : M → SpinorTotal D) (x : M) :
    (spinorLift D f a b x).proj = a x := rfl

/-- The actual base-square hypothesis makes the constructed polar lift map to precisely the original total-space map. -/
theorem polarMap_polarLift (a : M → B') (b : M → PolarTotal D)
    (hp : ∀x, (b x).proj = f (a x)) (x : M) :
    polarMap D f (polarLift D f a b x) = b x :=
  mapTotal_liftTotal (polarCore D) (polarCore (pullback D f)) f a b hp x

/-- The actual base-square hypothesis makes the constructed spinor lift map to precisely the original represented total-space map. -/
theorem spinorMap_spinorLift (a : M → B') (b : M → SpinorTotal D)
    (hp : ∀x, (b x).proj = f (a x)) (x : M) :
    spinorMap D f (spinorLift D f a b x) = b x :=
  mapTotal_liftTotal (spinorCore D) (spinorCore (pullback D f)) f a b hp x

/-- Each actual polar chart of the constructed lift has the prescribed base coordinate and the original total-map local fiber coordinate. -/
theorem localTriv_polarLift (a : M → B') (b : M → PolarTotal D)
    (hp : ∀x, (b x).proj = f (a x)) (i : ι) (x : M) :
    (polarCore (pullback D f)).localTriv i (polarLift D f a b x) =
      (a x, ((polarCore D).localTriv i (b x)).2) :=
  localTriv_liftTotal (polarCore D) (polarCore (pullback D f)) f
    (fun _ => rfl) (fun _ _ _ _ => rfl) a b hp i x

/-- Each actual spinor chart of the constructed lift has the original local fiber coordinate over the prescribed new base map. -/
theorem localTriv_spinorLift (a : M → B') (b : M → SpinorTotal D)
    (hp : ∀x, (b x).proj = f (a x)) (i : ι) (x : M) :
    (spinorCore (pullback D f)).localTriv i (spinorLift D f a b x) =
      (a x, ((spinorCore D).localTriv i (b x)).2) :=
  localTriv_liftTotal (spinorCore D) (spinorCore (pullback D f)) f
    (fun _ => rfl) (fun _ _ _ _ => rfl) a b hp i x

/-- Any actual polar total-space map with both prescribed projection laws is the explicit lift; no regularity of the competing map is assumed. -/
theorem polarLift_unique (a : M → B') (b : M → PolarTotal D)
    (r : M → PolarTotal (pullback D f)) (hproj : ∀x, (r x).proj = a x)
    (hmap : ∀x, polarMap D f (r x) = b x) : r = polarLift D f a b :=
  liftTotal_unique (polarCore D) (polarCore (pullback D f)) f a b r hproj hmap

/-- The represented-spinor lift is unique among all actual maps satisfying the two projection laws. -/
theorem spinorLift_unique (a : M → B') (b : M → SpinorTotal D)
    (r : M → SpinorTotal (pullback D f)) (hproj : ∀x, (r x).proj = a x)
    (hmap : ∀x, spinorMap D f (r x) = b x) : r = spinorLift D f a b :=
  liftTotal_unique (spinorCore D) (spinorCore (pullback D f)) f a b r hproj hmap
end Lift

variable [IsManifold I n B] [IsManifold J n B']

/-- The canonical polar pullback bundle map is genuinely smooth for the independent actual cocycle total-space atlases. -/
theorem contMDiff_polarMap :
    ContMDiff (polarModel J) (polarModel I) n (polarMap D f) :=
  contMDiff_mapTotal I J DensityFrameManifold.model (polarCore D)
    (polarCore (pullback D f)) f (fun _ _ => Iff.rfl)
    (fun _ => rfl) (fun _ _ _ _ => rfl)
    (contMDiffOn_polarChange D) (contMDiffOn_polarChange (pullback D f)) f.contMDiff

/-- The canonical represented-spinor pullback bundle map is genuinely smooth in its actual total-space atlases. -/
theorem contMDiff_spinorMap :
    ContMDiff (spinorModel J) (spinorModel I) n (spinorMap D f) :=
  contMDiff_mapTotal I J 𝓘(ℝ, Spinor) (spinorCore D)
    (spinorCore (pullback D f)) f (fun _ _ => Iff.rfl)
    (fun _ => rfl) (fun _ _ _ _ => rfl)
    (contMDiffOn_spinorChange D) (contMDiffOn_spinorChange (pullback D f)) f.contMDiff

/-- The actual canonical pullback maps commute exactly with independently constructed total-space polar realization. -/
theorem realization_commutes (p : PolarTotal (pullback D f)) :
    totalRealizationDiffeomorph D (polarMap D f p) =
      spinorMap D f (totalRealizationDiffeomorph (pullback D f) p) := rfl

section SmoothLift
variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {L : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

/-- Smooth maps forming the actual polar base square have a genuinely smooth explicit pullback lift, proved using actual local bundle charts. -/
theorem contMDiff_polarLift (a : M → B') (b : M → PolarTotal D)
    (hp : ∀x, (b x).proj = f (a x))
    (ha : ContMDiff L J n a) (hb : ContMDiff L (polarModel I) n b) :
    ContMDiff L (polarModel J) n (polarLift D f a b) :=
  contMDiff_liftTotal I J DensityFrameManifold.model (polarCore D)
    (polarCore (pullback D f)) f (fun _ _ => Iff.rfl)
    (fun _ => rfl) (fun _ _ _ _ => rfl)
    (contMDiffOn_polarChange D) (contMDiffOn_polarChange (pullback D f)) L a b hp ha hb

/-- Smooth maps forming the actual spinor base square have a genuinely smooth explicit represented-spinor pullback lift. -/
theorem contMDiff_spinorLift (a : M → B') (b : M → SpinorTotal D)
    (hp : ∀x, (b x).proj = f (a x))
    (ha : ContMDiff L J n a) (hb : ContMDiff L (spinorModel I) n b) :
    ContMDiff L (spinorModel J) n (spinorLift D f a b) :=
  contMDiff_liftTotal I J 𝓘(ℝ, Spinor) (spinorCore D)
    (spinorCore (pullback D f)) f (fun _ _ => Iff.rfl)
    (fun _ => rfl) (fun _ _ _ _ => rfl)
    (contMDiffOn_spinorChange D) (contMDiffOn_spinorChange (pullback D f)) L a b hp ha hb

/-- The actual polar pullback total space satisfies the smooth universal lifting property, with exact projection laws and a unique bundled smooth lift. -/
theorem existsUnique_polarLift
    (a : C^n⟮L, M; J, B'⟯) (b : C^n⟮L, M; polarModel I, PolarTotal D⟯)
    (hp : ∀x, (b x).proj = f (a x)) :
    ∃! r : C^n⟮L, M; polarModel J, PolarTotal (pullback D f)⟯,
      (∀x, (r x).proj = a x) ∧ (∀x, polarMap D f (r x) = b x) := by
  refine ⟨⟨polarLift D f a b,
    contMDiff_polarLift D f a b hp a.contMDiff b.contMDiff⟩, ?_, ?_⟩
  · exact ⟨fun _ => rfl, polarMap_polarLift D f a b hp⟩
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    exact congrFun (polarLift_unique D f a b r hr.1 hr.2) x

/-- The actual represented-spinor pullback total space satisfies the same genuine smooth universal lifting property. -/
theorem existsUnique_spinorLift
    (a : C^n⟮L, M; J, B'⟯) (b : C^n⟮L, M; spinorModel I, SpinorTotal D⟯)
    (hp : ∀x, (b x).proj = f (a x)) :
    ∃! r : C^n⟮L, M; spinorModel J, SpinorTotal (pullback D f)⟯,
      (∀x, (r x).proj = a x) ∧ (∀x, spinorMap D f (r x) = b x) := by
  refine ⟨⟨spinorLift D f a b,
    contMDiff_spinorLift D f a b hp a.contMDiff b.contMDiff⟩, ?_, ?_⟩
  · exact ⟨fun _ => rfl, spinorMap_spinorLift D f a b hp⟩
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    exact congrFun (spinorLift_unique D f a b r hr.1 hr.2) x
end SmoothLift
end FoliationQM.CocyclePullbackBundles
