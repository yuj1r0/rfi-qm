module
public import FoliationQM.GeometricSpinSmoothCover

/-!
# Local adapted charts for an existing smooth geometric Spin lift

Source scope: the geometric Spin-structure component of v13 `prop:takabayasi`.
An existing smooth equivariant map between independently smooth principal
atlases admits adapted charts after explicit local refinement. The coefficient
of the map in the original charts is lifted through a genuine local inverse
of the physical Clifford homomorphism. Multiplying the original source unit
section by the inverse lift makes its image the original target unit section.
The adjusted coordinates and their inverses are proved smooth on their actual
open domains, with the literal Spin-to-Lorentz coordinate expression.
These neighborhoods cover the base and supply actual refined principal atlases
indexed by the two original chart indices and a local Spin inverse anchor,
retaining both original topologies, total smooth structures, and right actions.
No same-cover individual lift or existence of a Spin structure is presumed.
-/

@[expose] public section
noncomputable section
open Set Function Bundle Topology
open scoped Topology Manifold
namespace FoliationQM.GeometricSpinAdaptedCharts
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {B Q P : Type*} [TopologicalSpace B] [TopologicalSpace Q] [TopologicalSpace P]
  {spinProj : Q → B} {frameProj : P → B} {ι κ : Type*}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ}
  (F : GeometricSpinLift.Map S L) (n : WithTop ℕ∞)

/-- The true adapted domain intersects both original base charts with the inverse image of an actual smooth Clifford inverse domain. -/
def domain (i : ι) (j : κ) (s : Spin) : Set B :=
  ((S.triv i).baseSet ∩ (L.triv j).baseSet) ∩
    F.localCoefficient i j ⁻¹' (localInverse n s).source

/-- The local coefficient lift is composition with the genuine Clifford inverse, with all conclusions restricted to its actual domain. -/
def coefficientLift (i : ι) (j : κ) (s : Spin) (x : B) : Spin :=
  localInverse n s (F.localCoefficient i j x)

/-- The explicit adapted domain is open without assuming global regularity of off-chart coefficient values. -/
theorem isOpen_domain (i : ι) (j : κ) (s : Spin) : IsOpen (domain F n i j s) :=
  (F.continuousOn_localCoefficient i j).isOpen_inter_preimage
    ((S.triv i).open_baseSet.inter (L.triv j).open_baseSet) (localInverse n s).open_source

/-- A prescribed physical lift of the actual coefficient puts the given common-chart point in the explicit adapted neighborhood. -/
theorem mem_domain (i : ι) (j : κ) (s : Spin) (x : B)
    (hi : x ∈ (S.triv i).baseSet) (hj : x ∈ (L.triv j).baseSet)
    (hs : F.localCoefficient i j x = lorentzHom s) : x ∈ domain F n i j s := by
  refine ⟨⟨hi, hj⟩, ?_⟩
  change F.localCoefficient i j x ∈ (localInverse n s).source
  rw [hs]
  exact image_mem_localInverse_source n s

/-- On the actual adapted domain the coefficient lift has exactly the original physical Lorentz image. -/
theorem projection_coefficientLift (i : ι) (j : κ) (s : Spin) (x : B)
    (hx : x ∈ domain F n i j s) :
    lorentzHom (coefficientLift F n i j s x) = F.localCoefficient i j x :=
  image_localInverse hx.2

/-- The actual coefficient lift returns the specified Spin anchor at its physical value. -/
theorem coefficientLift_at (i : ι) (j : κ) (s : Spin) (x : B)
    (hs : F.localCoefficient i j x = lorentzHom s) :
    coefficientLift F n i j s x = s := by
  simp only [coefficientLift, hs, localInverse_image]

/-- The adjusted unit section is the original geometric source unit translated by the inverse of the actual local coefficient lift. -/
def adjustedSection (i : ι) (j : κ) (s : Spin) (x : B) : Q :=
  S.right (S.localSection i x) (coefficientLift F n i j s x)⁻¹

/-- The adjusted coordinate reads the original source group coordinate after left multiplication by the local coefficient lift. -/
def toProd (i : ι) (j : κ) (s : Spin) (q : Q) : B × Spin :=
  (spinProj q, coefficientLift F n i j s (spinProj q) * (S.triv i q).2)

/-- Actual inverse adjusted coordinates use the original inverse chart after inverse coefficient multiplication. -/
def fromProd (i : ι) (j : κ) (s : Spin) (z : B × Spin) : Q :=
  (S.triv i).toOpenPartialHomeomorph.symm (z.1, (coefficientLift F n i j s z.1)⁻¹ * z.2)

/-- The inverse adjusted chart preserves the original base point on its actual domain. -/
theorem fromProd_proj (i : ι) (j : κ) (s : Spin) (z : B × Spin)
    (hz : z.1 ∈ domain F n i j s) :
    spinProj (fromProd F n i j s z) = z.1 :=
  (S.triv i).proj_symm_apply' hz.1.1

/-- Reading the actual adjusted coordinates of an inverse-chart point returns the original product point. -/
theorem toProd_fromProd (i : ι) (j : κ) (s : Spin) (z : B × Spin)
    (hz : z.1 ∈ domain F n i j s) :
    toProd F n i j s (fromProd F n i j s z) = z := by
  unfold toProd
  rw [fromProd_proj F n i j s z hz]
  have ht := (S.triv i).apply_symm_apply'
    (x := (coefficientLift F n i j s z.1)⁻¹ * z.2) hz.1.1
  change (z.1, coefficientLift F n i j s z.1 *
    ((S.triv i) ((S.triv i).toOpenPartialHomeomorph.symm
      (z.1, (coefficientLift F n i j s z.1)⁻¹ * z.2))).2) = z
  rw [ht]
  simp

/-- The actual inverse adjusted chart recovers every original source point on its true domain. -/
theorem fromProd_toProd (i : ι) (j : κ) (s : Spin) (q : Q)
    (hq : spinProj q ∈ domain F n i j s) :
    fromProd F n i j s (toProd F n i j s q) = q := by
  change (S.triv i).toOpenPartialHomeomorph.symm
    (spinProj q, (coefficientLift F n i j s (spinProj q))⁻¹ *
      (coefficientLift F n i j s (spinProj q) * (S.triv i q).2)) = q
  rw [inv_mul_cancel_left]
  exact (S.triv i).symm_apply_mk_proj ((S.triv i).mem_source.mpr hq.1.1)

/-- The actual inverse adjusted chart is the adjusted geometric unit acted on by its displayed Spin coordinate. -/
theorem fromProd_eq_right (i : ι) (j : κ) (s : Spin) (z : B × Spin)
    (hz : z.1 ∈ domain F n i j s) :
    fromProd F n i j s z = S.right (adjustedSection F n i j s z.1) z.2 := by
  rw [adjustedSection, S.right_mul]
  rw [S.right_eq_symm i _ _ (by
    rw [S.proj_localSection i z.1 hz.1.1]
    exact hz.1.1), S.proj_localSection i z.1 hz.1.1,
    S.localSection_coordinate i z.1 hz.1.1, one_mul]
  rfl

/-- The physical map in an actual adjusted chart has precisely the original Clifford homomorphism as its fiber expression. -/
theorem image_fromProd (i : ι) (j : κ) (s : Spin) (z : B × Spin)
    (hz : z.1 ∈ domain F n i j s) :
    L.triv j (F (fromProd F n i j s z)) = (z.1, lorentzHom z.2) := by
  rw [fromProd, F.local_formula i j z.1 _ hz.1.1 hz.1.2,
    map_mul, map_inv, projection_coefficientLift F n i j s z.1 hz]
  simp

/-- The adjusted actual geometric unit has the original base point on its explicit adapted domain. -/
theorem adjustedSection_proj (i : ι) (j : κ) (s : Spin) (x : B)
    (hx : x ∈ domain F n i j s) :
    spinProj (adjustedSection F n i j s x) = x := by
  rw [adjustedSection, S.proj_right, S.proj_localSection i x hx.1.1]

/-- The adjusted actual source unit maps exactly to the independently supplied target chart's unit section. -/
theorem image_adjustedSection (i : ι) (j : κ) (s : Spin) (x : B)
    (hx : x ∈ domain F n i j s) :
    F (adjustedSection F n i j s x) = L.localSection j x := by
  have he := fromProd_eq_right F n i j s (x, 1) hx
  rw [S.right_one] at he
  have hf := image_fromProd F n i j s (x, 1) hx
  rw [he, map_one] at hf
  apply (L.triv j).toOpenPartialHomeomorph.injOn
  · apply (L.triv j).mem_source.mpr
    rw [F.proj, adjustedSection_proj F n i j s x hx]
    exact hx.1.2
  · apply (L.triv j).mem_source.mpr
    rw [L.proj_localSection j x hx.1.2]
    exact hx.1.2
  · change L.triv j (F (adjustedSection F n i j s x)) = L.triv j (L.localSection j x)
    exact hf.trans (L.localSection_coordinate j x hx.1.2).symm

/-- The explicit adapted neighborhoods cover the base after allowing independent source/target chart indices and local Clifford inverse anchors. -/
theorem domains_cover (x : B) : ∃ i j s, x ∈ domain F n i j s := by
  obtain ⟨i, hi⟩ := S.covers x
  obtain ⟨j, hj⟩ := L.covers x
  obtain ⟨s, hs⟩ := lorentzHom_surjective (F.localCoefficient i j x)
  exact ⟨i, j, s, mem_domain F n i j s x hi hj hs.symm⟩

/-- The original target chart restricted to the explicit adapted neighborhood, with its original maps and topology retained. -/
def targetTriv (i : ι) (j : κ) (s : Spin) :
    Bundle.Trivialization ProperFutureLorentz frameProj where
  toFun := L.triv j
  invFun := (L.triv j).toOpenPartialHomeomorph.symm
  source := frameProj ⁻¹' domain F n i j s
  target := (domain F n i j s) ×ˢ univ
  map_source' p hp := by
    refine ⟨?_, mem_univ _⟩
    rw [(L.triv j).coe_fst' hp.1.2]
    exact hp
  map_target' z hz := by
    change frameProj ((L.triv j).toOpenPartialHomeomorph.symm z) ∈ domain F n i j s
    rw [(L.triv j).proj_symm_apply' hz.1.1.2]
    exact hz.1
  left_inv' p hp := (L.triv j).toOpenPartialHomeomorph.left_inv ((L.triv j).mem_source.mpr hp.1.2)
  right_inv' z hz := (L.triv j).apply_symm_apply' hz.1.1.2
  open_source := (isOpen_domain F n i j s).preimage L.continuous_proj
  open_target := (isOpen_domain F n i j s).prod isOpen_univ
  continuousOn_toFun := (L.triv j).toOpenPartialHomeomorph.continuousOn.mono
    (fun _ hp => (L.triv j).mem_source.mpr hp.1.2)
  continuousOn_invFun := (L.triv j).toOpenPartialHomeomorph.continuousOn_symm.mono
    (fun _ hz => (L.triv j).mem_target.mpr hz.1.1.2)
  baseSet := domain F n i j s
  open_baseSet := isOpen_domain F n i j s
  source_eq := rfl
  target_eq := rfl
  proj_toFun p hp := (L.triv j).coe_fst' hp.1.2

/-- The target principal atlas on the explicit refined cover uses the unchanged original target right action and actual restricted charts. -/
def refinedLorentzAtlas :
    GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj (ι × κ × Spin) where
  triv k := targetTriv F n k.1 k.2.1 k.2.2
  covers x := by
    obtain ⟨i, j, s, hx⟩ := domains_cover F n x
    exact ⟨(i, j, s), hx⟩
  right := L.right
  proj_right := L.proj_right
  right_local k p g hp := L.right_local k.2.1 p g hp.1.2

section Smooth
variable {EB EQ EP HB HQ HP : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HQ] [TopologicalSpace HP]
  [ChartedSpace HB B] [ChartedSpace HQ Q] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {KQ : ModelWithCorners ℝ EQ HQ}
  {KP : ModelWithCorners ℝ EP HP}
  (SF : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
  (LF : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  (hF : ContMDiff KQ KP n F)

include SF LF hF

/-- The actual coefficient lift is smooth on the explicit original-overlap and local-inverse domain. -/
theorem contMDiffOn_coefficientLift (i : ι) (j : κ) (s : Spin) :
    ContMDiffOn I spinModel n (coefficientLift F n i j s) (domain F n i j s) :=
  (contMDiffOn_localInverse n s).comp
    ((F.contMDiffOn_localCoefficient SF LF hF i j).mono inter_subset_left) (fun _ hx => hx.2)

/-- Adjusting an original geometric unit by the inverse coefficient lift is smooth on its genuine refined domain. -/
theorem contMDiffOn_adjustedSection (i : ι) (j : κ) (s : Spin) :
    ContMDiffOn I KQ n (adjustedSection F n i j s) (domain F n i j s) :=
  SF.contMDiff_right.comp_contMDiffOn
    (((SF.contMDiffOn_localSection i).mono (fun _ hx => hx.1.1)).prodMk
      (contMDiffOn_coefficientLift F n SF LF hF i j s).inv)

/-- Actual adjusted forward coordinates are smooth on the inverse image of their explicit refined base domain. -/
theorem contMDiffOn_toProd (i : ι) (j : κ) (s : Spin) :
    ContMDiffOn KQ (I.prod spinModel) n (toProd F n i j s)
      (spinProj ⁻¹' domain F n i j s) := by
  have hb := (contMDiffOn_coefficientLift F n SF LF hF i j s).comp
    SF.contMDiff_proj.contMDiffOn (fun _ hx => hx)
  have ht : ContMDiffOn KQ (I.prod spinModel) n (S.triv i)
      (spinProj ⁻¹' domain F n i j s) :=
    (SF.smooth_triv i).mono (fun q hq => (S.triv i).mem_source.mpr hq.1.1)
  intro q hq
  exact SF.contMDiff_proj.contMDiffAt.contMDiffWithinAt.prodMk ((hb q hq).mul (ht q hq).snd)

/-- Actual inverse adjusted coordinates are smooth on the true refined product domain. -/
theorem contMDiffOn_fromProd (i : ι) (j : κ) (s : Spin) :
    ContMDiffOn (I.prod spinModel) KQ n (fromProd F n i j s)
      ((domain F n i j s) ×ˢ (univ : Set Spin)) := by
  have hb : ContMDiffOn (I.prod spinModel) spinModel n
      (fun z : B × Spin => coefficientLift F n i j s z.1)
      ((domain F n i j s) ×ˢ (univ : Set Spin)) :=
    (contMDiffOn_coefficientLift F n SF LF hF i j s).comp
      (contMDiff_fst : ContMDiff (I.prod spinModel) I n (Prod.fst : B × Spin → B)).contMDiffOn
      (fun _ hx => hx.1)
  have hm : ContMDiffOn (I.prod spinModel) (I.prod spinModel) n
      (fun z : B × Spin => (z.1, (coefficientLift F n i j s z.1)⁻¹ * z.2))
      ((domain F n i j s) ×ˢ (univ : Set Spin)) := by
    intro z hz
    exact contMDiff_fst.contMDiffAt.contMDiffWithinAt.prodMk ((hb z hz).inv.mul contMDiff_snd.contMDiffAt.contMDiffWithinAt)
  exact (SF.smooth_symm i).comp hm (fun _ hz => (S.triv i).mem_target.mpr hz.1.1.1)

/-- The adjusted actual source chart and its explicit inverse form a genuine partial diffeomorphism with precisely the refined domain and original smooth structures. -/
def adaptedChart (i : ι) (j : κ) (s : Spin) :
    PartialDiffeomorph KQ (I.prod spinModel) Q (B × Spin) n where
  toFun := toProd F n i j s
  invFun := fromProd F n i j s
  source := spinProj ⁻¹' domain F n i j s
  target := (domain F n i j s) ×ˢ univ
  map_source' _ hq := ⟨hq, mem_univ _⟩
  map_target' z hz := by
    change spinProj (fromProd F n i j s z) ∈ domain F n i j s
    rw [fromProd_proj F n i j s z hz.1]
    exact hz.1
  left_inv' q hq := fromProd_toProd F n i j s q hq
  right_inv' z hz := toProd_fromProd F n i j s z hz.1
  open_source := (isOpen_domain F n i j s).preimage S.continuous_proj
  open_target := (isOpen_domain F n i j s).prod isOpen_univ
  contMDiffOn_toFun := contMDiffOn_toProd F n SF LF hF i j s
  contMDiffOn_invFun := contMDiffOn_fromProd F n SF LF hF i j s

/-- The genuine adjusted partial chart supplies an actual principal trivialization on its exact refined base set. -/
def sourceTriv (i : ι) (j : κ) (s : Spin) : Bundle.Trivialization Spin spinProj where
  toOpenPartialHomeomorph := (adaptedChart F n SF LF hF i j s).toOpenPartialHomeomorph
  baseSet := domain F n i j s
  open_baseSet := isOpen_domain F n i j s
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- Adjusted group coordinates still express the original source principal right action as literal right multiplication. -/
theorem sourceTriv_right (i : ι) (j : κ) (s : Spin) (q : Q) (g : Spin)
    (hq : spinProj q ∈ domain F n i j s) :
    sourceTriv F n SF LF hF i j s (S.right q g) =
      (spinProj q, (sourceTriv F n SF LF hF i j s q).2 * g) := by
  change (spinProj (S.right q g),
    coefficientLift F n i j s (spinProj (S.right q g)) * (S.triv i (S.right q g)).2) =
      (spinProj q, (coefficientLift F n i j s (spinProj q) * (S.triv i q).2) * g)
  rw [S.proj_right, S.right_local i q g hq.1.1, mul_assoc]

/-- Explicit adapted neighborhoods produce a covering refined source principal atlas without changing its original topology or right action. -/
def refinedSpinAtlas : GeometricPrincipalAtlas.Data (G := Spin) spinProj (ι × κ × Spin) where
  triv k := sourceTriv F n SF LF hF k.1 k.2.1 k.2.2
  covers x := by
    obtain ⟨i, j, s, hx⟩ := domains_cover F n x
    exact ⟨(i, j, s), hx⟩
  right := S.right
  proj_right := S.proj_right
  right_local k q g hq := congrArg Prod.snd (sourceTriv_right F n SF LF hF k.1 k.2.1 k.2.2 q g hq)

/-- The refined source atlas has actual forward and inverse smoothness for the unchanged independent source smooth structure. -/
theorem refinedSpinSmoothAtlas : GeometricPrincipalSmoothAtlas.Data I spinModel KQ
    (refinedSpinAtlas F n SF LF hF) n where
  smooth_triv k := contMDiffOn_toProd F n SF LF hF k.1 k.2.1 k.2.2
  smooth_symm k := contMDiffOn_fromProd F n SF LF hF k.1 k.2.1 k.2.2

omit [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ] [ChartedSpace HQ Q] SF hF in
/-- The refined target atlas has actual forward and inverse smoothness for the unchanged independent target smooth structure. -/
theorem refinedLorentzSmoothAtlas : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP
    (refinedLorentzAtlas F n) n where
  smooth_triv k := by
    change ContMDiffOn KP (I.prod lorentzModel) n (L.triv k.2.1)
      (frameProj ⁻¹' domain F n k.1 k.2.1 k.2.2)
    exact (LF.smooth_triv k.2.1).mono (fun _ hp => (L.triv k.2.1).mem_source.mpr hp.1.2)
  smooth_symm k := by
    change ContMDiffOn (I.prod lorentzModel) KP n (L.triv k.2.1).toOpenPartialHomeomorph.symm
      ((domain F n k.1 k.2.1 k.2.2) ×ˢ (univ : Set ProperFutureLorentz))
    exact (LF.smooth_symm k.2.1).mono (fun _ hz => (L.triv k.2.1).mem_target.mpr hz.1.1.2)

/-- The original geometric Spin lift itself is a map between the explicit refined atlases, without changing either total map or principal action. -/
def refinedMap : GeometricSpinLift.Map (refinedSpinAtlas F n SF LF hF) (refinedLorentzAtlas F n) where
  toFun := F
  continuous_toFun := F.continuous_toFun
  proj := F.proj
  equivariant := F.equivariant

/-- Source and target refined charts have exactly the same explicitly constructed base domains. -/
theorem refined_domain_eq (k : ι × κ × Spin) :
    ((refinedSpinAtlas F n SF LF hF).triv k).baseSet =
      ((refinedLorentzAtlas F n).triv k).baseSet := rfl

/-- The refined actual source unit sections map to their corresponding original restricted target unit sections on the true refined cover. -/
theorem refined_unit (k : ι × κ × Spin) (x : B)
    (hx : x ∈ ((refinedLorentzAtlas F n).triv k).baseSet) :
    refinedMap F n SF LF hF ((refinedSpinAtlas F n SF LF hF).localSection k x) =
      (refinedLorentzAtlas F n).localSection k x := by
  change F (fromProd F n k.1 k.2.1 k.2.2 (x, 1)) = L.localSection k.2.1 x
  rw [fromProd_eq_right F n k.1 k.2.1 k.2.2 (x, 1) hx, S.right_one]
  exact image_adjustedSection F n k.1 k.2.1 k.2.2 x hx

end Smooth
end FoliationQM.GeometricSpinAdaptedCharts
