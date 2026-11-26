module
public import FoliationQM.SpinLiftIsomorphism
public import FoliationQM.RefinedGeometricPrincipalAtlas
public import FoliationQM.SpinLiftChartGauge

/-!
# A geometric isomorphism from compatible chart signs

For the Spin-frame component of v13 `prop:takabayasi`, two geometric lifts
adapted to the same Lorentz charts can be compared by genuine kernel signs
on the charts. Multiplying a local Spin coordinate by its chart sign and
using the inverse target chart constructs the map on the original total
spaces. The overlap equation gives the same map in each containing chart.
-/

@[expose] public section
noncomputable section
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.AdaptedSpinGaugeMap
open CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup
open SpinSignHOne RefinedGeometricPrincipalAtlas

variable {E H B P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace P] {frameProj : P → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι} {n : WithTop ℕ∞}
  (A T : GeometricSpinStructure.Lift I L n) (a : ZeroCochain I (domains L) n)

/-- The target transition intertwines multiplication by the two chart signs on each pair overlap. -/
def Compatible : Prop :=
  ∀ i j x, x ∈ (L.triv i).baseSet → x ∈ (L.triv j).baseSet →
    T.atlas.transition i j x * (a.value i x).val = (a.value j x).val * A.atlas.transition i j x

/-- On a containing Lorentz chart, adaptation gives the corresponding source-chart membership. -/
theorem mem_source (i : ι) {x : B} (hx : x ∈ (L.triv i).baseSet) :
    x ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]

/-- Read a Spin coordinate in one chart, multiply by its sign, and invert the target chart at the same base point. -/
def localMap (i : ι) (p : A.Carrier) : T.Carrier :=
  (T.atlas.triv i).toOpenPartialHomeomorph.symm
    (A.proj p, (a.value i (A.proj p)).val * (A.atlas.triv i p).2)

/-- On its chart the local comparison preserves the base point. -/
theorem localMap_proj (i : ι) (p : A.Carrier) (hi : A.proj p ∈ (L.triv i).baseSet) :
    T.proj (localMap A T a i p) = A.proj p :=
  (T.atlas.triv i).proj_symm_apply' (mem_source T i hi)

/-- In its defining chart the image has exactly the sign times the original Spin coordinate. -/
theorem localMap_coordinate_self (i : ι) (p : A.Carrier) (hi : A.proj p ∈ (L.triv i).baseSet) :
    (T.atlas.triv i (localMap A T a i p)).2 = (a.value i (A.proj p)).val * (A.atlas.triv i p).2 :=
  congrArg Prod.snd ((T.atlas.triv i).apply_symm_apply' (mem_source T i hi))

/-- The local image satisfies the corresponding sign formula in every overlapping chart. -/
theorem localMap_coordinate (h : Compatible A T a) (i j : ι) (p : A.Carrier)
    (hi : A.proj p ∈ (L.triv i).baseSet) (hj : A.proj p ∈ (L.triv j).baseSet) :
    (T.atlas.triv j (localMap A T a i p)).2 = (a.value j (A.proj p)).val * (A.atlas.triv j p).2 := by
  have hp := localMap_proj A T a i p hi
  rw [T.atlas.change_coordinate i j _ (hp ▸ mem_source T i hi) (hp ▸ mem_source T j hj),
    hp, localMap_coordinate_self A T a i p hi, ← mul_assoc, h i j _ hi hj, mul_assoc,
    ← A.atlas.change_coordinate i j p (mem_source A i hi) (mem_source A j hj)]

/-- Compare the total spaces using any chosen containing chart. -/
def totalMap (p : A.Carrier) : T.Carrier :=
  localMap A T a (Classical.choose (L.covers (A.proj p))) p

/-- The map built from chart signs lies over the original base projection. -/
theorem totalMap_proj (p : A.Carrier) : T.proj (totalMap A T a p) = A.proj p :=
  localMap_proj A T a _ p (Classical.choose_spec (L.covers (A.proj p)))

/-- Every chart containing the base point computes the chosen map by its own signed coordinate. -/
theorem totalMap_coordinate (h : Compatible A T a) (i : ι) (p : A.Carrier)
    (hi : A.proj p ∈ (L.triv i).baseSet) :
    (T.atlas.triv i (totalMap A T a p)).2 = (a.value i (A.proj p)).val * (A.atlas.triv i p).2 :=
  localMap_coordinate A T a h _ i p (Classical.choose_spec (L.covers (A.proj p))) hi

/-- On any actual chart domain the total map equals that chart's elementary local comparison. -/
theorem totalMap_eq_localMap (h : Compatible A T a) (i : ι) (p : A.Carrier)
    (hi : A.proj p ∈ (L.triv i).baseSet) : totalMap A T a p = localMap A T a i p := by
  apply T.atlas.coordinate_injective i
  · rw [totalMap_proj]; exact mem_source T i hi
  · rw [localMap_proj A T a i p hi]; exact mem_source T i hi
  · exact (totalMap_proj A T a p).trans (localMap_proj A T a i p hi).symm
  · rw [totalMap_coordinate A T a h i p hi, localMap_coordinate_self A T a i p hi]

/-- The comparison by chart signs commutes with the actual geometric right Spin actions. -/
theorem totalMap_right (h : Compatible A T a) (p : A.Carrier) (s : Spin) :
    totalMap A T a (A.atlas.right p s) = T.atlas.right (totalMap A T a p) s := by
  obtain ⟨i, hi⟩ := L.covers (A.proj p)
  have hir : A.proj (A.atlas.right p s) ∈ (L.triv i).baseSet := by rwa [A.atlas.proj_right]
  have hit : T.proj (totalMap A T a p) ∈ (T.atlas.triv i).baseSet := by
    rw [totalMap_proj]; exact mem_source T i hi
  apply T.atlas.coordinate_injective i
  · rw [totalMap_proj]; exact mem_source T i hir
  · rwa [T.atlas.proj_right]
  · rw [totalMap_proj, T.atlas.proj_right, totalMap_proj, A.atlas.proj_right]
  · rw [totalMap_coordinate A T a h i _ hir, A.atlas.proj_right, A.atlas.right_local i p s (mem_source A i hi),
      T.atlas.right_local i _ s hit, totalMap_coordinate A T a h i p hi, mul_assoc]

/-- Projection of the comparison through the geometric Lorentz map agrees with the original physical image. -/
theorem totalMap_over (h : Compatible A T a) (p : A.Carrier) :
    T.map (totalMap A T a p) = A.map p := by
  obtain ⟨i, hi⟩ := L.covers (A.proj p)
  have hit : T.proj (totalMap A T a p) ∈ (T.atlas.triv i).baseSet := by
    rw [totalMap_proj]; exact mem_source T i hi
  apply L.coordinate_injective i
  · rwa [T.map.proj, totalMap_proj]
  · rwa [A.map.proj]
  · rw [T.map.proj, totalMap_proj, A.map.proj]
  · rw [T.adapted.coordinate i _ hit, A.adapted.coordinate i p (mem_source A i hi),
      totalMap_coordinate A T a h i p hi, map_mul, (a.value i (A.proj p)).property, one_mul]

/-- Smoothness follows from the local chart formula on an open neighborhood of each source point. -/
theorem contMDiff_totalMap (h : Compatible A T a) :
    ContMDiff (I.prod spinModel) (I.prod spinModel) n (totalMap A T a) := by
  intro p
  obtain ⟨i, hi⟩ := L.covers (A.proj p)
  have hp := A.smoothAtlas.contMDiff_proj.contMDiffAt (x := p)
  have hs := ((a.smooth_value i).contMDiffAt ((L.triv i).open_baseSet.mem_nhds hi)).comp p hp
  have hc := (A.smoothAtlas.contMDiffAt_triv i p (mem_source A i hi)).snd
  have hm := (CliffordSpinManifold.contMDiff_mul n).contMDiffAt.comp p (hs.prodMk hc)
  have ht := (T.smoothAtlas.contMDiffAt_symm i
    (A.proj p, (a.value i (A.proj p)).val * (A.atlas.triv i p).2) (mem_source T i hi)).comp p (hp.prodMk hm)
  apply ht.congr_of_eventuallyEq
  filter_upwards [A.atlas.continuous_proj.continuousAt.preimage_mem_nhds
    ((L.triv i).open_baseSet.mem_nhds hi)] with q hq
  exact totalMap_eq_localMap A T a h i q hq

/-- Inverse chart signs satisfy the comparison equation in the opposite direction. -/
theorem compatible_inverse (h : Compatible A T a) : Compatible T A (zeroInv a) := by
  intro i j x hi hj
  change A.atlas.transition i j x * (a.value i x).val⁻¹ = (a.value j x).val⁻¹ * T.atlas.transition i j x
  calc
    _ = (a.value j x).val⁻¹ * ((a.value j x).val * A.atlas.transition i j x) * (a.value i x).val⁻¹ := by
      rw [inv_mul_cancel_left]
    _ = _ := by rw [← h i j x hi hj]; group

/-- Successive comparisons whose chart coefficients cancel recover each point of the original source. -/
theorem totalMap_cancel (b : ZeroCochain I (domains L) n) (h : Compatible A T a)
    (k : Compatible T A b) (hc : ∀ i x, (b.value i x).val * (a.value i x).val = 1) (p : A.Carrier) :
    totalMap T A b (totalMap A T a p) = p := by
  obtain ⟨i, hi⟩ := L.covers (A.proj p)
  have ht : T.proj (totalMap A T a p) ∈ (L.triv i).baseSet := by rwa [totalMap_proj]
  apply A.atlas.coordinate_injective i
  · rw [totalMap_proj, totalMap_proj]; exact mem_source A i hi
  · exact mem_source A i hi
  · rw [totalMap_proj, totalMap_proj]
  · rw [totalMap_coordinate T A b k i _ ht, totalMap_proj, totalMap_coordinate A T a h i _ hi,
      ← mul_assoc, hc, one_mul]

/-- Compatible smooth chart signs give a diffeomorphism commuting with the Spin actions and the physical maps. -/
def between (h : Compatible A T a) : SpinLiftIsomorphism.Between A T where
  diffeo :=
    { toEquiv :=
        { toFun := totalMap A T a
          invFun := totalMap T A (zeroInv a)
          left_inv := totalMap_cancel A T a (zeroInv a) h (compatible_inverse A T a h)
            (fun _ _ => inv_mul_cancel _)
          right_inv := totalMap_cancel T A (zeroInv a) a (compatible_inverse A T a h) h
            (fun _ _ => mul_inv_cancel _) }
      contMDiff_toFun := contMDiff_totalMap A T a h
      contMDiff_invFun := contMDiff_totalMap T A (zeroInv a) (compatible_inverse A T a h) }
  equivariant := totalMap_right A T a h
  over := totalMap_over A T a h

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}

/-- Gauge-equivalent transitions of adapted Spin lifts give an actual geometric isomorphism over the original Lorentz total space. -/
theorem nonempty_between_of_gauge (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (A T : GeometricSpinStructure.Lift I L n)
    (h : SpinLiftChartGauge.GaugeEq (SpinLiftIsomorphism.transitions LM A) (SpinLiftIsomorphism.transitions LM T)) :
    Nonempty (SpinLiftIsomorphism.Between A T) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨between A T a ?_⟩
  intro i j x hi hj
  have he := ha i j x hi hj
  change T.atlas.transition i j x = (a.value j x).val * (a.value i x).val⁻¹ * A.atlas.transition i j x at he
  rw [he, mul_assoc _ (A.atlas.transition i j x), ← CliffordSpinSignKernel.kernel_mul_comm (a.value i x)]
  group

end FoliationQM.AdaptedSpinGaugeMap
