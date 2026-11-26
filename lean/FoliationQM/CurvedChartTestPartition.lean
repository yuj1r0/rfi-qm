module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite chart decompositions of compact manifold variations

A locally finite smooth partition of unity meets a compact test support in
only finitely many indices. Its products with the test are smooth and
compactly supported in the respective open sets. Existence for the actual
coordinate atlas consequently reduces vanishing of any additive first
variation to vanishing on chart-supported tests.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedChartTestPartition

open Set Function
open scoped Topology Manifold ContDiff BigOperators

variable {E F H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} {n : ℕ∞}

/-- The additive group of compact Cⁿ manifold test fields with values in the real normed space F. -/
def testSpace (I : ModelWithCorners ℝ E H) (M F : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ∞) : AddSubgroup (M → F) where
  carrier := {η | ContMDiff I 𝓘(ℝ, F) n η ∧ HasCompactSupport η}
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero⟩
  add_mem' hu hv := ⟨hu.1.add hv.1, hu.2.add hv.2⟩
  neg_mem' hu := ⟨hu.1.neg, hu.2.neg⟩

/-- One localized test is the pointwise product of the partition coefficient and the given test. -/
def piece (χ : SmoothPartitionOfUnity ι I M univ) (η : testSpace I M F n) (i : ι) :
    testSpace I M F n :=
  ⟨fun x => χ i x • η.val x,
    χ.contMDiff_smul (fun _ _ => η.property.1.contMDiffAt),
    η.property.2.smul_left⟩

/-- The localized test is supported inside its own chart in any subordinate open family. -/
theorem piece_tsupport (χ : SmoothPartitionOfUnity ι I M univ) (η : testSpace I M F n)
    {U : ι → Set M} (hχ : χ.IsSubordinate U) (i : ι) : tsupport (piece χ η i).val ⊆ U i :=
  (tsupport_smul_subset_left (fun x => χ i x) η.val).trans (hχ i)

/-- Only partition supports meeting the compact support of the test enter its finite decomposition. -/
def indices (χ : SmoothPartitionOfUnity ι I M univ) (η : testSpace I M F n) : Finset ι :=
  (χ.locallyFinite.finite_nonempty_inter_compact η.property.2).toFinset

/-- The actual compact global test is the finite sum of its chart-localized fields. -/
theorem sum_pieces (χ : SmoothPartitionOfUnity ι I M univ) (η : testSpace I M F n) :
    ∑ i ∈ indices χ η, piece χ η i = η := by
  classical
  apply Subtype.ext
  funext x
  change ((testSpace I M F n).subtype (∑ i ∈ indices χ η, piece χ η i)) x = η.val x
  rw [map_sum, Finset.sum_apply]
  change ∑ i ∈ indices χ η, χ i x • η.val x = η.val x
  rw [← Finset.sum_smul]
  by_cases hx : x ∈ tsupport η.val
  · have hI : χ.finsupport x ⊆ indices χ η := by
      intro i hi
      rw [indices, Set.Finite.mem_toFinset]
      exact ⟨x, (χ.mem_finsupport x).mp hi, hx⟩
    rw [χ.sum_finsupport' x (mem_univ x) hI, one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- An additive first variation on compact tests equals the finite sum of its values on the localized tests. -/
theorem variation_sum {A : Type*} [AddCommMonoid A] (Λ : testSpace I M F n →+ A)
    (χ : SmoothPartitionOfUnity ι I M univ) (η : testSpace I M F n) :
    Λ η = ∑ i ∈ indices χ η, Λ (piece χ η i) := by
  simpa only [map_sum] using (congrArg Λ (sum_pieces χ η)).symm

section Existence

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]

/-- Any open cover of a second-countable Hausdorff finite-dimensional smooth manifold admits a partition
giving a finite chartwise decomposition of each compact test. -/
theorem exists_partition (U : ι → Set M) (ho : ∀ i, IsOpen (U i)) (hU : univ ⊆ ⋃ i, U i) :
    ∃ χ : SmoothPartitionOfUnity ι I M univ, χ.IsSubordinate U ∧ ∀ η : testSpace I M F n,
      (∑ i ∈ indices χ η, piece χ η i) = η ∧ ∀ i, tsupport (piece χ η i).val ⊆ U i := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U ho hU
  exact ⟨χ, hχ, fun η => ⟨sum_pieces χ η, piece_tsupport χ η hχ⟩⟩

/-- For an additive first variation, vanishing on compact tests supported in single coordinate charts
is equivalent to vanishing on all compact tests on the manifold. -/
theorem additive_vanish_iff_chart_tests {A : Type*} [AddCommMonoid A] (Λ : testSpace I M F n →+ A) :
    (∀ η, Λ η = 0) ↔ ∀ (x : M) (η : testSpace I M F n),
      tsupport η.val ⊆ (chartAt H x).source → Λ η = 0 := by
  refine ⟨fun h _ η _ => h η, fun h η => ?_⟩
  obtain ⟨χ, hχ, _⟩ := exists_partition (I := I) (F := F) (n := n)
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source)
    (fun x _ => mem_iUnion_of_mem x (mem_chart_source H x))
  rw [variation_sum Λ χ η]
  exact Finset.sum_eq_zero fun i _ => h i _ (piece_tsupport χ η hχ i)

end Existence
end FoliationQM.CurvedChartTestPartition
