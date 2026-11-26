module

public import FoliationQM.CurvedChartTestPartition

/-!
# Local vanishing of additive functionals on compact tests

Source: v13 `thm:wallstrom` Part(c), localization step of the distributional
argument, component kind D. An additive functional on compact tests of a
smooth manifold vanishes on a given test once every point of the closed
support of that test has an open neighbourhood on whose tests, supported
inside the original support, the functional vanishes. The proof is the finite
smooth partition-of-unity decomposition of the test.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TestLocalVanishing

open Set Function CurvedChartTestPartition
open scoped Topology Manifold ContDiff

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]

/-- An additive functional on compact tests vanishes on a test as soon as every
point of its closed support has an open neighbourhood on whose tests, with
support inside the original support, the functional vanishes. -/
theorem vanish_of_local {A : Type*} [AddCommMonoid A] (Λ : testSpace I M F n →+ A)
    (Φ : testSpace I M F n)
    (hloc : ∀ x ∈ tsupport Φ.val, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∀ η : testSpace I M F n, tsupport η.val ⊆ tsupport Φ.val → tsupport η.val ⊆ W →
        Λ η = 0) :
    Λ Φ = 0 := by
  classical
  choose! W hWo hxW hW using hloc
  let Ucov : M → Set M := fun x => if x ∈ tsupport Φ.val then W x else (tsupport Φ.val)ᶜ
  have ho : ∀ x, IsOpen (Ucov x) := by
    intro x
    by_cases hx : x ∈ tsupport Φ.val
    · simpa only [Ucov, hx, ite_true] using hWo x hx
    · simpa only [Ucov, hx, ite_false] using (isClosed_tsupport Φ.val).isOpen_compl
  have hcov : univ ⊆ ⋃ x, Ucov x := by
    intro x _
    refine mem_iUnion_of_mem x ?_
    by_cases hx : x ∈ tsupport Φ.val
    · simpa only [Ucov, hx, ite_true] using hxW x hx
    · have hU : Ucov x = (tsupport Φ.val)ᶜ := by simp only [Ucov, hx, ite_false]
      rw [hU]
      exact hx
  obtain ⟨χ, hχ, -⟩ := exists_partition (I := I) (F := F) (n := n) Ucov ho hcov
  rw [variation_sum Λ χ Φ]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hpU : tsupport (piece χ Φ i).val ⊆ Ucov i := piece_tsupport χ Φ hχ i
  have hpK : tsupport (piece χ Φ i).val ⊆ tsupport Φ.val :=
    tsupport_smul_subset_right (fun x => χ i x) Φ.val
  by_cases hi : i ∈ tsupport Φ.val
  · exact hW i hi _ hpK (by simpa only [Ucov, hi, ite_true] using hpU)
  · have hempty : tsupport (piece χ Φ i).val = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have h1 : y ∈ (tsupport Φ.val)ᶜ := by
        simpa only [Ucov, hi, ite_false] using hpU hy
      exact h1 (hpK hy)
    have hz : piece χ Φ i = 0 := Subtype.ext (tsupport_eq_empty_iff.mp hempty)
    rw [hz, map_zero]

end FoliationQM.TestLocalVanishing
