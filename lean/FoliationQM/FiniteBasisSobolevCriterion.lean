module

public import FoliationQM.BesselLaplacianIdentity

/-!
# First-order Sobolev membership from a finite orthonormal basis

Source: v13 `thm:wallstrom` Part (c), analytic prerequisites of kinds C and D.
On a finite-dimensional real Hilbert domain, actual H¹ membership is equivalent
to H⁰ membership of the distribution and its first derivatives in a finite
orthonormal basis. The converse uses the actual order-two Bessel identity;
second derivatives are required only in H⁻¹. The L² corollary retains genuine
distributional derivative equalities. Applying the criterion to a localized
nodal extension remains separate, and the basis may be empty.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.FiniteBasisSobolevCriterion
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv Laplacian

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

/-- Actual H¹ membership is equivalent to H⁰ membership of the field and its
first distributional derivatives in any finite orthonormal basis. -/
theorem memSobolev_one_iff (b : OrthonormalBasis ι ℝ E) (f : 𝓢'(E, F)) :
    MemSobolev 1 2 f ↔ MemSobolev 0 2 f ∧
      ∀ i, MemSobolev 0 2 (∂_{b i} f) := by
  constructor
  · intro hf
    refine ⟨MemSobolev.mono (by norm_num) hf, ?_⟩
    intro i
    simpa only [sub_self] using hf.lineDerivOp (m := b i)
  · rintro ⟨hf, hdf⟩
    have hfneg : MemSobolev (-1) 2 f := MemSobolev.mono (by norm_num) hf
    have hdd (i : ι) : MemSobolev (-1) 2 (∂_{b i} (∂_{b i} f)) := by
      simpa only [zero_sub] using (hdf i).lineDerivOp (m := b i)
    have hsum (s : Finset ι) :
        MemSobolev (-1) 2 (∑ i ∈ s, ∂_{b i} (∂_{b i} f)) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (hdd i).add ih
    have hLap : MemSobolev (-1) 2 (Δ f) := by
      rw [TemperedDistribution.laplacian_eq_sum b f]
      exact hsum Finset.univ
    have hB : MemSobolev (-1) 2 (besselPotential E F 2 f) := by
      rw [BesselLaplacianIdentity.besselPotential_two_eq]
      exact hfneg.sub (MemSobolev.smul _ hLap)
    simpa only [show (2 : ℝ) + -1 = 1 by norm_num] using
      memSobolev_besselPotential_iff.mp hB

/-- Actual L² fields whose basis derivatives equal an L² family as tempered
distributions belong to the pinned H¹ space, including in dimension zero. -/
theorem memSobolev_one_of_lp_derivatives (b : OrthonormalBasis ι ℝ E)
    (f : Lp F 2 (volume : Measure E)) (g : ι → Lp F 2 (volume : Measure E))
    (hd : ∀ i, ∂_{b i} (f : 𝓢'(E, F)) = (g i : 𝓢'(E, F))) :
    MemSobolev 1 2 (f : 𝓢'(E, F)) := by
  apply (memSobolev_one_iff b _).mpr
  exact ⟨memSobolev_zero_iff.mpr ⟨f, rfl⟩,
    fun i => memSobolev_zero_iff.mpr ⟨g i, hd i⟩⟩

end FoliationQM.FiniteBasisSobolevCriterion
