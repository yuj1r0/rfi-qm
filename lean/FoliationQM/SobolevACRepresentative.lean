module

public import FoliationQM.WeakDerivativeRepresentative
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual locally absolutely continuous representatives of the source H¹ class

Sources: v13 thm:uncertainty, eq:cramer_rao and eq:p_var_decomp,
component kinds C and D. The input is the actual pinned Bessel H¹ condition
on an actual complex L² function. The weak-derivative construction gives a
continuous representative, locally absolutely continuous on every interval,
with an actual almost-everywhere derivative in L². A supplied finite position
moment transfers to that representative. H¹ alone is not used to assert it.

Classical derivatives below belong to the constructed representative. An
arbitrary original Lp representative is only equal to it almost everywhere.
No boundary decay, density-score identity or quantum variance is asserted here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevACRepresentative
open MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv

/-- Actual H¹ membership supplies a continuous locally AC representative and
its genuine L² derivative, retaining the tempered-distribution identity. -/
theorem exists_locally_ac_representative (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ))) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume := by
  obtain ⟨g, hg, hw⟩ := SobolevWeakDerivative.exists_of_memSobolev f hf
  obtain ⟨u, huf, hc, hAC, hd⟩ :=
    WeakDerivativeRepresentative.exists_locally_ac_representative hw
  refine ⟨g, u, hg, huf, hc, hAC, hd, MemLp.ae_eq huf.symm (Lp.memLp f), ?_⟩
  apply MemLp.ae_eq _ (Lp.memLp g)
  filter_upwards [hd] with x hx
  exact hx.deriv.symm

/-- The genuine finite position moment of the source state transfers to its
actual AC representative; it is an explicit premise independent of H¹. -/
theorem exists_locally_ac_representative_with_position
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hx : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume ∧
      MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, huL2, hdL2⟩ :=
    exists_locally_ac_representative f hf
  refine ⟨g, u, hg, huf, hc, hAC, hd, huL2, hdL2, ?_⟩
  apply MemLp.ae_eq _ hx
  filter_upwards [huf] with x he
  rw [he]

/-- Continuous representatives of the same actual almost-everywhere class
agree everywhere. Continuity of both representatives is essential. -/
theorem continuous_representative_unique {f u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (huf : u =ᵐ[volume] f) (hvf : v =ᵐ[volume] f) : u = v :=
  Measure.eq_of_ae_eq (huf.trans hvf.symm) hu hv

end FoliationQM.SobolevACRepresentative
