module

public import FoliationQM.BesselFirstOrderIdentity
public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Actual first-order L² data imply pinned Bessel H¹ membership

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The actual order-two Bessel identity and the pinned derivative-lowering
theorem show that an actual tempered distribution and its first derivative
in H⁰ belong to H¹. The second derivative is used only in H⁻¹. The Lp
specialization retains a genuine distributional derivative equality and
does not replace it with classical differentiation of arbitrary representatives.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.FirstOrderSobolevConverse
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv

private theorem bessel_one_eq (f : 𝓢'(ℝ, ℂ)) :
    besselPotential ℝ ℂ 1 f = besselPotential ℝ ℂ (-1) f -
      (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) •
        besselPotential ℝ ℂ (-1) (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) := by
  have h := congrArg (besselPotential ℝ ℂ (-1))
    (BesselFirstOrderIdentity.besselPotential_two_eq f)
  simpa only [besselPotential_besselPotential_apply, map_sub, map_smul,
    show (2 : ℝ) + -1 = 1 by norm_num] using h

/-- An actual tempered distribution with H⁰ function and first derivative
belongs to the pinned Bessel H¹ space; no L² second derivative is assumed. -/
theorem memSobolev_one_of_memSobolev_zero {f : 𝓢'(ℝ, ℂ)}
    (hf : MemSobolev 0 2 f) (hdf : MemSobolev 0 2 (∂_{(1 : ℝ)} f)) :
    MemSobolev 1 2 f := by
  have hfneg : MemSobolev (-1) 2 f := MemSobolev.mono (by norm_num) hf
  have hdd : MemSobolev (-1) 2 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) := by
    simpa only [zero_sub] using hdf.lineDerivOp (m := (1 : ℝ))
  have hleft : MemSobolev 0 2 (besselPotential ℝ ℂ (-1) f) := by
    apply memSobolev_besselPotential_iff.mpr
    simpa only [add_zero] using hfneg
  have hright : MemSobolev 0 2
      (besselPotential ℝ ℂ (-1) (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f))) := by
    apply memSobolev_besselPotential_iff.mpr
    simpa only [add_zero] using hdd
  have hB : MemSobolev 0 2 (besselPotential ℝ ℂ 1 f) := by
    rw [bessel_one_eq]
    exact hleft.sub (MemSobolev.smul _ hright)
  simpa only [add_zero] using memSobolev_besselPotential_iff.mp hB

/-- Actual complex L² functions linked by the genuine tempered-distribution
derivative relation give an actual pinned Bessel H¹ source state. -/
theorem memSobolev_one_of_lp_derivative
    (f g : Lp ℂ 2 (volume : Measure ℝ))
    (hd : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)) :=
  memSobolev_one_of_memSobolev_zero
    (memSobolev_zero_iff.mpr ⟨f, rfl⟩) (memSobolev_zero_iff.mpr ⟨g, hd⟩)

end FoliationQM.FirstOrderSobolevConverse
