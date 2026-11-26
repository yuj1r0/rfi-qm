module

public import FoliationQM.AuxiliaryMetricEnergy
public import FoliationQM.RNCCoordinateConnection
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Circle-valued polar derivative energy

Source: v13 `thm:wallstrom` Part (c), the positive polar-energy identity,
component kinds A and B. A supplied unit complex phase satisfies the actual
clock differential relation without a global real phase. The product rule
and its mixed real pairing give the full inverse-metric energy splitting.
These are pointwise identities; no integrability or extension is claimed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CirclePolarEnergy

open LorentzMatrixGroup RNCCoordinateConnection AuxiliaryMetricEnergy
open scoped BigOperators ComplexConjugate Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The wave reconstructed from a real amplitude and a complex phase. -/
def field (R : E → ℝ) (q : E → ℂ) : E → ℂ := fun y => R y • q y

/-- The actual product derivative follows from the amplitude derivative and the supplied circle-phase differential relation. -/
theorem hasFDerivAt_field {R : E → ℝ} {q : E → ℂ} {x : E}
    {dR α : E →L[ℝ] ℝ} {ω : ℝ}
    (hR : HasFDerivAt R dR x)
    (hq : HasFDerivAt q (α.smulRight (-Complex.I * (ω : ℂ) * q x)) x) :
    HasFDerivAt (field R q)
      (R x • α.smulRight (-Complex.I * (ω : ℂ) * q x) + dR.smulRight (q x)) x := by
  simpa only [field] using! hR.smul hq

/-- A unit phase removes the mixed real amplitude-clock terms in two arbitrary actual derivative directions. -/
theorem mixed_re {R : E → ℝ} {q : E → ℂ} {x : E}
    {dR α : E →L[ℝ] ℝ} {ω : ℝ}
    (hR : HasFDerivAt R dR x)
    (hq : HasFDerivAt q (α.smulRight (-Complex.I * (ω : ℂ) * q x)) x)
    (hunit : ‖q x‖ = 1) (v w : E) :
    (star (fderiv ℝ (field R q) x v) * fderiv ℝ (field R q) x w).re =
      dR v * dR w + ω ^ 2 * (R x) ^ 2 * α v * α w := by
  have hd (u : E) : fderiv ℝ (field R q) x u =
      q x * ((dR u : ℂ) - Complex.I * (ω : ℂ) * (R x : ℂ) * (α u : ℂ)) := by
    rw [(hasFDerivAt_field hR hq).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.real_smul]
    ring
  have hn : Complex.normSq (q x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hunit, one_pow]
  have hu : star (q x) * q x = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn, Complex.ofReal_one]
  rw [hd v, hd w, star_mul]
  rw [show star ((dR v : ℂ) - Complex.I * (ω : ℂ) *
      (R x : ℂ) * (α v : ℂ)) * star (q x) * (q x * ((dR w : ℂ) - Complex.I *
      (ω : ℂ) * (R x : ℂ) * (α w : ℂ))) =
      (star (q x) * q x) * (star ((dR v : ℂ) - Complex.I * (ω : ℂ) *
        (R x : ℂ) * (α v : ℂ)) * ((dR w : ℂ) - Complex.I *
        (ω : ℂ) * (R x : ℂ) * (α w : ℂ))) by ring, hu, one_mul]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The actual wave norm and full inverse-metric derivative energy equal the amplitude and clock energies, without choosing a real phase. -/
theorem energy_split (H : Mat4) {R : Covector → ℝ} {q : Covector → ℂ}
    {x : Covector} {dR α : Covector →L[ℝ] ℝ} {ω : ℝ}
    (hR : HasFDerivAt R dR x)
    (hq : HasFDerivAt q (α.smulRight (-Complex.I * (ω : ℂ) * q x)) x)
    (hunit : ‖q x‖ = 1) :
    ‖field R q x‖ ^ 2 = (R x) ^ 2 ∧
      complexEnergy H (fun i => fderiv ℝ (field R q) x (axis i)) =
        realEnergy H (fun i => dR (axis i)) +
          ω ^ 2 * (R x) ^ 2 * realEnergy H (fun i => α (axis i)) := by
  constructor
  · simp only [field, norm_smul, hunit, mul_one, Real.norm_eq_abs, sq_abs]
  · rw [complexEnergy_eq_sum]
    simp only [mixed_re hR hq hunit, realEnergy, dotProduct, Matrix.mulVec,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end FoliationQM.CirclePolarEnergy
