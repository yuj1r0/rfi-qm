module

public import FoliationQM.PolarDifferential
public import FoliationQM.PolarLocalInverse
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp

/-!
# Local polar Hermitian and symplectic compatibility

Sources: v13 `thm:kahler` (i), `eq:master_local_metric`, and supplement
`eq:audit11_master_euclidean`. The density is positive and the phase is a
real local lift. The bilinear metric, alternating nondegenerate form, and
complex structure below are linked to the actual Fréchet differential of
`sqrt ρ * exp (I * Φ)`. They describe the unweighted amplitude-plane metric.
No global phase quotient, nodal completion, manifold isometry, or spacetime
isometry is asserted. In particular the density-normalized cylindrical
metric in the supplement is not used for this compatibility statement.
-/
@[expose] public section

namespace FoliationQM.PolarKahlerGeometry

open PolarDifferential MasterMetricAndCone
open scoped ComplexConjugate

/-- The Fisher--phase metric as a real bilinear form on density-phase tangents. -/
noncomputable def metric (ρ : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  (1 / (4 * ρ)) • LinearMap.BilinForm.linMulLin
    (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) +
  ρ • LinearMap.BilinForm.linMulLin
    (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

/-- The pullback of `Im (conj v * w)`, with its orientation and factor fixed. -/
noncomputable def symplectic : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  (1 / 2 : ℝ) • (LinearMap.BilinForm.linMulLin
    (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ) -
    LinearMap.BilinForm.linMulLin
    (LinearMap.snd ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ))

/-- Multiplication by `I` in density-phase tangent coordinates. -/
noncomputable def complexStructure (ρ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun v := (-2 * ρ * v.2, v.1 / (2 * ρ))
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' c v := by
    change (-2 * ρ * (c * v.2), (c * v.1) / (2 * ρ)) =
      (c * (-2 * ρ * v.2), c * (v.1 / (2 * ρ)))
    ext <;> ring

/-- Evaluation of the bilinear source metric. -/
theorem metric_apply (ρ : ℝ) (v w : ℝ × ℝ) :
    metric ρ v w = v.1 * w.1 / (4 * ρ) + ρ * v.2 * w.2 := by
  simp [metric, LinearMap.BilinForm.linMulLin_apply]
  ring

/-- Evaluation of the alternating source form. -/
theorem symplectic_apply (v w : ℝ × ℝ) :
    symplectic v w = (v.1 * w.2 - v.2 * w.1) / 2 := by
  simp [symplectic, LinearMap.BilinForm.linMulLin_apply]
  ring

/-- The same source two-form bundled as a continuous alternating map, so that
its actual exterior derivative is available. -/
noncomputable def symplecticForm : (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := ((v 0).1 * (v 1).2 - (v 0).2 * (v 1).1) / 2
  map_update_add' v i x y := by
    fin_cases i <;> simp [Function.update] <;> ring
  map_update_smul' v i c x := by
    fin_cases i <;> simp [Function.update] <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp_all; ring
    · simp_all; ring
    · exact (hij rfl).elim
  cont := by fun_prop

/-- The continuous alternating form has exactly the fixed bilinear normalization. -/
theorem symplecticForm_apply (v w : ℝ × ℝ) :
    symplecticForm ![v, w] = symplectic v w := by
  rw [symplectic_apply]
  rfl

/-- The source two-form is closed: its actual exterior derivative vanishes.
Its coefficients are constant on the full coordinate plane. -/
theorem extDeriv_symplecticForm (q : ℝ × ℝ) :
    extDeriv (fun _ : ℝ × ℝ => symplecticForm) q = 0 := by
  simp only [extDeriv, fderiv_const_apply,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]

/-- Evaluation of the real-linear complex structure. -/
theorem complexStructure_apply (ρ : ℝ) (v : ℝ × ℝ) :
    complexStructure ρ v = (-2 * ρ * v.2, v.1 / (2 * ρ)) := rfl

/-- Symmetry of the real metric. -/
theorem metric_symm (ρ : ℝ) (v w : ℝ × ℝ) : metric ρ v w = metric ρ w v := by
  simp only [metric_apply]
  ring

/-- The source two-form is alternating. -/
theorem symplectic_self (v : ℝ × ℝ) : symplectic v v = 0 := by
  rw [symplectic_apply]
  ring

/-- The source two-form is skew-symmetric. -/
theorem symplectic_skew (v w : ℝ × ℝ) : symplectic v w = -symplectic w v := by
  simp only [symplectic_apply]
  ring

/-- Nondegeneracy of the source two-form, by its two coordinate probes. -/
theorem symplectic_nondegenerate (v : ℝ × ℝ)
    (h : ∀ w, symplectic v w = 0) : v = 0 := by
  have ha := h (0, 1)
  have hb := h (1, 0)
  simp only [symplectic_apply] at ha hb
  apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> linarith

/-- Strict positivity on every nonzero tangent when the density is positive. -/
theorem metric_pos {ρ : ℝ} (hρ : 0 < ρ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < metric ρ v v := by
  rw [metric_apply]
  have ha : 0 ≤ v.1 * v.1 / (4 * ρ) := div_nonneg (mul_self_nonneg _) (by positivity)
  have hb : 0 ≤ ρ * v.2 * v.2 := by nlinarith [sq_nonneg v.2]
  by_cases hfst : v.1 = 0
  · have hsnd : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hfst h)
    have hpos : 0 < ρ * v.2 * v.2 := by
      have := mul_pos hρ (sq_pos_of_ne_zero hsnd)
      nlinarith
    linarith
  · have hpos : 0 < v.1 * v.1 / (4 * ρ) :=
      div_pos (by nlinarith [sq_pos_of_ne_zero hfst]) (by positivity)
    linarith

/-- Squaring the local complex structure is minus the identity. -/
theorem complexStructure_sq {ρ : ℝ} (hρ : 0 < ρ) (v : ℝ × ℝ) :
    complexStructure ρ (complexStructure ρ v) = -v := by
  have hr : ρ ≠ 0 := ne_of_gt hρ
  ext <;> simp only [complexStructure_apply, Prod.fst_neg, Prod.snd_neg] <;> field_simp

/-- The sign convention is `g (J v) w = ω v w`. -/
theorem metric_complexStructure_left {ρ : ℝ} (hρ : 0 < ρ) (v w : ℝ × ℝ) :
    metric ρ (complexStructure ρ v) w = symplectic v w := by
  have hr : ρ ≠ 0 := ne_of_gt hρ
  simp only [metric_apply, complexStructure_apply, symplectic_apply]
  field_simp
  ring

/-- The complex structure preserves the positive source metric. -/
theorem metric_complexStructure_both {ρ : ℝ} (hρ : 0 < ρ) (v w : ℝ × ℝ) :
    metric ρ (complexStructure ρ v) (complexStructure ρ w) = metric ρ v w := by
  have hr : ρ ≠ 0 := ne_of_gt hρ
  simp only [metric_apply, complexStructure_apply]
  field_simp
  ring

/-- The complex structure preserves the source two-form. -/
theorem symplectic_complexStructure_both {ρ : ℝ} (hρ : 0 < ρ) (v w : ℝ × ℝ) :
    symplectic (complexStructure ρ v) (complexStructure ρ w) = symplectic v w := by
  have hr : ρ ≠ 0 := ne_of_gt hρ
  simp only [symplectic_apply, complexStructure_apply]
  field_simp
  ring

/-- The full Hermitian product, including its alternating imaginary part. -/
theorem polarTangent_conj_mul {ρ : ℝ} (hρ : 0 < ρ) (Φ : ℝ) (v w : ℝ × ℝ) :
    conj (polarTangent ρ Φ v.1 v.2) * polarTangent ρ Φ w.1 w.2 =
      (metric ρ v w : ℂ) + Complex.I * (symplectic v w : ℂ) := by
  have hs : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ)
  have hs2 : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hp : conj (phase Φ) * phase Φ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have hn : Complex.normSq (phase Φ) = 1 := by
      simp only [phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq Φ]
    rw [hn, Complex.ofReal_one]
  simp only [polarTangent, amplitudeTangent, map_mul]
  rw [show conj (phase Φ) * conj
      ((v.1 / (2 * Real.sqrt ρ) : ℝ) + Complex.I * (Real.sqrt ρ : ℂ) * (v.2 : ℂ)) *
      (phase Φ * ((w.1 / (2 * Real.sqrt ρ) : ℝ) +
        Complex.I * (Real.sqrt ρ : ℂ) * (w.2 : ℂ))) =
      (conj (phase Φ) * phase Φ) * (conj
        ((v.1 / (2 * Real.sqrt ρ) : ℝ) + Complex.I * (Real.sqrt ρ : ℂ) * (v.2 : ℂ)) *
        ((w.1 / (2 * Real.sqrt ρ) : ℝ) +
          Complex.I * (Real.sqrt ρ : ℂ) * (w.2 : ℂ))) by ring, hp, one_mul]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, metric_apply, symplectic_apply]
  · simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul, sub_zero]
    field_simp
    ring_nf
    rw [show Real.sqrt ρ ^ 4 = ρ ^ 2 by nlinarith [sq_nonneg (Real.sqrt ρ ^ 2 - ρ)]]
    simp only [hs2]
    ring
  · simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul, sub_zero]
    field_simp
    ring

/-- The polar tangent sends the local complex structure to multiplication by `I`. -/
theorem polarTangent_complexStructure {ρ : ℝ} (hρ : 0 < ρ) (Φ : ℝ) (v : ℝ × ℝ) :
    polarTangent ρ Φ (complexStructure ρ v).1 (complexStructure ρ v).2 =
      Complex.I * polarTangent ρ Φ v.1 v.2 := by
  have hs : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ)
  have hr : ρ ≠ 0 := ne_of_gt hρ
  have hs2 : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  simp only [polarTangent, amplitudeTangent, complexStructure_apply]
  rw [show Complex.I * (phase Φ *
    ((v.1 / (2 * Real.sqrt ρ) : ℝ) + Complex.I * (Real.sqrt ρ : ℂ) * (v.2 : ℂ))) =
    phase Φ * (Complex.I *
    ((v.1 / (2 * Real.sqrt ρ) : ℝ) + Complex.I * (Real.sqrt ρ : ℂ) * (v.2 : ℂ))) by ring]
  congr 1
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul, sub_zero, zero_sub]
    <;> field_simp <;> ring_nf <;> simp only [hs2] <;> ring

/-- The concrete density-phase coordinate map, with real local phase. -/
noncomputable def polarMap : (ℝ × ℝ) → ℂ := polarField Prod.fst Prod.snd

/-- A smooth inverse branch in density and dimensionless phase coordinates.
The physical action chart is divided by the same positive `ℏ`. -/
noncomputable def polarInverse (p : MassiveParameters) (a z : ℂ) : ℝ × ℝ :=
  (Complex.normSq z, PolarLocalInverse.localAction p a z / p.hbar)

/-- The forward polar coordinate map is smooth at every positive-density point. -/
theorem contDiffAt_polarMap {q : ℝ × ℝ} (hρ : 0 < q.1) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n polarMap q := by
  have hR : ContDiffAt ℝ n (fun x : ℝ × ℝ => (Real.sqrt x.1 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
    (contDiffAt_fst.sqrt (ne_of_gt hρ))
  have hΦ : ContDiffAt ℝ n (fun x : ℝ × ℝ => (x.2 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q contDiffAt_snd
  exact hR.mul ((hΦ.mul (contDiffAt_const (c := Complex.I))).cexp)

/-- The anchored inverse branch is smooth on its open logarithmic domain. -/
theorem contDiffAt_polarInverse (p : MassiveParameters) {a z : ℂ}
    (hz : z ∈ PolarLocalInverse.chartDomain a) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (polarInverse p a) z := by
  exact (PolarLocalInverse.contDiff_normSq n).contDiffAt.prodMk
    ((PolarLocalInverse.contDiffAt_localAction p hz n).div_const p.hbar)

/-- The coordinate map reconstructs every complex value from its inverse branch. -/
theorem polarMap_polarInverse (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    polarMap (polarInverse p a z) = z :=
  PolarLocalInverse.localAction_reconstruction p ha z

/-- The inverse branch recovers both positive density and the selected real phase. -/
theorem polarInverse_polarMap (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0)
    {q : ℝ × ℝ} (hρ : 0 < q.1) (hΦ : q.2 - a.arg ∈ Set.Ioo (-Real.pi) Real.pi) :
    polarInverse p a (polarMap q) = q := by
  have hh : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  have h := PolarLocalInverse.localAction_polar p ha (S := p.hbar * q.2) hρ
    (by simpa [hh] using hΦ)
  apply Prod.ext
  · exact ActionDensity.polarField_normSq Prod.fst Prod.snd q hρ.le
  · change PolarLocalInverse.localAction p a (polarMap q) / p.hbar = q.2
    simpa [polarMap, polarField, hh] using congrArg (fun S : ℝ => S / p.hbar) h

/-- A positive density and a single open phase branch land in the inverse domain. -/
theorem polarMap_mem_chartDomain (p : MassiveParameters) {a : ℂ} (ha : a ≠ 0)
    {q : ℝ × ℝ} (hρ : 0 < q.1) (hΦ : q.2 - a.arg ∈ Set.Ioo (-Real.pi) Real.pi) :
    polarMap q ∈ PolarLocalInverse.chartDomain a := by
  have hh : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  simpa [polarMap, polarField, hh] using
    PolarLocalInverse.polar_mem_chartDomain p ha (S := p.hbar * q.2) hρ
      (by simpa [hh] using hΦ)

/-- The actual Fréchet differential of the coordinate map on positive density. -/
theorem fderiv_polarMap_apply {q : ℝ × ℝ} (hρ : 0 < q.1) (v : ℝ × ℝ) :
    fderiv ℝ polarMap q v = polarTangent q.1 q.2 v.1 v.2 := by
  have h := fderiv_polarField_apply differentiableAt_fst differentiableAt_snd hρ v
  rw [fderiv_fst, fderiv_snd] at h
  exact h

/-- The actual coordinate differential pulls back both Hermitian components. -/
theorem fderiv_polarMap_conj_mul {q : ℝ × ℝ} (hρ : 0 < q.1) (v w : ℝ × ℝ) :
    conj (fderiv ℝ polarMap q v) * fderiv ℝ polarMap q w =
      (metric q.1 v w : ℂ) + Complex.I * (symplectic v w : ℂ) := by
  rw [fderiv_polarMap_apply hρ, fderiv_polarMap_apply hρ]
  exact polarTangent_conj_mul hρ q.2 v w

/-- The actual coordinate differential pulls back the Euclidean real metric. -/
theorem fderiv_polarMap_metric {q : ℝ × ℝ} (hρ : 0 < q.1) (v w : ℝ × ℝ) :
    (conj (fderiv ℝ polarMap q v) * fderiv ℝ polarMap q w).re = metric q.1 v w := by
  rw [fderiv_polarMap_conj_mul hρ]
  simp

/-- The actual differential pulls the standard complex area form back to the
closed, nondegenerate source form, with the stated orientation. -/
theorem fderiv_polarMap_symplecticForm {q : ℝ × ℝ} (hρ : 0 < q.1) (v w : ℝ × ℝ) :
    (conj (fderiv ℝ polarMap q v) * fderiv ℝ polarMap q w).im =
      symplecticForm ![v, w] := by
  rw [fderiv_polarMap_conj_mul hρ, symplecticForm_apply]
  simp

/-- The actual coordinate differential preserves the specified complex structures. -/
theorem fderiv_polarMap_complexStructure {q : ℝ × ℝ} (hρ : 0 < q.1) (v : ℝ × ℝ) :
    fderiv ℝ polarMap q (complexStructure q.1 v) =
      Complex.I * fderiv ℝ polarMap q v := by
  rw [fderiv_polarMap_apply hρ, fderiv_polarMap_apply hρ]
  exact polarTangent_complexStructure hρ q.2 v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hermitian pullback formula for genuine derivatives of arbitrary fields. -/
theorem fderiv_polarField_conj_mul {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v w : E) :
    conj (fderiv ℝ (polarField ρ Φ) x v) * fderiv ℝ (polarField ρ Φ) x w =
      (metric (ρ x) (fderiv ℝ ρ x v, fderiv ℝ Φ x v)
        (fderiv ℝ ρ x w, fderiv ℝ Φ x w) : ℂ) +
      Complex.I * (symplectic (fderiv ℝ ρ x v, fderiv ℝ Φ x v)
        (fderiv ℝ ρ x w, fderiv ℝ Φ x w) : ℂ) := by
  rw [fderiv_polarField_apply hρ hΦ hpos, fderiv_polarField_apply hρ hΦ hpos]
  exact polarTangent_conj_mul hpos (Φ x)
    (fderiv ℝ ρ x v, fderiv ℝ Φ x v) (fderiv ℝ ρ x w, fderiv ℝ Φ x w)

end FoliationQM.PolarKahlerGeometry
