module

public import FoliationQM.PolarKahlerGeometry
public import FoliationQM.ActionDensity
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Extension of the cone tensor in the fixed physical Cartesian coordinate

Sources: v13 `lem:uniqueness`, `eq:lambda_metric`, `eq:unique_params`.
The coordinate is the fixed degree-one Born map `sqrt(rho) * exp(i*Phi)`.
We express the actual source tensor in this coordinate and test continuity
at its missing origin. This is an obstruction in the specified physical
Cartesian chart, not a claim about every possible smooth atlas or a metric
completion not yet constructed.
-/
@[expose] public section

namespace FoliationQM.ConeMetricExtension

open MasterMetricAndCone PolarKahlerGeometry PolarDifferential
open scoped ComplexConjugate Topology ContDiff

/-- The Euclidean scalar product in the physical complex plane. -/
noncomputable def euclidean (v w : ℂ) : ℝ := (conj v * w).re

/-- Radial projection before normalization by the radius. -/
noncomputable def radial (z v : ℂ) : ℝ := (conj z * v).re

/-- The source cone tensor in the fixed degree-one Cartesian coordinate,
away from zero. Its value at zero is totalized and is not used for limits. -/
noncomputable def tensor (hbar coupling : ℝ) (z v w : ℂ) : ℝ :=
  euclidean v w + (4 * coupling / hbar ^ 2 - 1) * radial z v * radial z w /
    Complex.normSq z

/-- The tensor is symmetric in its tangent arguments. -/
theorem tensor_symm (hbar coupling : ℝ) (z v w : ℂ) :
    tensor hbar coupling z v w = tensor hbar coupling z w v := by
  simp only [tensor, euclidean, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Canonical coupling gives the ordinary Euclidean tensor, including at zero. -/
theorem tensor_canonical (hbar : ℝ) (hh : 0 < hbar) (z v w : ℂ) :
    tensor hbar (hbar ^ 2 / 4) z v w = euclidean v w := by
  have he : 4 * (hbar ^ 2 / 4) / hbar ^ 2 = 1 := by field_simp
  simp only [tensor, he, sub_self, zero_mul, zero_div, add_zero]

/-- The real-axis radial probe measures the radial coefficient at every
nonzero distance from the origin. -/
theorem tensor_real_axis (hbar coupling t : ℝ) (ht : t ≠ 0) :
    tensor hbar coupling (t : ℂ) 1 1 = 4 * coupling / hbar ^ 2 := by
  simp only [tensor, euclidean, radial, map_one, Complex.one_re,
    mul_one, Complex.conj_ofReal, Complex.ofReal_re, Complex.normSq_ofReal]
  field_simp
  ring

/-- The same fixed Cartesian tangent is tangential on the imaginary axis,
so its metric coefficient is one at every nonzero radius. -/
theorem tensor_imag_axis (hbar coupling t : ℝ) :
    tensor hbar coupling ((t : ℂ) * Complex.I) 1 1 = 1 := by
  simp [tensor, euclidean, radial, Complex.mul_re]

/-- Actual polar tangents have radial projection equal to half their density
increment. Positivity justifies the square-root division. -/
theorem radial_polarTangent (ρ Φ dρ dΦ : ℝ) (hρ : 0 < ρ) :
    radial ((Real.sqrt ρ : ℂ) * phase Φ) (polarTangent ρ Φ dρ dΦ) = dρ / 2 := by
  have hp : conj (phase Φ) * phase Φ = 1 := by
    change conj (Circle.exp Φ : ℂ) * (Circle.exp Φ : ℂ) = 1
    rw [← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
  have hs : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ)
  unfold radial polarTangent amplitudeTangent
  rw [map_mul, Complex.conj_ofReal,
    show (Real.sqrt ρ : ℂ) * conj (phase Φ) *
      (phase Φ * ((dρ / (2 * Real.sqrt ρ) : ℝ) +
        Complex.I * (Real.sqrt ρ : ℂ) * (dΦ : ℂ))) =
      (Real.sqrt ρ : ℂ) * (conj (phase Φ) * phase Φ) *
        ((dρ / (2 * Real.sqrt ρ) : ℝ) +
          Complex.I * (Real.sqrt ρ : ℂ) * (dΦ : ℂ)) by ring,
    hp, mul_one]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  simp only [mul_zero, zero_mul, zero_add, add_zero, sub_zero]
  field_simp

/-- The tensor's pullback by the actual degree-one polar derivative is exactly
the arbitrary-coupling source bilinear form. -/
theorem tensor_fderiv_polarMap (hbar coupling : ℝ) (q v w : ℝ × ℝ) (hq : 0 < q.1) :
    tensor hbar coupling (polarMap q)
      (fderiv ℝ polarMap q v) (fderiv ℝ polarMap q w) =
      coupling / (hbar ^ 2 * q.1) * v.1 * w.1 + q.1 * v.2 * w.2 := by
  have hn : Complex.normSq (polarMap q) = q.1 :=
    ActionDensity.polarField_normSq Prod.fst Prod.snd q hq.le
  have hr (u : ℝ × ℝ) : radial (polarMap q) (fderiv ℝ polarMap q u) = u.1 / 2 := by
    rw [fderiv_polarMap_apply hq]
    exact radial_polarTangent q.1 q.2 u.1 u.2 hq
  have he : euclidean (fderiv ℝ polarMap q v) (fderiv ℝ polarMap q w) =
      metric q.1 v w := fderiv_polarMap_metric hq v w
  rw [tensor, hn, hr, hr, he, metric_apply]
  ring

/-- Any continuous scalar extension of even this single Cartesian component
forces canonical coupling. Real and imaginary approaches have different limits
unless the radial coefficient is one. -/
theorem continuous_component_extension_forces_canonical (hbar coupling : ℝ)
    (hh : 0 < hbar) (f : ℂ → ℝ) (hf : ContinuousAt f 0)
    (hagree : ∀ z : ℂ, z ≠ 0 → f z = tensor hbar coupling z 1 1) :
    coupling = hbar ^ 2 / 4 := by
  have hreal : f 0 = 4 * coupling / hbar ^ 2 := by
    have hc : ContinuousAt (fun t : ℝ => f (t : ℂ)) 0 :=
      hf.comp_of_eq (f := fun t : ℝ => (t : ℂ))
        Complex.continuous_ofReal.continuousAt rfl
    have heq : (fun t : ℝ => f (t : ℂ)) =ᶠ[𝓝[≠] 0]
        (fun _ => 4 * coupling / hbar ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      rw [hagree _ (by exact_mod_cast ht0), tensor_real_axis _ _ _ ht0]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' heq.symm)
  have himag : f 0 = 1 := by
    have hc : ContinuousAt (fun t : ℝ => f ((t : ℂ) * Complex.I)) 0 := by
      exact hf.comp_of_eq (f := fun t : ℝ => (t : ℂ) * Complex.I)
        (Complex.continuous_ofReal.continuousAt.mul_const Complex.I) (by simp)
    have heq : (fun t : ℝ => f ((t : ℂ) * Complex.I)) =ᶠ[𝓝[≠] 0] (fun _ => 1) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 from ht)
      rw [hagree _ (mul_ne_zero ht0 Complex.I_ne_zero), tensor_imag_axis]
    simpa using tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' heq.symm)
  have he : 4 * coupling / hbar ^ 2 = 1 := hreal.symm.trans himag
  have hh0 : hbar ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hh)
  have hm := (div_eq_iff hh0).1 he
  linarith

/-- A componentwise continuous tensor extension through the fixed physical
Cartesian origin exists exactly at canonical coupling. -/
theorem exists_continuous_tensor_extension_iff (hbar coupling : ℝ) (hh : 0 < hbar) :
    (∃ G : ℂ → ℂ → ℂ → ℝ,
      (∀ v w, ContinuousAt (fun z => G z v w) 0) ∧
      (∀ z, z ≠ 0 → ∀ v w, G z v w = tensor hbar coupling z v w)) ↔
      coupling = hbar ^ 2 / 4 := by
  constructor
  · rintro ⟨G, hc, he⟩
    exact continuous_component_extension_forces_canonical hbar coupling hh
      (fun z => G z 1 1) (hc 1 1) (fun z hz => he z hz 1 1)
  · rintro rfl
    refine ⟨fun _ v w => euclidean v w, fun _ _ => continuousAt_const, ?_⟩
    intro z _ v w
    exact (tensor_canonical hbar hh z v w).symm

/-- The canonical extension is smooth in position, with Euclidean
coefficients at every point, including the added origin. -/
theorem contDiff_canonical_tensor (hbar : ℝ) (hh : 0 < hbar)
    (v w : ℂ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : ℂ => tensor hbar (hbar ^ 2 / 4) z v w) := by
  simp_rw [tensor_canonical hbar hh]
  exact contDiff_const

/-- The canonical tensor is positive on every nonzero tangent, including at
its added origin. -/
theorem tensor_canonical_pos (hbar : ℝ) (hh : 0 < hbar) (z : ℂ) {v : ℂ}
    (hv : v ≠ 0) : 0 < tensor hbar (hbar ^ 2 / 4) z v v := by
  rw [tensor_canonical hbar hh]
  change 0 < (conj v * v).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_pos.mpr hv

/-- The Euclidean extension is jointly smooth in position and both tangent
arguments, not merely continuous in a selected component. -/
theorem contDiff_euclidean_joint (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun q : ℂ × ℂ × ℂ => euclidean q.2.1 q.2.2) := by
  exact Complex.reCLM.contDiff.comp
    ((Complex.conjCLE.contDiff.comp (contDiff_fst.comp contDiff_snd)).mul
      (contDiff_snd.comp contDiff_snd))

/-- A jointly smooth tensor extension in the fixed physical Cartesian
coordinate exists exactly for canonical coupling. -/
theorem exists_smooth_tensor_extension_iff (hbar coupling : ℝ) (hh : 0 < hbar) :
    (∃ G : ℂ → ℂ → ℂ → ℝ,
      ContDiff ℝ ∞ (fun q : ℂ × ℂ × ℂ => G q.1 q.2.1 q.2.2) ∧
      (∀ z, z ≠ 0 → ∀ v w, G z v w = tensor hbar coupling z v w)) ↔
      coupling = hbar ^ 2 / 4 := by
  constructor
  · rintro ⟨G, hG, he⟩
    apply (exists_continuous_tensor_extension_iff hbar coupling hh).1
    refine ⟨G, ?_, he⟩
    intro v w
    have hc : ContDiff ℝ ∞ (fun z : ℂ => G z v w) :=
      hG.comp (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))
    exact hc.continuous.continuousAt
  · rintro rfl
    refine ⟨fun _ v w => euclidean v w, contDiff_euclidean_joint ∞, ?_⟩
    intro z _ v w
    exact (tensor_canonical hbar hh z v w).symm

end FoliationQM.ConeMetricExtension
