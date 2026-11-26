module

public import FoliationQM.ConeRadialCompletion

/-!
# Recovering tangential geometry from actual cone path lengths

Source: v13 `lem:uniqueness`, the metric-to-tangent step away from the tip.
The estimates here concern the constructed path infimum, with actual C1 paths
and actual source speeds. In particular no equality of metric speed and tensor
speed is postulated.
-/
@[expose] public section
noncomputable section

namespace FoliationQM.ConeTangentialDistance

open ConeManifold ConeIntrinsicMetric ConeSpeed ConeMetricExtension
open Set MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal Manifold

/-- The angular projection is controlled by source speed with coefficient one. -/
theorem angular_projection_le (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    |(conj z * v).im| ≤ ‖z‖ * speed hbar coupling z v := by
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hid : (conj z * v).re ^ 2 + (conj z * v).im ^ 2 =
      Complex.normSq z * Complex.normSq v := by
    have h : Complex.normSq (conj z * v) = Complex.normSq z * Complex.normSq v := by simp
    rw [Complex.normSq_apply] at h
    nlinarith
  have hs : speed hbar coupling z v ^ 2 = tensor hbar coupling z v v :=
    Real.sq_sqrt (tensor_nonneg hbar coupling hh hc z v)
  have ht : Complex.normSq z * tensor hbar coupling z v v =
      radialFactorSq hbar coupling * (conj z * v).re ^ 2 + (conj z * v).im ^ 2 := by
    rw [tensor_self_eq]
    change Complex.normSq z * (Complex.normSq v +
      (radialFactorSq hbar coupling - 1) * ((conj z * v).re ^ 2 / Complex.normSq z)) = _
    field_simp
    nlinarith
  have hnon := mul_nonneg (radialFactorSq_pos hbar coupling hh hc).le
    (sq_nonneg (conj z * v).re)
  have hnorm := Complex.normSq_eq_norm_sq z
  have ha : 0 ≤ ‖z‖ * speed hbar coupling z v :=
    mul_nonneg (norm_nonneg _) (speed_nonneg _ _ _ _)
  nlinarith [sq_abs (conj z * v).im]

/-- Near the physical point one, the fixed imaginary projection is controlled
by source speed with a coefficient tending to one as the neighborhood shrinks. -/
theorem imag_le_local_speed (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    {δ : ℝ} {z : ℂ} (hz : z ≠ 0) (hd : ‖z - 1‖ ≤ δ) (v : ℂ) :
    |v.im| ≤ (1 + δ + δ / lowerFactor hbar coupling) * speed hbar coupling z v := by
  have hm := lowerFactor_pos hbar coupling hh hc
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hd
  have hv := speed_lower_bound hbar coupling hh hc z v
  have hz' : ‖z‖ ≤ 1 + δ := by
    have h := norm_le_norm_sub_add z (1 : ℂ)
    simp only [norm_one] at h
    linarith
  have he : v.im = (conj z * v).im + (conj (1 - z) * v).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  calc
    |v.im| ≤ |(conj z * v).im| + |(conj (1 - z) * v).im| := by
      rw [he]; exact abs_add_le _ _
    _ ≤ ‖z‖ * speed hbar coupling z v + ‖z - 1‖ * ‖v‖ := by
      apply add_le_add (angular_projection_le hbar coupling hh hc hz v)
      simpa only [norm_mul, Complex.norm_conj, norm_sub_rev] using
        Complex.abs_im_le_norm (conj (1 - z) * v)
    _ ≤ (1 + δ) * speed hbar coupling z v + δ * ‖v‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_right hz' (speed_nonneg _ _ _ _))
        (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    _ ≤ (1 + δ) * speed hbar coupling z v +
        δ * (speed hbar coupling z v / lowerFactor hbar coupling) := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hv)
    _ = (1 + δ + δ / lowerFactor hbar coupling) * speed hbar coupling z v := by ring

/-- A globally nonvanishing vertical probe through the physical point one. -/
def verticalPoint (hbar coupling t : ℝ) : Point hbar coupling where
  value := 1 + (t : ℂ) * Complex.I
  value_ne_zero := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- Every point on a sufficiently short actual C1 path stays near its starting
physical coordinate. This uses the genuine intrinsic distance on each prefix. -/
theorem short_path_stays_near_start {γ : ℝ → Point hbar coupling}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) {δ : ℝ} (hδ : 0 < δ)
    (hlen : Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 <
      ENNReal.ofReal (lowerFactor hbar coupling * δ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ 0).value (γ t).value < δ := by
  have hm := lowerFactor_pos hbar coupling Fact.out Fact.out
  have hl : ENNReal.ofReal (lowerFactor hbar coupling *
      dist (γ 0).value (γ t).value) ≤ Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 := by
    rw [ENNReal.ofReal_mul hm.le, ← edist_dist]
    apply (intrinsicEDist_lower_bound hbar coupling Fact.out Fact.out (γ 0) (γ t)).trans
    apply (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl ht.1).trans
    exact Manifold.pathELength_mono le_rfl ht.2
  have h := (ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hδ)).mp (hl.trans_lt hlen)
  exact (mul_lt_mul_iff_right₀ hm).mp h

/-- A C1 path confined near one pays almost its full imaginary endpoint
variation, by the actual derivative projection bound and the fundamental theorem. -/
theorem imag_variation_le_confined_path {γ : ℝ → Point hbar coupling}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hconf : ∀ t ∈ Icc (0 : ℝ) 1, ‖(γ t).value - 1‖ ≤ δ) :
    ENNReal.ofReal |(γ 1).value.im - (γ 0).value.im| ≤
      ENNReal.ofReal (1 + δ + δ / lowerFactor hbar coupling) *
        Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 := by
  have hm := lowerFactor_pos hbar coupling Fact.out Fact.out
  have hv : ContDiff ℝ 1 (fun t => (γ t).value) :=
    contMDiff_iff_contDiff.mp ((contMDiff_value 1).comp hγ)
  have him : ContDiff ℝ 1 (fun t => (γ t).value.im) := Complex.imCLM.contDiff.comp hv
  have hfund := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc him.contDiffOn zero_le_one
  rw [Real.enorm_eq_ofReal_abs] at hfund
  apply hfund.trans
  rw [pathELength_eq_integral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hd : deriv (fun u => (γ u).value.im) t =
      (deriv (fun u => (γ u).value) t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hv.differentiable (by norm_num)) t).hasDerivAt).deriv
  rw [hd, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (imag_le_local_speed hbar coupling Fact.out Fact.out
      (γ t).value_ne_zero (hconf t ht) _)

/-- If the actual intrinsic cone distance were a constant multiple of every
physical chord, that multiple could not be smaller than one. Short-path
confinement and the local tangential projection rule out such a collapse. -/
theorem one_le_scale_of_dist_eq (a : ℝ) (ha : 0 < a)
    (hdist : ∀ p q : Point hbar coupling, dist p q = a * dist p.value q.value) :
    1 ≤ a := by
  by_contra h
  have ha1 : a < 1 := lt_of_not_ge h
  let c := (a + 1) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hac : a < c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  let m := lowerFactor hbar coupling
  have hm : 0 < m := lowerFactor_pos hbar coupling Fact.out Fact.out
  let δ := (1 - c) / (2 * c * (1 + 1 / m))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let t := m * δ / (2 * c)
  have ht : 0 < t := by dsimp [t]; positivity
  have hct : c * t < m * δ := by
    have he : c * t = m * δ / 2 := by dsimp [t]; field_simp
    rw [he]
    nlinarith [mul_pos hm hδ]
  have hD : (1 + δ + δ / m) * c = (1 + c) / 2 := by
    dsimp [δ]
    field_simp
    ring
  let p := verticalPoint hbar coupling 0
  let q := verticalPoint hbar coupling t
  have hp : p.value = 1 := by simp [p, verticalPoint]
  have hq : q.value.im = t := by simp [q, verticalPoint]
  have hchord : dist p.value q.value = t := by
    simp [p, q, verticalPoint, dist_eq_norm, Complex.norm_real, abs_of_pos ht]
  have hsmall : intrinsicEDist hbar coupling p q < ENNReal.ofReal (c * t) := by
    rw [← edist_eq_intrinsicEDist, edist_dist, hdist, hchord]
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc ht)).mpr
      (mul_lt_mul_of_pos_right hac ht)
  obtain ⟨γ, hzero, hone, hsmooth, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hsmall zero_lt_one
  have hlen' : Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 < ENNReal.ofReal (m * δ) :=
    hlen.trans ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hδ)).mpr hct)
  have hconf (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖(γ u).value - 1‖ ≤ δ := by
    have hu' := short_path_stays_near_start hbar coupling hsmooth hδ hlen' hu
    rw [hzero, hp, dist_comm, dist_eq_norm] at hu'
    exact hu'.le
  have hvar := imag_variation_le_confined_path hbar coupling hsmooth hδ.le hconf
  rw [hzero, hone, hp, hq, Complex.one_im, sub_zero, abs_of_pos ht] at hvar
  have hDpos : 0 < 1 + δ + δ / m := by positivity
  have hstrict : ENNReal.ofReal t < ENNReal.ofReal ((1 + δ + δ / m) * (c * t)) := by
    apply hvar.trans_lt
    rw [ENNReal.ofReal_mul hDpos.le]
    simpa only [mul_comm] using
      (ENNReal.mul_lt_mul_left (ENNReal.ofReal_ne_zero_iff.mpr hDpos)
        ENNReal.ofReal_ne_top hlen)
  have hreal : t < (1 + δ + δ / m) * (c * t) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos hDpos (mul_pos hc ht))).mp hstrict
  rw [← mul_assoc, hD] at hreal
  nlinarith

end FoliationQM.ConeTangentialDistance
