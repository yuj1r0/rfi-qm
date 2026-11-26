module

public import FoliationQM.DyadicShellIntegral
public import FoliationQM.LocallyFlatTubeVolume
public import FoliationQM.LipschitzLogCutoff
public import FoliationQM.LogarithmicCutoffEnergy
public import FoliationQM.AuxiliaryCutoffEnergy

/-!
# The `L²` estimate for the logarithmic cutoff of a distance to the nodal set

Source: v13 `eq:log_cutoff_l2_bound`,
"`‖dχ_ε‖²_{L²(h)} ≤ (C/|ln ε|²) ∫_{ε²}^{ε} dr/r ≤ C/|ln ε| → 0`" with
`r = dist_h(x, 𝒩)`, component kinds C and D. Let `N` be closed relative to
the open coordinate domain `V` and locally a codimension-two axis there, `K`
a compact subset of `V`, and `r` a real function with, on `K`,

* `|r(y) − r(x)| ≤ L |y − x|` for `y` near `x` (Lipschitz in the chart), and
* `c · dist(x, N) ≤ r(x)` for the coordinate distance and some `c > 0`.

Then for the literal cutoff `χ_ε = χ_ε ∘ r` of `eq:log_cutoff_wallstrom` there
are `C` and `ε₀` with

`∫_K |dχ_ε|² ≤ C / |ln ε|` for `0 < ε < ε₀`,

so the energy tends to zero. The same holds for the energy
`√(det h) h⁻¹(dχ_ε, dχ_ε)` of any continuous positive-definite auxiliary
metric `h` on `K`. The hypotheses hold with `L = c = 1` for the coordinate
distance to `N`, and for the distance to `N` of any function `d` satisfying
the triangle inequality and `c |x − y| ≤ d(x, y) ≤ L |x − y|`.

The integrals are lower Lebesgue integrals of nonnegative functions; the
differential is the Fréchet differential, zero where it does not exist. That
the distance of a Riemannian metric satisfies the two-sided comparison with
the coordinate distance on compact sets is not proved here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DistanceCutoffEnergy

open Filter MeasureTheory Set Metric LorentzMatrixGroup AuxiliaryMetricEnergy
open LogarithmicCutoffProfile LocallyFlatNodalSet RNCCoordinateConnection RealLorentzFrame
open scoped Topology ENNReal Matrix.Norms.Operator

variable {N V K : Set Covector} {r : Covector → ℝ} {L c : ℝ}

/-- The tube bound in terms of the coordinate distance function. -/
theorem exists_infDist_tube_bound (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) :
    ∃ A s₀ : ℝ, 0 ≤ A ∧ 0 < s₀ ∧ ∀ s, 0 < s → s ≤ s₀ →
      volume (K ∩ {x | infDist x N < s}) ≤ ENNReal.ofReal (A * s ^ 2) := by
  obtain ⟨A, s₀, hA, hs₀, hb⟩ := LocallyFlatTubeVolume.exists_tube_bound h hK hKV
  refine ⟨A, s₀, hA, hs₀, fun s hs hle => ?_⟩
  have he : K ∩ {x | infDist x N < s} = K ∩ thickening s N := by
    ext x
    exact and_congr_right fun _ => (mem_thickening_iff_infDist_lt hN).symm
  rw [he]
  exact hb s hs hle

/-- The number of dyadic shells between `ε²` and `ε / c` is at most a
multiple of `|ln ε|`. -/
theorem exists_shell_count (hc : 0 < c) {ε : ℝ} (h0 : 0 < ε) (hε1 : ε ≤ Real.exp (-1))
    (hεc : ε ≤ 1 / c) :
    ∃ m : ℕ, ε < c * (2 ^ m * ε ^ 2) ∧ 2 ^ m * ε ^ 2 ≤ 2 * ε / c ∧
      (m : ℝ) ≤ (1 + (|Real.log c| + 1) / Real.log 2) * |Real.log ε| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogε : Real.log ε ≤ -1 := by
    have := Real.log_le_log h0 hε1
    rwa [Real.log_exp] at this
  have hℓ : |Real.log ε| = -Real.log ε := abs_of_neg (by linarith)
  have hℓ1 : 1 ≤ |Real.log ε| := by rw [hℓ]; linarith
  have hx1 : 1 ≤ 1 / (c * ε) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ hc).mp hεc
    linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx1 one_lt_two
  refine ⟨n + 1, ?_, ?_, ?_⟩
  · have h3 : 1 < 2 ^ (n + 1) * (c * ε) := by
      rwa [div_lt_iff₀ (by positivity)] at hn2
    nlinarith
  · have h3 : 2 ^ n * (c * ε) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hn1
    rw [le_div_iff₀ hc, pow_succ]
    nlinarith
  · have h3 : (n : ℝ) * Real.log 2 ≤ Real.log (1 / (c * ε)) := by
      have := Real.log_le_log (by positivity) hn1
      rwa [Real.log_pow] at this
    have h4 : Real.log (1 / (c * ε)) = -Real.log c - Real.log ε := by
      rw [one_div, Real.log_inv, Real.log_mul hc.ne' h0.ne']
      ring
    have h5 : -Real.log c ≤ |Real.log c| := neg_le_abs _
    have h6 : (n : ℝ) ≤ (|Real.log c| + |Real.log ε|) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      rw [h4] at h3
      rw [hℓ]
      linarith
    have h7 : (|Real.log c| + |Real.log ε|) / Real.log 2 ≤
        (|Real.log c| + 1) / Real.log 2 * |Real.log ε| := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hlog2.le
      nlinarith [abs_nonneg (Real.log c)]
    push_cast
    nlinarith

/-- The `L²` estimate for the logarithmic cutoff of a distance function:
`∫_K |dχ_ε|² ≤ C / |ln ε|` for small `ε`. -/
theorem exists_energy_bound (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∫⁻ x in K, ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2) ≤
        ENNReal.ofReal (C / |Real.log ε|) := by
  classical
  obtain ⟨A, s₀, hA, hs₀, htube⟩ := exists_infDist_tube_bound h hK hKV hN
  have hKm : MeasurableSet K := hK.measurableSet
  have hrK : ContinuousOn r K := fun x hx =>
    (LipschitzLogCutoff.continuousAt_of_lip (hlip x hx)).continuousWithinAt
  set rt : Covector → ℝ := K.piecewise r (fun _ => 0) with hrtdef
  have hrtm : Measurable rt := hrK.measurable_piecewise continuousOn_const hKm
  have hrt : ∀ x ∈ K, rt x = r x := fun x hx => piecewise_eq_of_mem K r _ hx
  have hδm : Measurable fun x : Covector => infDist x N := (continuous_infDist_pt N).measurable
  have hlow' : ∀ x ∈ K, c * infDist x N ≤ rt x := fun x hx => by
    rw [hrt x hx]
    exact hlow x hx
  set Q : ℝ := 1 + (|Real.log c| + 1) / Real.log 2 with hQdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQ : 0 ≤ Q := by positivity
  set C : ℝ := L ^ 2 * (A + 4 * A * Q / c ^ 2) with hCdef
  have hC : 0 ≤ C := by positivity
  have hexp : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  refine ⟨C, min (min (Real.exp (-1)) (1 / c)) (c * s₀ / 2), hC, by positivity,
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) hexp, fun ε h0 hε => ?_⟩
  have hε1 : ε ≤ Real.exp (-1) := hε.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεc : ε ≤ 1 / c := hε.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεs : ε ≤ c * s₀ / 2 := hε.le.trans (min_le_right _ _)
  have h1 : ε < 1 := lt_of_le_of_lt hε1 hexp
  have hℓ : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  have hℓ1 : 1 ≤ |Real.log ε| := by
    have := Real.log_le_log h0 hε1
    rw [Real.log_exp] at this
    rw [abs_of_neg (by linarith)]
    linarith
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_shell_count hc h0 hε1 hεc
  have hms : 2 ^ m * ε ^ 2 ≤ s₀ := hm2.trans (by
    rw [div_le_iff₀ hc]
    linarith)
  have hshell := DyadicShellIntegral.lintegral_between_le (μ := volume) (K := K)
    (b := ε) hδm hrtm hKm htube hA hc hlow' (sq_pos_of_pos h0) m hm1 hms
  set Sset : Set Covector := {x | ε ^ 2 ≤ rt x ∧ rt x ≤ ε} with hSdef
  have hSm : MeasurableSet Sset :=
    (measurableSet_le measurable_const hrtm).inter (measurableSet_le hrtm measurable_const)
  have hpoint : ∀ x ∈ K, ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2) ≤
      Sset.indicator (fun z => ENNReal.ofReal ((L / |Real.log ε|) ^ 2) *
        ENNReal.ofReal ((rt z)⁻¹ ^ 2)) x := by
    intro x hx
    have hb := LipschitzLogCutoff.norm_fderiv_sq_le h0 h1 hL (hlip x hx)
    by_cases hxS : ε ^ 2 ≤ r x ∧ r x ≤ ε
    · have hxS' : x ∈ Sset := by
        rw [hSdef, Set.mem_ofPred_eq, hrt x hx]
        exact hxS
      rw [indicator_of_mem (show x ∈ {z | ε ^ 2 ≤ r z ∧ r z ≤ ε} from hxS)] at hb
      rw [indicator_of_mem hxS', hrt x hx, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hb
    · rw [indicator_of_notMem (show x ∉ {z | ε ^ 2 ≤ r z ∧ r z ≤ ε} from hxS)] at hb
      have hz : ‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2 = 0 :=
        le_antisymm hb (sq_nonneg _)
      rw [hz, ENNReal.ofReal_zero]
      exact bot_le
  calc ∫⁻ x in K, ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2)
      ≤ ∫⁻ x in K, Sset.indicator (fun z => ENNReal.ofReal ((L / |Real.log ε|) ^ 2) *
          ENNReal.ofReal ((rt z)⁻¹ ^ 2)) x := setLIntegral_mono' hKm hpoint
    _ = ∫⁻ x in K ∩ Sset, ENNReal.ofReal ((L / |Real.log ε|) ^ 2) *
          ENNReal.ofReal ((rt x)⁻¹ ^ 2) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, inter_comm]
    _ = ENNReal.ofReal ((L / |Real.log ε|) ^ 2) *
          ∫⁻ x in K ∩ Sset, ENNReal.ofReal ((rt x)⁻¹ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((L / |Real.log ε|) ^ 2) *
          ENNReal.ofReal (A + 4 * A * m / c ^ 2) := by
        gcongr
    _ = ENNReal.ofReal ((L / |Real.log ε|) ^ 2 * (A + 4 * A * m / c ^ 2)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (C / |Real.log ε|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm4 : A + 4 * A * m / c ^ 2 ≤ |Real.log ε| * (A + 4 * A * Q / c ^ 2) := by
          have e1 : 4 * A * (m : ℝ) / c ^ 2 ≤ 4 * A * (Q * |Real.log ε|) / c ^ 2 := by
            gcongr
          have e2 : A ≤ |Real.log ε| * A := by nlinarith
          calc A + 4 * A * m / c ^ 2 ≤ |Real.log ε| * A + 4 * A * (Q * |Real.log ε|) / c ^ 2 :=
                add_le_add e2 e1
            _ = |Real.log ε| * (A + 4 * A * Q / c ^ 2) := by ring
        calc (L / |Real.log ε|) ^ 2 * (A + 4 * A * m / c ^ 2)
            ≤ (L / |Real.log ε|) ^ 2 * (|Real.log ε| * (A + 4 * A * Q / c ^ 2)) := by
              gcongr
          _ = C / |Real.log ε| := by
              rw [hCdef]
              field_simp

/-- The energy of the cutoff tends to zero with the cutoff radius. -/
theorem tendsto_energy (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) :
    Tendsto (fun ε : ℝ =>
      ∫⁻ x in K, ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, ε₀, hC, hε₀, -, hb⟩ := exists_energy_bound h hK hKV hN hL hc hlip hlow
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C / |Real.log ε|)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (LogarithmicCutoffEnergy.tendsto_inv_abs_log.const_mul C)
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun ε => ?_
    simp only [Function.comp_apply, mul_one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  exact hb ε hε.1 hε.2

/-- The density-weighted inverse-metric energy of a covector is at most
`16 B` times the squared norm of the linear form, when `B` bounds the
density-weighted inverse coefficients. -/
theorem auxiliary_energy_le {H : Mat4} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i j : Fin 4, ‖density H * H⁻¹ i j‖ ≤ B) (ℓ : Covector →L[ℝ] ℝ) :
    density H * realEnergy H (fun i => ℓ (axis i)) ≤ 16 * B * ‖ℓ‖ ^ 2 := by
  have ha (i : Fin 4) : ‖ℓ (axis i)‖ ≤ ‖ℓ‖ := by
    simpa [axis, Pi.norm_single] using ℓ.le_opNorm (axis i)
  have he : density H * realEnergy H (fun i => ℓ (axis i)) =
      ∑ i : Fin 4, ∑ j : Fin 4, (density H * H⁻¹ i j) * ℓ (axis i) * ℓ (axis j) := by
    simp only [realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [he]
  calc ∑ i : Fin 4, ∑ j : Fin 4, (density H * H⁻¹ i j) * ℓ (axis i) * ℓ (axis j)
      ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, B * ‖ℓ‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc (density H * H⁻¹ i j) * ℓ (axis i) * ℓ (axis j)
            ≤ ‖(density H * H⁻¹ i j) * ℓ (axis i) * ℓ (axis j)‖ := le_abs_self _
          _ = ‖density H * H⁻¹ i j‖ * ‖ℓ (axis i)‖ * ‖ℓ (axis j)‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ (B * ‖ℓ‖) * ‖ℓ‖ :=
              mul_le_mul (mul_le_mul (hb i j) (ha i) (norm_nonneg _) hB) (ha j) (norm_nonneg _)
                (mul_nonneg hB (norm_nonneg _))
          _ = B * ‖ℓ‖ ^ 2 := by ring
    _ = 16 * B * ‖ℓ‖ ^ 2 := by
        simp
        ring

/-- The `L²(h)` estimate: for a continuous positive-definite auxiliary metric
on the compact set, the `h`-energy of the cutoff is at most `C / |ln ε|`. -/
theorem exists_auxiliary_energy_bound (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) {H : Covector → Mat4} (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∫⁻ x in K, ENNReal.ofReal (density (H x) * realEnergy (H x)
        (fun i => fderiv ℝ (fun y => profile ε (r y)) x (axis i))) ≤
        ENNReal.ofReal (C / |Real.log ε|) := by
  obtain ⟨B, hB, hb⟩ := AuxiliaryCutoffEnergy.compact_coefficient_bounds hK hH hpos
  obtain ⟨C, ε₀, hC, hε₀, hε₁, hbound⟩ := exists_energy_bound h hK hKV hN hL hc hlip hlow
  refine ⟨16 * B * C, ε₀, by positivity, hε₀, hε₁, fun ε h0 hε => ?_⟩
  calc ∫⁻ x in K, ENNReal.ofReal (density (H x) * realEnergy (H x)
        (fun i => fderiv ℝ (fun y => profile ε (r y)) x (axis i)))
      ≤ ∫⁻ x in K, ENNReal.ofReal (16 * B) *
          ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2) := by
        refine setLIntegral_mono' hK.measurableSet fun x hx => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (auxiliary_energy_le hB (hb x hx) _)
    _ = ENNReal.ofReal (16 * B) *
          ∫⁻ x in K, ENNReal.ofReal (‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (16 * B) * ENNReal.ofReal (C / |Real.log ε|) := by
        gcongr
        exact hbound ε h0 hε
    _ = ENNReal.ofReal (16 * B * C / |Real.log ε|) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The coordinate distance to the nodal set satisfies the two hypotheses
with constants one. -/
theorem infDist_data (x : Covector) :
    (∀ᶠ y in 𝓝 x, |infDist y N - infDist x N| ≤ 1 * ‖y - x‖) ∧
      1 * infDist x N ≤ infDist x N := by
  refine ⟨Eventually.of_forall fun y => ?_, by rw [one_mul]⟩
  have h := (lipschitz_infDist_pt N).dist_le_mul y x
  rwa [Real.dist_eq, NNReal.coe_one, dist_eq_norm] at h

/-- The distance to the nodal set of a function `d` with the triangle
inequality and a two-sided comparison with the coordinate distance. -/
def distanceTo (d : Covector → Covector → ℝ) (N : Set Covector) (x : Covector) : ℝ :=
  ⨅ z : N, d x z

/-- The distance to the nodal set of a comparable distance function satisfies
the two hypotheses. -/
theorem distanceTo_data {d : Covector → Covector → ℝ} (hN : N.Nonempty) (hc : 0 ≤ c)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hlower : ∀ x y, c * ‖x - y‖ ≤ d x y) (hupper : ∀ x y, d x y ≤ L * ‖x - y‖)
    (x : Covector) :
    (∀ᶠ y in 𝓝 x, |distanceTo d N y - distanceTo d N x| ≤ L * ‖y - x‖) ∧
      c * infDist x N ≤ distanceTo d N x := by
  have : Nonempty N := hN.to_subtype
  have hbdd : ∀ u, BddBelow (range fun z : N => d u z) := fun u =>
    ⟨0, by
      rintro _ ⟨z, rfl⟩
      exact (mul_nonneg hc (norm_nonneg _)).trans (hlower u z)⟩
  have hstep : ∀ u v, distanceTo d N u ≤ distanceTo d N v + d u v := by
    intro u v
    rw [distanceTo, distanceTo, ← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    exact (ciInf_le (hbdd u) z).trans (by linarith [htri u v z])
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · rw [abs_le]
    have h1 := (hstep y x).trans (add_le_add_right (hupper y x) _)
    have h2 := (hstep x y).trans (add_le_add_right (hupper x y) _)
    rw [← norm_neg, neg_sub] at h2
    constructor <;> linarith
  · refine le_ciInf fun z => ?_
    have h1 : infDist x N ≤ dist x z := infDist_le_dist_of_mem z.property
    rw [dist_eq_norm] at h1
    exact (mul_le_mul_of_nonneg_left h1 hc).trans (hlower x z)

/-- A family bounded by `C / |ln ε|` for small `ε` tends to zero. -/
theorem tendsto_of_log_bound {f : ℝ → ℝ≥0∞}
    (hf : ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      f ε ≤ ENNReal.ofReal (C / |Real.log ε|)) : Tendsto f (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, ε₀, -, hε₀, -, hb⟩ := hf
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C / |Real.log ε|)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (LogarithmicCutoffEnergy.tendsto_inv_abs_log.const_mul C)
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun ε => ?_
    simp only [Function.comp_apply, mul_one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  exact hb ε hε.1 hε.2

/-- The `L²(h)` energy of the cutoff tends to zero with the cutoff radius. -/
theorem tendsto_auxiliary_energy (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) {H : Covector → Mat4} (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    Tendsto (fun ε : ℝ => ∫⁻ x in K, ENNReal.ofReal (density (H x) * realEnergy (H x)
      (fun i => fderiv ℝ (fun y => profile ε (r y)) x (axis i)))) (𝓝[>] 0) (𝓝 0) :=
  tendsto_of_log_bound (exists_auxiliary_energy_bound h hK hKV hN hL hc hlip hlow hH hpos)

/-- The Euclidean distance of the four coordinates. -/
def euclideanDist (x y : Covector) : ℝ := ‖ProductTubeCoordinates.coordinates (x - y)‖

/-- The Euclidean distance to the nodal set satisfies the two hypotheses,
with constants the norms of the coordinate equivalence and its inverse. -/
theorem euclidean_data (hN : N.Nonempty) (x : Covector) :
    (∀ᶠ y in 𝓝 x, |distanceTo euclideanDist N y - distanceTo euclideanDist N x| ≤
      ‖(ProductTubeCoordinates.coordinates : Covector →L[ℝ] WithLp 2 (ℂ × ℂ))‖ * ‖y - x‖) ∧
      ‖(ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector)‖⁻¹ * infDist x N ≤
        distanceTo euclideanDist N x := by
  refine distanceTo_data hN (inv_nonneg.mpr (norm_nonneg _)) (fun u v w => ?_) (fun u v => ?_)
    (fun u v => ?_) x
  · have e : u - w = (u - v) + (v - w) := by abel
    rw [euclideanDist, euclideanDist, euclideanDist, e, map_add]
    exact norm_add_le _ _
  · have h1 : ‖u - v‖ ≤ ‖(ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector)‖ *
        ‖ProductTubeCoordinates.coordinates (u - v)‖ := by
      have := (ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector).le_opNorm
        (ProductTubeCoordinates.coordinates (u - v))
      simpa using this
    rcases eq_or_lt_of_le (norm_nonneg
      (ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector)) with h0 | hpos
    · rw [← h0, inv_zero, zero_mul]
      exact norm_nonneg _
    · rw [inv_mul_le_iff₀ hpos]
      exact h1
  · exact (ProductTubeCoordinates.coordinates : Covector →L[ℝ] WithLp 2 (ℂ × ℂ)).le_opNorm (u - v)

/-- The norm of the inverse coordinate equivalence is positive. -/
theorem norm_coordinates_symm_pos :
    0 < ‖(ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector)‖ := by
  by_contra hn
  have h0 : ‖(ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector)‖ = 0 :=
    le_antisymm (not_lt.mp hn) (norm_nonneg _)
  have h1 := (ProductTubeCoordinates.coordinates.symm : WithLp 2 (ℂ × ℂ) →L[ℝ] Covector).le_opNorm
    (ProductTubeCoordinates.coordinates (axis 0))
  rw [h0, zero_mul] at h1
  have h2 : ‖axis 0‖ ≤ 0 := by simpa using h1
  have h3 : ‖axis 0‖ = 1 := by simp [axis, Pi.norm_single]
  linarith

/-- The `L²(h)` estimate for the cutoff of the Euclidean distance to the
nodal set. -/
theorem exists_euclidean_energy_bound (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) {H : Covector → Mat4} (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∫⁻ x in K, ENNReal.ofReal (density (H x) * realEnergy (H x)
        (fun i => fderiv ℝ (fun y => profile ε (distanceTo euclideanDist N y)) x (axis i))) ≤
        ENNReal.ofReal (C / |Real.log ε|) :=
  exists_auxiliary_energy_bound h hK hKV hN (norm_nonneg _)
    (inv_pos.mpr norm_coordinates_symm_pos) (fun x _ => (euclidean_data hN x).1)
    (fun x _ => (euclidean_data hN x).2) hH hpos

end FoliationQM.DistanceCutoffEnergy
