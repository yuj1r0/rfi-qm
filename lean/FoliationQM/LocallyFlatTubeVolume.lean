module

public import FoliationQM.LocallyFlatNodalSet
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The quadratic tube-volume bound for a locally flat nodal set

Source: v13 `thm:wallstrom` Part(c), "the codimension-2 tubular volume
element is bounded by `C r dr dθ dvol_𝒩`", used in `eq:log_cutoff_l2_bound`,
component kinds B and C. Let `N` be closed relative to the open coordinate
domain `V` and locally a codimension-two axis there, and `K` a compact subset
of `V`. Then there are `A` and `s₀ > 0` with

`volume (K ∩ {x | dist(x, N) < s}) ≤ A s²` for `0 < s ≤ s₀`.

The distance is the coordinate distance of the four real coordinates. The
proof covers the part of `N` near `K` by finitely many adapted charts; in each
the tube lies in the preimage of a coordinate box with two sides of length
`2 L s`, and the Jacobian of the inverse chart is bounded on a compact set.
No tubular-neighbourhood theorem or normal exponential map is used. The
comparison of an auxiliary Riemannian distance with the coordinate distance
is separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LocallyFlatTubeVolume

open MeasureTheory Set Metric RealLorentzFrame LocallyFlatNodalSet
open scoped ContDiff Topology ENNReal

/-- The coordinate box with two long sides and two short sides. -/
def box (y : Covector) (D t : ℝ) : Set Covector :=
  Set.pi univ fun i : Fin 4 =>
    if i = 2 ∨ i = 3 then Ioo (-t) t else Icc (y i - D) (y i + D)

/-- The volume of the box is `16 D² t²`. -/
theorem volume_box (y : Covector) {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    volume (box y D t) = ENNReal.ofReal (16 * D ^ 2 * t ^ 2) := by
  have e0 : volume (Icc (y 0 - D) (y 0 + D)) = ENNReal.ofReal (2 * D) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have e1 : volume (Icc (y 1 - D) (y 1 + D)) = ENNReal.ofReal (2 * D) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have e2 : volume (Ioo (-t) t) = ENNReal.ofReal (2 * t) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hprod : volume (box y D t) =
      ENNReal.ofReal (2 * D) * ENNReal.ofReal (2 * D) * ENNReal.ofReal (2 * t) *
        ENNReal.ofReal (2 * t) := by
    rw [box, volume_pi_pi, Fin.prod_univ_four]
    simp [e0, e1, e2]
  rw [hprod, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * D by positivity),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * D * (2 * D) by positivity),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * D * (2 * D) * (2 * t) by positivity)]
  congr 1
  ring

/-- Near a point of the source of a smooth coordinate change, the points
within distance `s` of the part of the preimage of the axis in a small ball
have volume at most a constant times `s²`. -/
theorem exists_local_tube_bound (e : OpenPartialHomeomorph Covector Covector)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) {z : Covector}
    (hz : z ∈ e.source) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧ ball z (2 * ρ) ⊆ e.source ∧ ∀ s, 0 < s → s ≤ ρ →
      volume {x | ∃ w ∈ ball z ρ, (e w) 2 = 0 ∧ (e w) 3 = 0 ∧ dist x w < s} ≤
        ENNReal.ofReal (B * s ^ 2) := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp e.open_source z hz
  set ρ : ℝ := ρ₀ / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  set C : Set Covector := closedBall z (2 * ρ) with hCdef
  have hCsub : C ⊆ e.source := fun x hx => hball (lt_of_le_of_lt (mem_closedBall.mp hx)
    (by rw [hρdef]; linarith))
  have hCc : IsCompact C := isCompact_closedBall z (2 * ρ)
  have hdiff : ∀ x ∈ C, DifferentiableAt ℝ e x := fun x hx =>
    (he.contDiffAt (e.open_source.mem_nhds (hCsub hx))).differentiableAt (by simp)
  have hcontd : ContinuousOn (fun x => fderiv ℝ e x) C :=
    (he.continuousOn_fderiv_of_isOpen e.open_source (by simp)).mono hCsub
  obtain ⟨L₀, hL₀⟩ := hCc.exists_bound_of_continuousOn hcontd
  set L : ℝ := |L₀| + 1 with hLdef
  have hL : 0 < L := by positivity
  have hLb : ∀ x ∈ C, ‖fderiv ℝ e x‖ ≤ L := fun x hx =>
    (hL₀ x hx).trans ((le_abs_self L₀).trans (by linarith))
  have hlip : ∀ x ∈ C, ∀ y ∈ C, ‖e y - e x‖ ≤ L * ‖y - x‖ := fun x hx y hy =>
    (convex_closedBall z (2 * ρ)).norm_image_sub_le_of_norm_fderiv_le hdiff hLb hx hy
  set T : Set Covector := e '' C with hTdef
  have hTc : IsCompact T := hCc.image_of_continuousOn (e.continuousOn.mono hCsub)
  have hTsub : T ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hCsub hx)
  have hdetc : ContinuousOn (fun y => (fderiv ℝ e.symm y).det) T :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (hi.continuousOn_fderiv_of_isOpen e.open_target (by simp))).mono hTsub
  obtain ⟨J₀, hJ₀⟩ := hTc.exists_bound_of_continuousOn hdetc
  set J : ℝ := |J₀| + 1 with hJdef
  have hJ : 0 < J := by positivity
  set D : ℝ := L * (2 * ρ) with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨ρ, J * (16 * D ^ 2 * L ^ 2), hρ, by positivity,
    fun x hx => hball (lt_trans (mem_ball.mp hx) (by rw [hρdef]; linarith)), fun s hs hsρ => ?_⟩
  set S : Set Covector := T ∩ {y | |y 2| < L * s ∧ |y 3| < L * s} with hSdef
  have hSm : MeasurableSet S := by
    refine hTc.measurableSet.inter ?_
    exact ((isOpen_lt (continuous_apply (2 : Fin 4)).abs continuous_const).inter
      (isOpen_lt (continuous_apply (3 : Fin 4)).abs continuous_const)).measurableSet
  have hsubset : {x | ∃ w ∈ ball z ρ, (e w) 2 = 0 ∧ (e w) 3 = 0 ∧ dist x w < s} ⊆
      e.symm '' S := by
    rintro x ⟨w, hw, hw2, hw3, hxw⟩
    have hwC : w ∈ C := mem_closedBall.mpr ((mem_ball.mp hw).le.trans (by linarith))
    have hxC : x ∈ C := by
      refine mem_closedBall.mpr ?_
      have := dist_triangle x w z
      have := mem_ball.mp hw
      linarith
    have hnorm : ‖e x - e w‖ < L * s := by
      refine lt_of_le_of_lt (hlip w hwC x hxC) ?_
      rw [← dist_eq_norm]
      exact mul_lt_mul_of_pos_left hxw hL
    have hcomp (i : Fin 4) (hwi : (e w) i = 0) : |(e x) i| < L * s := by
      have h1 := norm_le_pi_norm (e x - e w) i
      rw [Pi.sub_apply, hwi, sub_zero, Real.norm_eq_abs] at h1
      exact lt_of_le_of_lt h1 hnorm
    exact ⟨e x, ⟨⟨x, hxC, rfl⟩, hcomp 2 hw2, hcomp 3 hw3⟩, e.left_inv (hCsub hxC)⟩
  have hSbox : S ⊆ box (e z) D (L * s) := by
    rintro y ⟨⟨x, hx, rfl⟩, hy2, hy3⟩ i _
    by_cases hi' : i = 2 ∨ i = 3
    · simp only [hi', ite_true]
      rcases hi' with rfl | rfl
      · exact abs_lt.mp hy2
      · exact abs_lt.mp hy3
    · simp only [hi', ite_false]
      have hzC : z ∈ C := mem_closedBall_self (by positivity)
      have h1 := (norm_le_pi_norm (e x - e z) i).trans (hlip z hzC x hx)
      have h2 : ‖x - z‖ ≤ 2 * ρ := by
        rw [← dist_eq_norm]
        exact mem_closedBall.mp hx
      rw [Pi.sub_apply, Real.norm_eq_abs] at h1
      have h3 : |(e x) i - (e z) i| ≤ D := h1.trans (mul_le_mul_of_nonneg_left h2 hL.le)
      exact ⟨by linarith [(abs_le.mp h3).1], by linarith [(abs_le.mp h3).2]⟩
  have himage : volume (e.symm '' S) ≤ ∫⁻ y in S, ENNReal.ofReal |(fderiv ℝ e.symm y).det| :=
    addHaar_image_le_lintegral_abs_det_fderiv volume hSm fun y hy =>
      ((hi.contDiffAt (e.open_target.mem_nhds (hTsub hy.1))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt
  calc volume {x | ∃ w ∈ ball z ρ, (e w) 2 = 0 ∧ (e w) 3 = 0 ∧ dist x w < s}
      ≤ volume (e.symm '' S) := measure_mono hsubset
    _ ≤ ∫⁻ y in S, ENNReal.ofReal |(fderiv ℝ e.symm y).det| := himage
    _ ≤ ∫⁻ _ in S, ENNReal.ofReal J := by
        refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
        have := hJ₀ y hy.1
        rw [Real.norm_eq_abs] at this
        exact this.trans ((le_abs_self J₀).trans (by linarith))
    _ = ENNReal.ofReal J * volume S := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal J * volume (box (e z) D (L * s)) := by
        gcongr
    _ = ENNReal.ofReal (J * (16 * D ^ 2 * L ^ 2) * s ^ 2) := by
        rw [volume_box (e z) hD (by positivity), ← ENNReal.ofReal_mul hJ.le]
        congr 1
        ring

variable {N V K : Set Covector}

/-- The part of a compact subset of the domain within coordinate distance `s`
of a locally flat nodal set has volume at most a constant times `s²`. -/
theorem exists_tube_bound (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ A s₀ : ℝ, 0 ≤ A ∧ 0 < s₀ ∧ ∀ s, 0 < s → s ≤ s₀ →
      volume (K ∩ thickening s N) ≤ ENNReal.ofReal (A * s ^ 2) := by
  classical
  obtain ⟨η, hη, hηV⟩ := hK.exists_cthickening_subset_open h.isOpen hKV
  set K₁ : Set Covector := cthickening η K with hK₁def
  have hK₁ : IsCompact K₁ := hK.cthickening
  set N₁ : Set Covector := K₁ \ (V \ N) with hN₁def
  have hN₁c : IsCompact N₁ := hK₁.diff h.isOpen_diff
  have hN₁N : ∀ w ∈ N₁, w ∈ N ∩ V := fun w hw =>
    ⟨by_contra fun hn => hw.2 ⟨hηV hw.1, hn⟩, hηV hw.1⟩
  have hloc : ∀ w ∈ N₁, ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧ ∀ s, 0 < s → s ≤ ρ →
      volume {x | ∃ w' ∈ ball w ρ ∩ N, dist x w' < s} ≤ ENNReal.ofReal (B * s ^ 2) := by
    intro w hw
    obtain ⟨e, hwe, he, hi, haxis⟩ := h.adapted w (hN₁N w hw)
    obtain ⟨ρ, B, hρ, hB, hsub, hb⟩ := exists_local_tube_bound e he hi hwe
    refine ⟨ρ, B, hρ, hB, fun s hs hsρ => (measure_mono ?_).trans (hb s hs hsρ)⟩
    rintro x ⟨w', ⟨hw'b, hw'N⟩, hd⟩
    have hsrc : w' ∈ e.source := hsub (ball_subset_ball (by linarith) hw'b)
    exact ⟨w', hw'b, ((haxis w' hsrc).mp hw'N).1, ((haxis w' hsrc).mp hw'N).2, hd⟩
  choose! ρ B hρ hB hb using hloc
  obtain ⟨t, htN, hcover⟩ := hN₁c.elim_nhds_subcover (fun w => ball w (ρ w))
    (fun w hw => ball_mem_nhds w (hρ w hw))
  obtain ⟨s₂, hs₂, hs₂le⟩ : ∃ s₂ : ℝ, 0 < s₂ ∧ ∀ w ∈ t, s₂ ≤ ρ w := by
    by_cases ht : t.Nonempty
    · exact ⟨t.inf' ht ρ, (Finset.lt_inf'_iff ht).mpr fun w hw => hρ w (htN w hw),
        fun w hw => Finset.inf'_le ρ hw⟩
    · exact ⟨1, one_pos, fun w hw => (ht ⟨w, hw⟩).elim⟩
  refine ⟨∑ w ∈ t, B w, min η s₂, Finset.sum_nonneg fun w hw => hB w (htN w hw),
    lt_min hη hs₂, fun s hs hsle => ?_⟩
  have hsub : K ∩ thickening s N ⊆
      ⋃ w ∈ t, {x | ∃ w' ∈ ball w (ρ w) ∩ N, dist x w' < s} := by
    rintro x ⟨hxK, hxN⟩
    obtain ⟨w', hw'N, hd⟩ := mem_thickening_iff.mp hxN
    have hw'K₁ : w' ∈ K₁ := mem_cthickening_of_dist_le w' x η K hxK
      (by rw [dist_comm]; exact hd.le.trans (hsle.trans (min_le_left _ _)))
    have hw'N₁ : w' ∈ N₁ := ⟨hw'K₁, fun hn => hn.2 hw'N⟩
    obtain ⟨w, hwt, hw'⟩ := mem_iUnion₂.mp (hcover hw'N₁)
    exact mem_iUnion₂.mpr ⟨w, hwt, w', ⟨hw', hw'N⟩, hd⟩
  calc volume (K ∩ thickening s N)
      ≤ volume (⋃ w ∈ t, {x | ∃ w' ∈ ball w (ρ w) ∩ N, dist x w' < s}) := measure_mono hsub
    _ ≤ ∑ w ∈ t, volume {x | ∃ w' ∈ ball w (ρ w) ∩ N, dist x w' < s} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ t, ENNReal.ofReal (B w * s ^ 2) :=
        Finset.sum_le_sum fun w hw => hb w (htN w hw) s hs
          (hsle.trans ((min_le_right _ _).trans (hs₂le w hw)))
    _ = ENNReal.ofReal ((∑ w ∈ t, B w) * s ^ 2) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun w hw =>
          mul_nonneg (hB w (htN w hw)) (sq_nonneg s)]

end FoliationQM.LocallyFlatTubeVolume
