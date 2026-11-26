module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The inverse-square integral over shells from a quadratic tube bound

Source: v13 `eq:log_cutoff_l2_bound`, the step
"`(C/|ln ε|²) ∫_{ε²}^{ε} dr/r`" for a tubular neighbourhood whose
"codimension-2 tubular volume element is bounded by `C r dr dθ dvol_𝒩`",
component kind C. In measure form the tubular bound is
`μ(K ∩ {δ < s}) ≤ A s²` for a function `δ` and all small `s`. This module
proves, by a dyadic decomposition, that then

`∫_{K ∩ {a ≤ δ < 2ⁿ a}} δ⁻² dμ ≤ 4 A n`,

which is the logarithm `∫_a^{2ⁿ a} dr/r` up to a constant. If a second
function `r` satisfies `c δ ≤ r` on `K`, then

`∫_{K ∩ {a ≤ r ≤ b}} r⁻² dμ ≤ A + 4 A n / c²` whenever `b < c 2ⁿ a`.

Only the lower comparison `c δ ≤ r` is used. The integrals are lower Lebesgue
integrals, so no integrability is assumed. The tube bound itself and the
cutoff are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DyadicShellIntegral

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {δ r : α → ℝ}
  {A s₀ a b c : ℝ}

/-- One dyadic shell contributes at most `4 A`. -/
theorem lintegral_shell_le (hδ : Measurable δ) (hK : MeasurableSet K)
    (htube : ∀ s, 0 < s → s ≤ s₀ → μ (K ∩ {x | δ x < s}) ≤ ENNReal.ofReal (A * s ^ 2))
    (ha : 0 < a) (hs : 2 * a ≤ s₀) :
    ∫⁻ x in K ∩ {x | a ≤ δ x ∧ δ x < 2 * a}, ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ ≤
      ENNReal.ofReal (4 * A) := by
  have hm : MeasurableSet (K ∩ {x | a ≤ δ x ∧ δ x < 2 * a}) :=
    hK.inter ((measurableSet_le measurable_const hδ).inter (measurableSet_lt hδ measurable_const))
  calc ∫⁻ x in K ∩ {x | a ≤ δ x ∧ δ x < 2 * a}, ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ
      ≤ ∫⁻ _ in K ∩ {x | a ≤ δ x ∧ δ x < 2 * a}, ENNReal.ofReal (a⁻¹ ^ 2) ∂μ := by
        refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
        have h1 : (δ x)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hx.2.1
        have h2 : 0 ≤ (δ x)⁻¹ := inv_nonneg.mpr (ha.le.trans hx.2.1)
        exact pow_le_pow_left₀ h2 h1 2
    _ = ENNReal.ofReal (a⁻¹ ^ 2) * μ (K ∩ {x | a ≤ δ x ∧ δ x < 2 * a}) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (a⁻¹ ^ 2) * ENNReal.ofReal (A * (2 * a) ^ 2) := by
        gcongr
        have hsub : K ∩ {x | a ≤ δ x ∧ δ x < 2 * a} ⊆ K ∩ {x | δ x < 2 * a} :=
          fun x hx => ⟨hx.1, hx.2.2⟩
        exact (measure_mono hsub).trans (htube (2 * a) (by positivity) hs)
    _ = ENNReal.ofReal (4 * A) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- The inverse-square integral over `n` dyadic shells is at most `4 A n`. -/
theorem lintegral_dyadic_le (hδ : Measurable δ) (hK : MeasurableSet K)
    (htube : ∀ s, 0 < s → s ≤ s₀ → μ (K ∩ {x | δ x < s}) ≤ ENNReal.ofReal (A * s ^ 2))
    (hA : 0 ≤ A) (ha : 0 < a) (n : ℕ) (hs : 2 ^ n * a ≤ s₀) :
    ∫⁻ x in K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ n * a}, ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ ≤
      ENNReal.ofReal (4 * A * n) := by
  induction n with
  | zero =>
    have he : K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ 0 * a} = ∅ := by
      ext x
      simp only [pow_zero, one_mul, mem_inter_iff, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false,
        not_and, not_lt]
      exact fun _ h => h
    rw [he]
    simp
  | succ n ih =>
    have h2 : (2 : ℝ) ^ n * a ≤ 2 ^ (n + 1) * a := by
      rw [pow_succ]
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) n]
    have hsplit : K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ (n + 1) * a} ⊆
        (K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ n * a}) ∪
          (K ∩ {x | 2 ^ n * a ≤ δ x ∧ δ x < 2 * (2 ^ n * a)}) := by
      intro x hx
      by_cases hlt : δ x < 2 ^ n * a
      · exact Or.inl ⟨hx.1, hx.2.1, hlt⟩
      · refine Or.inr ⟨hx.1, not_lt.mp hlt, ?_⟩
        have := hx.2.2
        rw [pow_succ] at this
        linarith
    have hshell := lintegral_shell_le (a := 2 ^ n * a) hδ hK htube (by positivity)
      (by rw [pow_succ] at hs; linarith)
    calc ∫⁻ x in K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ (n + 1) * a}, ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ
        ≤ ∫⁻ x in (K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ n * a}) ∪
            (K ∩ {x | 2 ^ n * a ≤ δ x ∧ δ x < 2 * (2 ^ n * a)}),
            ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ := lintegral_mono_set hsplit
      _ ≤ ENNReal.ofReal (4 * A * n) + ENNReal.ofReal (4 * A) :=
          (lintegral_union_le _ _ _).trans (add_le_add (ih (h2.trans hs)) hshell)
      _ = ENNReal.ofReal (4 * A * (n + 1 : ℕ)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring

/-- The inverse-square integral of a function bounded below by a multiple of
`δ`, over the region where it lies between `a` and `b`. -/
theorem lintegral_between_le (hδ : Measurable δ) (hr : Measurable r) (hK : MeasurableSet K)
    (htube : ∀ s, 0 < s → s ≤ s₀ → μ (K ∩ {x | δ x < s}) ≤ ENNReal.ofReal (A * s ^ 2))
    (hA : 0 ≤ A) (hc : 0 < c) (hlow : ∀ x ∈ K, c * δ x ≤ r x) (ha : 0 < a) (n : ℕ)
    (hb : b < c * (2 ^ n * a)) (hs : 2 ^ n * a ≤ s₀) :
    ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b}, ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ ≤
      ENNReal.ofReal (A + 4 * A * n / c ^ 2) := by
  have ha0 : a ≤ s₀ := le_trans (by
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]) hs
  have hsplit : K ∩ {x | a ≤ r x ∧ r x ≤ b} ⊆
      (K ∩ {x | a ≤ r x} ∩ {x | δ x < a}) ∪
        (K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x}) := by
    intro x hx
    by_cases hlt : δ x < a
    · exact Or.inl ⟨⟨hx.1, hx.2.1⟩, hlt⟩
    · exact Or.inr ⟨hx, not_lt.mp hlt⟩
  have h1 : ∫⁻ x in K ∩ {x | a ≤ r x} ∩ {x | δ x < a}, ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ ≤
      ENNReal.ofReal A := by
    have hm : MeasurableSet (K ∩ {x | a ≤ r x} ∩ {x | δ x < a}) :=
      (hK.inter (measurableSet_le measurable_const hr)).inter
        (measurableSet_lt hδ measurable_const)
    calc ∫⁻ x in K ∩ {x | a ≤ r x} ∩ {x | δ x < a}, ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ
        ≤ ∫⁻ _ in K ∩ {x | a ≤ r x} ∩ {x | δ x < a}, ENNReal.ofReal (a⁻¹ ^ 2) ∂μ := by
          refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
          have h1 : (r x)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hx.1.2
          exact pow_le_pow_left₀ (inv_nonneg.mpr (ha.le.trans hx.1.2)) h1 2
      _ = ENNReal.ofReal (a⁻¹ ^ 2) * μ (K ∩ {x | a ≤ r x} ∩ {x | δ x < a}) := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (a⁻¹ ^ 2) * ENNReal.ofReal (A * a ^ 2) := by
          gcongr
          have hsub : K ∩ {x | a ≤ r x} ∩ {x | δ x < a} ⊆ K ∩ {x | δ x < a} :=
            fun x hx => ⟨hx.1.1, hx.2⟩
          exact (measure_mono hsub).trans (htube a ha ha0)
      _ = ENNReal.ofReal A := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have h2 : ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x},
      ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ ≤ ENNReal.ofReal (4 * A * n / c ^ 2) := by
    have hsub : K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x} ⊆
        K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ n * a} := by
      intro x hx
      refine ⟨hx.1.1, hx.2, ?_⟩
      have h3 := hlow x hx.1.1
      have h4 := hx.1.2.2
      by_contra hge
      have : c * (2 ^ n * a) ≤ c * δ x := mul_le_mul_of_nonneg_left (not_lt.mp hge) hc.le
      linarith
    have hmK : MeasurableSet (K ∩ {x | a ≤ δ x ∧ δ x < 2 ^ n * a}) :=
      hK.inter ((measurableSet_le measurable_const hδ).inter
        (measurableSet_lt hδ measurable_const))
    calc ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x}, ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ
        ≤ ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x},
            ENNReal.ofReal ((c ^ 2)⁻¹) * ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ := by
          refine setLIntegral_mono' ((hK.inter ((measurableSet_le measurable_const hr).inter
            (measurableSet_le hr measurable_const))).inter
              (measurableSet_le measurable_const hδ)) fun x hx => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hd : 0 < δ x := ha.trans_le hx.2
          have hrx : c * δ x ≤ r x := hlow x hx.1.1
          have hcd : 0 < c * δ x := mul_pos hc hd
          have h5 : (r x)⁻¹ ≤ (c * δ x)⁻¹ := inv_anti₀ hcd hrx
          have h6 : (r x)⁻¹ ^ 2 ≤ (c * δ x)⁻¹ ^ 2 :=
            pow_le_pow_left₀ (inv_nonneg.mpr (hcd.le.trans hrx)) h5 2
          calc (r x)⁻¹ ^ 2 ≤ (c * δ x)⁻¹ ^ 2 := h6
            _ = (c ^ 2)⁻¹ * (δ x)⁻¹ ^ 2 := by
                rw [mul_inv, mul_pow, inv_pow]
      _ = ENNReal.ofReal ((c ^ 2)⁻¹) * ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x},
            ENNReal.ofReal ((δ x)⁻¹ ^ 2) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((c ^ 2)⁻¹) * ENNReal.ofReal (4 * A * n) := by
          gcongr
          exact (lintegral_mono_set hsub).trans (lintegral_dyadic_le hδ hK htube hA ha n hs)
      _ = ENNReal.ofReal (4 * A * n / c ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  calc ∫⁻ x in K ∩ {x | a ≤ r x ∧ r x ≤ b}, ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ
      ≤ ∫⁻ x in (K ∩ {x | a ≤ r x} ∩ {x | δ x < a}) ∪
          (K ∩ {x | a ≤ r x ∧ r x ≤ b} ∩ {x | a ≤ δ x}), ENNReal.ofReal ((r x)⁻¹ ^ 2) ∂μ :=
        lintegral_mono_set hsplit
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal (4 * A * n / c ^ 2) :=
        (lintegral_union_le _ _ _).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal (A + 4 * A * n / c ^ 2) :=
        (ENNReal.ofReal_add hA (by positivity)).symm

end FoliationQM.DyadicShellIntegral
