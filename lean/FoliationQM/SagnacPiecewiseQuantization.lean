module

public import FoliationQM.SagnacQuantization

/-!
# Quantization of the clock circulation along piecewise contours

Source: v13 `thm:wallstrom` Part(a) and `eq:sagnac_quant`, "for every closed
contour `C ⊂ Ω`", and the parenthetical remark that "the physical proper-time
circulation is weighted by `m / M_eff(x)` ... coinciding with `-n T₀` when
`M_eff = m`", component kinds B and C. A contour made of finitely many
differentiable pieces, each ending where the next begins, transports a phase
with the clock differential relation by the exponential of the sum of the
circulations of the pieces. If the contour is closed and the phase does not
vanish at its base point, that sum is an integer multiple of `T₀ = 2π/ω`, and
the action circulation is an integer multiple of `2πħ`. If the clock form is
`(M_eff/m)` times a second form, the circulation of the second form is the
circulation of the clock form weighted by `m/M_eff`, and the two agree along
a curve on which `M_eff = m`.

The single-valued phase is a hypothesis, as in the source. Each piece is a
differentiable map of the real line used on the unit interval, and the
differential relation is used along each whole piece. Each piece may carry
its own coordinate expression of the phase and of the clock form, with the
phase values matched at the joints; this is the form a contour through
several charts of a manifold takes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SagnacPiecewiseQuantization

open MeasureTheory Set NodalPolarConverse SagnacQuantization
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : E → ℂ}
  {α : E → E →L[ℝ] ℝ} {w : ℝ}

/-- A real number whose phase factor at frequency `w` is trivial is an
integer multiple of the period `2π/w`. -/
theorem multiple_of_period (hw : w ≠ 0) {c : ℝ}
    (hexp : Complex.exp (-Complex.I * w * (c : ℂ)) = 1) :
    ∃ n : ℤ, c = -(n : ℝ) * (2 * Real.pi / w) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (-(w : ℂ) * (c : ℂ) - n * (2 * Real.pi)) * Complex.I = 0 := by
    linear_combination hn
  have hreal : -(w : ℂ) * (c : ℂ) = n * (2 * Real.pi) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero)
  have hr : -w * c = n * (2 * Real.pi) := by exact_mod_cast hreal
  field_simp
  linarith

variable {qs : ℕ → E → ℂ} {αs : ℕ → E → E →L[ℝ] ℝ} {γ γ' : ℕ → ℝ → E} {Q : ℕ → ℂ} {N : ℕ}

/-- A phase with the clock differential relation is transported along a chain
of differentiable pieces by the exponential of the summed circulation. Each
piece may carry its own coordinate expression of the phase and of the clock
form; only the phase values at the joints are matched. -/
theorem phase_transport_chain
    (hγ : ∀ k < N, ∀ t, HasDerivAt (γ k) (γ' k t) t)
    (hq : ∀ k < N, ∀ t, HasFDerivAt (qs k)
      ((αs k (γ k t)).smulRight (-Complex.I * (w : ℂ) * qs k (γ k t))) (γ k t))
    (hα : ∀ k < N, Continuous fun t => αs k (γ k t) (γ' k t))
    (h0 : ∀ k < N, qs k (γ k 0) = Q k) (h1 : ∀ k < N, qs k (γ k 1) = Q (k + 1)) :
    ∀ M ≤ N, Q M = Q 0 * Complex.exp (-Complex.I * w *
      ((∑ k ∈ Finset.range M, circulation (αs k) (γ k) (γ' k) : ℝ) : ℂ)) := by
  intro M
  induction M with
  | zero =>
    intro _
    simp
  | succ M ih =>
    intro hM
    have hlt : M < N := hM
    have ht := phase_transport (hγ M hlt) (hq M hlt) (hα M hlt) 1
    rw [h1 M hlt, h0 M hlt, ih hlt.le] at ht
    rw [ht, Finset.sum_range_succ, mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [circulation]
    push_cast
    ring

/-- Sagnac–Wallstrom quantization along a closed piecewise-differentiable
contour: the summed circulation is an integer multiple of `2π/ω`. -/
theorem circulation_quantized (hw : w ≠ 0)
    (hγ : ∀ k < N, ∀ t, HasDerivAt (γ k) (γ' k t) t)
    (hq : ∀ k < N, ∀ t, HasFDerivAt (qs k)
      ((αs k (γ k t)).smulRight (-Complex.I * (w : ℂ) * qs k (γ k t))) (γ k t))
    (hα : ∀ k < N, Continuous fun t => αs k (γ k t) (γ' k t))
    (h0 : ∀ k < N, qs k (γ k 0) = Q k) (h1 : ∀ k < N, qs k (γ k 1) = Q (k + 1))
    (hclosed : Q N = Q 0) (hne : Q 0 ≠ 0) :
    ∃ n : ℤ, (∑ k ∈ Finset.range N, circulation (αs k) (γ k) (γ' k)) =
      -(n : ℝ) * (2 * Real.pi / w) := by
  have h := phase_transport_chain hγ hq hα h0 h1 N le_rfl
  rw [hclosed] at h
  have h' : Q 0 * 1 = Q 0 * Complex.exp (-Complex.I * w *
      ((∑ k ∈ Finset.range N, circulation (αs k) (γ k) (γ' k) : ℝ) : ℂ)) := by
    rw [mul_one]
    exact h
  exact multiple_of_period hw (mul_left_cancel₀ hne h').symm

/-- The Wallstrom circulation condition along a closed piecewise contour:
with `ω = mc²/ħ` and `dS = -mc² α`, the action circulation is an integer
multiple of `2πħ`. -/
theorem action_circulation_quantized (p : MassiveParameters)
    (hγ : ∀ k < N, ∀ t, HasDerivAt (γ k) (γ' k t) t)
    (hq : ∀ k < N, ∀ t, HasFDerivAt (qs k) ((αs k (γ k t)).smulRight
      (-Complex.I * ((p.m * p.c ^ 2 / p.hbar : ℝ) : ℂ) * qs k (γ k t))) (γ k t))
    (hα : ∀ k < N, Continuous fun t => αs k (γ k t) (γ' k t))
    (h0 : ∀ k < N, qs k (γ k 0) = Q k) (h1 : ∀ k < N, qs k (γ k 1) = Q (k + 1))
    (hclosed : Q N = Q 0) (hne : Q 0 ≠ 0) :
    ∃ n : ℤ, -(p.m * p.c ^ 2) * (∑ k ∈ Finset.range N, circulation (αs k) (γ k) (γ' k)) =
      2 * Real.pi * n * p.hbar := by
  have hm := p.m_pos
  have hc := p.c_pos
  have hh := p.hbar_pos
  have hw : p.m * p.c ^ 2 / p.hbar ≠ 0 := by positivity
  obtain ⟨n, hn⟩ := circulation_quantized hw hγ hq hα h0 h1 hclosed hne
  refine ⟨n, ?_⟩
  rw [hn]
  field_simp

/-- Quantization for one phase and one clock form on a single coordinate
domain, along a closed chain of pieces joined at the points `P k`. -/
theorem circulation_quantized_of_points {P : ℕ → E} (hw : w ≠ 0)
    (hγ : ∀ k < N, ∀ t, HasDerivAt (γ k) (γ' k t) t)
    (hq : ∀ k < N, ∀ t, HasFDerivAt q
      ((α (γ k t)).smulRight (-Complex.I * (w : ℂ) * q (γ k t))) (γ k t))
    (hα : ∀ k < N, Continuous fun t => α (γ k t) (γ' k t))
    (h0 : ∀ k < N, γ k 0 = P k) (h1 : ∀ k < N, γ k 1 = P (k + 1))
    (hclosed : P N = P 0) (hne : q (P 0) ≠ 0) :
    ∃ n : ℤ, (∑ k ∈ Finset.range N, circulation α (γ k) (γ' k)) =
      -(n : ℝ) * (2 * Real.pi / w) :=
  circulation_quantized (qs := fun _ => q) (αs := fun _ => α) (Q := fun k => q (P k)) hw hγ hq
    hα (fun k hk => by rw [h0 k hk]) (fun k hk => by rw [h1 k hk]) (by rw [hclosed]) hne

/-- If the clock form is `M_eff/m` times the proper form along a curve, the
proper circulation is the clock circulation weighted by `m/M_eff`. -/
theorem proper_circulation_weighted {β : E → E →L[ℝ] ℝ} {Meff : E → ℝ} {m : ℝ}
    {c c' : ℝ → E} (hm : m ≠ 0) (hM : ∀ t, Meff (c t) ≠ 0)
    (hβ : ∀ t, α (c t) = (Meff (c t) / m) • β (c t)) :
    circulation β c c' = ∫ t in (0 : ℝ)..1, m / Meff (c t) * α (c t) (c' t) := by
  simp only [circulation]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h := hM t
  simp only [hβ t, _root_.smul_apply, smul_eq_mul]
  field_simp

/-- On the fixed-mass shell `M_eff = m` the proper circulation coincides with
the clock circulation. -/
theorem proper_circulation_of_shell {β : E → E →L[ℝ] ℝ} {Meff : E → ℝ} {m : ℝ}
    {c c' : ℝ → E} (hm : m ≠ 0) (hshell : ∀ t, Meff (c t) = m)
    (hβ : ∀ t, α (c t) = (Meff (c t) / m) • β (c t)) :
    circulation β c c' = circulation α c c' := by
  rw [proper_circulation_weighted hm (fun t => by rw [hshell t]; exact hm) hβ]
  simp only [circulation]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hshell t, div_self hm, one_mul]

end FoliationQM.SagnacPiecewiseQuantization
