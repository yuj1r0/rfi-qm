module

public import FoliationQM.LatticeUnitaryPropagator
public import FoliationQM.LatticePolarVariation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness for the exact Neumann evolution

Transport a differentiable complex profile to a fixed reference time using
the same finite Neumann propagator. Its derivative is the transported
inhomogeneous term. For a homogeneous solution this proves uniqueness on
an open interval for arbitrary complex site data.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePropagatorUniqueness

open LatticeUnitaryPropagator Set

/-- Deducing the time derivative after transport requires no differentiability
of the forcing term. Its value at the differentiation time suffices. -/
theorem transported_derivative {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : ℝ → Space n) (b t : ℝ) (r : Space n)
    (hz : HasDerivAt z (generator p h V (z t) + r) t) :
    HasDerivAt (fun s => propagator p h V (b-s) (z s)) (propagator p h V (b-t) r) t := by
  let U := propagator p h V
  let G := generator p h V
  have ht : HasDerivAt (fun s : ℝ => b-s) (-1) t := (hasDerivAt_id t).const_sub b
  have hu : HasDerivAt (fun s => U (b-s)) (-(U (b-t) * G)) t := by
    simpa [U, G, Function.comp_def] using (propagator_deriv_right p h V (b-t)).scomp t ht
  let restrict := ContinuousLinearMap.restrictScalarsL ℂ (Space n) (Space n) ℝ ℝ
  have hur := restrict.hasFDerivAt.comp_hasDerivAt t hu
  have hd := hur.clm_apply hz
  apply hd.congr_deriv
  change -(U (b-t) (G (z t))) + U (b-t) (G (z t) + r) = U (b-t) r
  rw [map_add]
  abel

/-- Every solution of the homogeneous finite Schrödinger equation on an open
interval is obtained by transporting its value at any other time in that interval. -/
theorem homogeneous_unique {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : ℝ → Space n) {l u a b : ℝ} (ha : a ∈ Ioo l u) (hb : b ∈ Ioo l u)
    (hz : ∀ t ∈ Ioo l u, HasDerivAt z (generator p h V (z t)) t) :
    z b = propagator p h V (b-a) (z a) := by
  have hd (t : ℝ) (ht : t ∈ Ioo l u) :
      HasDerivAt (fun s => propagator p h V (b-s) (z s)) 0 t := by
    simpa only [map_zero] using transported_derivative p h V z b t 0 (by simpa using hz t ht)
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hb ha
  simpa only [sub_self, propagator_zero, one_apply_eq_self] using he

/-- Each mode of the frequency matrix with real eigenvalue λ acquires precisely
the phase exp(−itλ) used by the reference program in its eigenbasis. -/
theorem eigenmode {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (x : Space n) (eigenvalue : ℝ) (hx : ham p h V x = (eigenvalue : ℂ) • x) (t : ℝ) :
    propagator p h V t x = phase (-t * eigenvalue) • x := by
  let z (s : ℝ) := phase (-s * eigenvalue) • x
  have hz (s : ℝ) : HasDerivAt z (generator p h V (z s)) s := by
    have hc : HasDerivAt (fun u : ℝ => -u * eigenvalue) (-1 * eigenvalue) s :=
      (hasDerivAt_id s).neg.mul_const eigenvalue
    have hφ := LatticePolarVariation.phase_path hc
    have hd := hφ.smul_const x
    apply hd.congr_deriv
    simp only [generator, smul_apply, z, map_smul, hx, smul_smul]
    push_cast
    congr 1
    ring
  have h0 : z 0 = x := by simp [z, phase]
  have he := homogeneous_unique p h V z (l := min t 0 - 1) (u := max t 0 + 1)
    (a := 0) (b := t)
    ⟨by linarith [min_le_right t (0:ℝ)], by linarith [le_max_right t (0:ℝ)]⟩
    ⟨by linarith [min_le_left t (0:ℝ)], by linarith [le_max_left t (0:ℝ)]⟩ (fun s _ => hz s)
  simpa only [h0, sub_zero] using he.symm

end FoliationQM.LatticePropagatorUniqueness
