module

public import FoliationQM.MassShellForms

/-!
# Local nonexactness of the actual shell Liouville form

Source: v13 `thm:contact_period`, the distinction between the Liouville form
on the full seven-dimensional shell and its pullback to a Hamilton--Jacobi
section. The shell form has nonzero actual exterior derivative, even on the
positive-energy massless shell. Consequently it cannot equal the differential
of a C2 real potential on any open neighborhood. This does not obstruct exact
pullback to a lower-dimensional Hamilton--Jacobi section.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LiouvilleNonexact
open MassShellChart
open scoped Topology

/-- A scalar potential represented as an actual differential zero-form on shell coordinates. -/
def potentialZeroForm (F : Space → ℝ) (q : Space) : Space [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ Space (Fin 0) (F q)

/-- The actual exterior differential of a scalar potential on the shell coordinate space. -/
def potentialDifferential (F : Space → ℝ) (q : Space) : Space [⋀^Fin 1]→L[ℝ] ℝ :=
  extDeriv (potentialZeroForm F) q

/-- The potential differential evaluates as the actual Frechet derivative of the scalar potential. -/
theorem potentialDifferential_apply (F : Space → ℝ) (q : Space) (v : Fin 1 → Space) :
    potentialDifferential F q v = fderiv ℝ F q (v 0) := by
  change extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ Space (Fin 0) (F x)) q v = _
  rw [extDeriv_constOfIsEmpty]
  rfl

/-- A C2 scalar potential gives a C2 zero-form at the same point. -/
theorem contDiffAt_potentialZeroForm {F : Space → ℝ} {q : Space}
    (hF : ContDiffAt ℝ 2 F q) : ContDiffAt ℝ 2 (potentialZeroForm F) q := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ Space ℝ (Fin 0)).contDiff.contDiffAt.comp q hF

/-- The actual exterior derivative of a C2 potential's differential vanishes by d squared equals zero. -/
theorem extDeriv_potentialDifferential_zero {F : Space → ℝ} {q : Space}
    (hF : ContDiffAt ℝ 2 F q) : extDeriv (potentialDifferential F) q = 0 := by
  exact extDeriv_extDeriv_apply (contDiffAt_potentialZeroForm hF) (by simp)

/-- Near a positive-energy point, the actual shell Liouville form cannot be a C2 potential differential. -/
theorem not_eventuallyEq_potentialDifferential {m c : ℝ} {q : Space}
    (hE : 0 < energy m c q) {F : Space → ℝ} (hF : ContDiffAt ℝ 2 F q) :
    ¬ potentialDifferential F =ᶠ[𝓝 q] MassShellForms.pullback m c := by
  intro h
  have hd := h.extDeriv_eq
  rw [extDeriv_potentialDifferential_zero hF] at hd
  exact MassShellForms.extDeriv_pullback_ne_zero hE hd.symm

/-- No C2 potential has the shell Liouville differential on an open set containing a positive-energy point. -/
theorem not_eqOn_potentialDifferential {m c : ℝ} {q : Space}
    (hE : 0 < energy m c q) {U : Set Space} (hU : IsOpen U) (hq : q ∈ U)
    {F : Space → ℝ} (hF : ContDiffOn ℝ 2 F U) :
    ¬ Set.EqOn (potentialDifferential F) (MassShellForms.pullback m c) U := by
  intro h
  apply not_eventuallyEq_potentialDifferential hE (hF.contDiffAt (hU.mem_nhds hq))
  filter_upwards [hU.mem_nhds hq] with x hx
  exact h hx

/-- The scalar Frechet derivative cannot equal every shell Liouville pairing on such an open neighborhood. -/
theorem not_fderiv_eq_pullback_on {m c : ℝ} {q : Space}
    (hE : 0 < energy m c q) {U : Set Space} (hU : IsOpen U) (hq : q ∈ U)
    {F : Space → ℝ} (hF : ContDiffOn ℝ 2 F U) :
    ¬ ∀ x ∈ U, ∀ v : Space, fderiv ℝ F x v = MassShellForms.pullback m c x ![v] := by
  intro h
  apply not_eqOn_potentialDifferential hE hU hq hF
  intro x hx
  ext v
  rw [potentialDifferential_apply]
  have hv : ![v 0] = v := by
    ext i
    fin_cases i
    rfl
  simpa only [hv] using h x hx (v 0)

/-- In particular, no globally C2 potential differentiates to the shell Liouville form at all chart points. -/
theorem not_global_potential {m c : ℝ} {q : Space} (hE : 0 < energy m c q)
    (F : Space → ℝ) (hF : ContDiff ℝ 2 F) :
    ¬ potentialDifferential F = MassShellForms.pullback m c := by
  intro h
  apply not_eventuallyEq_potentialDifferential hE hF.contDiffAt
  exact Filter.EventuallyEq.of_eq h

end FoliationQM.LiouvilleNonexact
