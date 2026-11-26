module

public import FoliationQM.RestEnvelopeKG

/-!
# Exact rest-action factorization for supplied real phases

Source: v13 `cor:schrodinger`, component kinds A, C and D. The displayed
split of the real action and the rest-carrier split of the complex field
are equalities of actual functions. Physical coordinate zero is t; original
normal-coordinate density and action are both pulled through the same ct map.
Nodes are allowed. No real phase is constructed for an arbitrary complex wave,
and no temporal control is inferred from a first phase derivative.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestActionPhase

open ActionDensity RestEnvelopeDifferential RestEnvelopeKG LaboratoryCoordinates

/-- Splitting a supplied real action by the negative rest term restores exactly the same
physical carrier on the full complex field, including its nodes. -/
theorem actionField_rest_split (p : MassiveParameters) (ρ S_tilde : Covector → ℝ) :
    actionField p ρ (fun x => -p.m * p.c ^ 2 * x 0 + S_tilde x) =
      dressedField p (actionField p ρ S_tilde) := by
  funext x
  have hphase : (-p.m * p.c ^ 2 * x 0 + S_tilde x) / p.hbar =
      -p.omega0 * x 0 + S_tilde x / p.hbar := by
    unfold MassiveParameters.omega0
    ring
  change (Real.sqrt (ρ x) : ℂ) * phase ((-p.m * p.c ^ 2 * x 0 + S_tilde x) / p.hbar) =
    phase (-p.omega0 * x 0) * ((Real.sqrt (ρ x) : ℂ) * phase (S_tilde x / p.hbar))
  rw [hphase]
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- The actual original-field envelope has the same pulled density and the pulled real action
plus mc²t, as a whole-function identity without a positivity assumption. -/
theorem envelope_actionField (p : MassiveParameters) (ρ S : Covector → ℝ) :
    envelope p (actionField p ρ S) =
      actionField p (pullback p.c ρ)
        (fun x => pullback p.c S x + p.m * p.c ^ 2 * x 0) := by
  have hsplit := actionField_rest_split p (pullback p.c ρ)
    (fun x => pullback p.c S x + p.m * p.c ^ 2 * x 0)
  have hphase : (fun x => -p.m * p.c ^ 2 * x 0 +
      (pullback p.c S x + p.m * p.c ^ 2 * x 0)) = pullback p.c S := by
    funext x
    ring
  rw [hphase] at hsplit
  change pullback p.c (actionField p ρ S) =
    dressedField p (actionField p (pullback p.c ρ)
      (fun x => pullback p.c S x + p.m * p.c ^ 2 * x 0)) at hsplit
  funext x
  apply mul_left_cancel₀ (carrierField_ne_zero p x)
  change dressedField p (envelope p (actionField p ρ S)) x = _
  rw [dressedField_envelope]
  exact congrFun hsplit x

end FoliationQM.RestActionPhase
