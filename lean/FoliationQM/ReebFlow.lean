module

public import FoliationQM.ContactReeb
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual affine Reeb curves and proper-time reparameterization

Sources: v13 `thm:contact_period` and its clock conversion used by
`thm:clock_sideband`. Momentum coordinates are lowered and position velocities
are raised with the explicit Minkowski signature. The constant-momentum
curves below are actual integral curves. Their action/proper-time conversion
is derived; periodic compactification remains a separate stipulated input.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ReebFlow

open ContactReeb

/-- The raised proper velocity associated with massive shell momentum. -/
def properVelocity (m : ℝ) (p : Covector) : Covector := m⁻¹ • sharp p

/-- The constant-momentum proper-time curve in flat phase space. -/
def properLine (m : ℝ) (z : Ambient) (τ : ℝ) : Ambient :=
  (z.1 + τ • properVelocity m z.2, z.2)

/-- The actual affine curve parameterized by the source Reeb action coordinate. -/
def actionLine (m c : ℝ) (z : Ambient) (s : ℝ) : Ambient :=
  (z.1 + s • (reeb m c z.2).1, z.2)

/-- Raising and dividing shell momentum gives Minkowski square c squared. -/
theorem properVelocity_normalized {m c : ℝ} (hm : 0 < m) {p : Covector}
    (hs : OnShell m c p) : minkowski (properVelocity m p) (properVelocity m p) = c ^ 2 := by
  have he := hs.1
  simp only [minkowski] at he
  simp [properVelocity, sharp, minkowski]
  field_simp [hm.ne']
  nlinarith [he]

/-- Positive-energy massive momentum gives a future-directed proper velocity. -/
theorem properVelocity_future {m c : ℝ} (hm : 0 < m) {p : Covector}
    (hs : OnShell m c p) : 0 < properVelocity m p 0 := by
  simp only [properVelocity, Pi.smul_apply, smul_eq_mul, sharp]
  exact mul_pos (inv_pos.mpr hm) hs.2

/-- The Reeb position field has the source negative action/proper-time rate. -/
theorem reeb_eq_scaled_properVelocity {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (p : Covector) : (reeb m c p).1 = -(m * c ^ 2)⁻¹ • properVelocity m p := by
  funext i
  simp only [reeb, properVelocity, Pi.smul_apply, smul_eq_mul]
  field_simp [hm.ne', hc.ne']

/-- The actual proper-time curve starts at its supplied phase-space point. -/
theorem properLine_zero (m : ℝ) (z : Ambient) : properLine m z 0 = z := by
  simp [properLine]

/-- The actual Reeb action curve starts at its supplied phase-space point. -/
theorem actionLine_zero (m c : ℝ) (z : Ambient) : actionLine m c z 0 = z := by
  simp [actionLine]

/-- Proper-time translations compose by addition along the constant-momentum curve. -/
theorem properLine_add (m : ℝ) (z : Ambient) (s t : ℝ) :
    properLine m (properLine m z s) t = properLine m z (s + t) := by
  simp [properLine, add_smul, add_assoc]

/-- The actual Reeb action translations likewise form an additive flow. -/
theorem actionLine_add (m c : ℝ) (z : Ambient) (s t : ℝ) :
    actionLine m c (actionLine m c z s) t = actionLine m c z (s + t) := by
  simp [actionLine, add_smul, add_assoc]

/-- Proper-time flow preserves the actual fixed positive-energy shell. -/
theorem properLine_onShell {m c : ℝ} {z : Ambient} (hs : OnShell m c z.2) (τ : ℝ) :
    OnShell m c (properLine m z τ).2 := hs

/-- Reeb action flow preserves the same fixed shell. -/
theorem actionLine_onShell {m c : ℝ} {z : Ambient} (hs : OnShell m c z.2) (s : ℝ) :
    OnShell m c (actionLine m c z s).2 := hs

/-- The actual derivative of the proper-time curve is its raised velocity
and zero momentum velocity. -/
theorem hasDerivAt_properLine (m : ℝ) (z : Ambient) (τ : ℝ) :
    HasDerivAt (properLine m z) (properVelocity m z.2, 0) τ := by
  have h : HasDerivAt (fun t => z.1 + t • properVelocity m z.2) (properVelocity m z.2) τ := by
    simpa only [one_smul] using!
      HasDerivAt.const_add z.1 ((hasDerivAt_id τ).smul_const (properVelocity m z.2))
  exact HasDerivAt.prodMk h (hasDerivAt_const τ z.2)

/-- The actual action-parameter derivative is the source Reeb field at every point. -/
theorem hasDerivAt_actionLine (m c : ℝ) (z : Ambient) (s : ℝ) :
    HasDerivAt (actionLine m c z) (reeb m c (actionLine m c z s).2) s := by
  have h : HasDerivAt (fun t => z.1 + t • (reeb m c z.2).1) (reeb m c z.2).1 s := by
    simpa only [one_smul] using!
      HasDerivAt.const_add z.1 ((hasDerivAt_id s).smul_const (reeb m c z.2).1)
  exact HasDerivAt.prodMk h (hasDerivAt_const s z.2)

/-- The proper-time curve is smooth as an actual real-parameter map. -/
theorem contDiff_properLine (m : ℝ) (z : Ambient) : ContDiff ℝ ⊤ (properLine m z) := by
  unfold properLine
  fun_prop

/-- The actual Reeb action curve is smooth. -/
theorem contDiff_actionLine (m c : ℝ) (z : Ambient) : ContDiff ℝ ⊤ (actionLine m c z) := by
  unfold actionLine
  fun_prop

/-- The explicit reparameterization s=-mc²τ identifies the two actual curves. -/
theorem actionLine_reparam {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (z : Ambient) (τ : ℝ) : actionLine m c z (-m * c ^ 2 * τ) = properLine m z τ := by
  apply Prod.ext
  · funext i
    simp [actionLine, properLine, properVelocity, reeb]
    field_simp [hm.ne', hc.ne']
  · rfl

/-- Along the action curve the actual Liouville pullback evaluates to one. -/
theorem alpha_actionLine_deriv {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    {z : Ambient} (hs : OnShell m c z.2) (s : ℝ) :
    alpha (actionLine m c z s) (deriv (actionLine m c z) s) = 1 := by
  rw [(hasDerivAt_actionLine m c z s).deriv]
  exact alpha_reeb_eq_one hm hc (actionLine_onShell hs s)

/-- Along proper time the actual Liouville derivative is minus the rest energy. -/
theorem alpha_properLine_deriv {m c : ℝ} (hm : 0 < m)
    {z : Ambient} (hs : OnShell m c z.2) (τ : ℝ) :
    alpha (properLine m z τ) (deriv (properLine m z) τ) = -(m * c ^ 2) := by
  rw [(hasDerivAt_properLine m z τ).deriv]
  change -pairing z.2 (m⁻¹ • sharp z.2) = _
  rw [pairing_smul_right, pairing_sharp_right, hs.1]
  field_simp [hm.ne']

/-- The source action/proper-time scalar change has its actual constant derivative. -/
theorem hasDerivAt_action_parameter (m c τ : ℝ) :
    HasDerivAt (fun t : ℝ => -m * c ^ 2 * t) (-m * c ^ 2) τ := by
  simpa only [mul_one] using! (hasDerivAt_id τ).const_mul (-m * c ^ 2)

end FoliationQM.ReebFlow
