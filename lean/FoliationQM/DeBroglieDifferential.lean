module

public import FoliationQM.HamiltonJacobiPullback
public import FoliationQM.LorentzCoordinates
public import FoliationQM.ActionClockCircle

/-!
# Actual local de Broglie phase differentials

Source: v13 `prop:debroglie` and `eq:phase_Phi`. A local real action phase S
is differentiated through the actual Frechet derivative and actual exterior
derivative. Its derivative-defined momentum gives the source laboratory
formula with positive spatial phase and negative positive-energy time phase.
The physical four-velocity specialization uses the actual square-root Lorentz
factor and explicit Minkowski signature.

The equal-time expression contains no explicit c squared: that cancellation
is derived from the actual momentum contraction. The remaining dependence on
c through gamma is retained. The quotient/unit-circle statements identify an
available local real lift with the adopted action-circle readout; they do not
assert a global real action lift across nontrivial winding.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.DeBroglieDifferential
open LorentzCoordinates

/-- The local real phase obtained by dividing the local action potential by the supplied action scale. -/
def phase (S : Covector → ℝ) (h : ℝ) (x : Covector) : ℝ := S x / h

/-- The actual exterior differential of the local scalar phase S/hbar. -/
def phaseForm (S : Covector → ℝ) (h : ℝ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  HamiltonJacobiPullback.phaseDifferential (phase S h) x

/-- Differentiating the actual scalar phase gives the action derivative divided by the fixed action scale. -/
theorem hasFDerivAt_phase {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (h : ℝ) :
    HasFDerivAt (phase S h) (h⁻¹ • fderiv ℝ S x) x := by
  simpa only [phase, div_eq_mul_inv, mul_comm] using! hS.hasFDerivAt.const_mul h⁻¹

/-- The actual Frechet derivative of the scalar phase is the scaled action derivative. -/
theorem fderiv_phase {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (h : ℝ) :
    fderiv ℝ (phase S h) x = h⁻¹ • fderiv ℝ S x := (hasFDerivAt_phase hS h).fderiv

/-- The genuine phase one-form evaluates as the actual action derivative divided by the action scale. -/
theorem phaseForm_apply {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (h : ℝ) (v : Fin 1 → Covector) :
    phaseForm S h x v = fderiv ℝ S x (v 0) / h := by
  rw [phaseForm, HamiltonJacobiPullback.phaseDifferential_apply, fderiv_phase hS]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual phase exterior differential is the scaled actual action exterior differential. -/
theorem phaseForm_eq_scaled {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (h : ℝ) :
    phaseForm S h x = h⁻¹ • HamiltonJacobiPullback.phaseDifferential S x := by
  ext v
  change phaseForm S h x v = h⁻¹ * HamiltonJacobiPullback.phaseDifferential S x v
  rw [phaseForm_apply hS, HamiltonJacobiPullback.phaseDifferential_apply]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual phase differential is minus the derivative-defined lower-momentum pairing divided by hbar. -/
theorem phaseForm_momentum {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (h : ℝ) (v : Fin 1 → Covector) :
    phaseForm S h x v = -(ContactReeb.pairing (HamiltonJacobiPullback.momentum S x) (v 0)) / h := by
  rw [phaseForm_apply hS, HamiltonJacobiPullback.momentum_pairing, neg_neg]

/-- The actual phase differential has the source laboratory spatial and time expression. -/
theorem phaseForm_laboratory {S : Covector → ℝ} {x : Covector} {m c h : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (dt : ℝ) (dx : Spatial) :
    phaseForm S h x ![displacement c dt dx] =
      (gamma c v*m*spatialDot v dx - gamma c v*m*c^2*dt)/h := by
  rw [phaseForm_momentum hS, hp, ContactReeb.pairing_smul_left,
    ContactReeb.pairing_sharp_left]
  change -(m*minkowski (fourVelocity c v) (displacement c dt dx))/h = _
  rw [velocity_displacement_contraction]
  ring

/-- The scalar Frechet derivative itself has the source laboratory de Broglie expression. -/
theorem fderiv_phase_laboratory {S : Covector → ℝ} {x : Covector} {m c h : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (dt : ℝ) (dx : Spatial) :
    fderiv ℝ (phase S h) x (displacement c dt dx) =
      (gamma c v*m*spatialDot v dx - gamma c v*m*c^2*dt)/h := by
  simpa only [phaseForm, HamiltonJacobiPullback.phaseDifferential_apply, Matrix.cons_val_zero]
    using phaseForm_laboratory (h := h) hS hp dt dx

/-- The actual equal-time phase differential has the exact c-squared cancellation and retains gamma. -/
theorem phaseForm_equal_time {S : Covector → ℝ} {x : Covector} {m c h : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (dx : Spatial) :
    phaseForm S h x ![displacement c 0 dx] = gamma c v*m*spatialDot v dx/h := by
  simpa using phaseForm_laboratory hS hp 0 dx

/-- The actual phase differential along the laboratory time direction has the negative positive-energy sign. -/
theorem phaseForm_time_axis {S : Covector → ℝ} {x : Covector} {m c h : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (dt : ℝ) :
    phaseForm S h x ![displacement c dt 0] = -gamma c v*m*c^2*dt/h := by
  rw [phaseForm_laboratory hS hp]
  simp [spatialDot]

/-- On the physical subluminal domain the actual equal-time phase shift is nonzero exactly in nonorthogonal spatial directions. -/
theorem phaseForm_equal_time_ne_zero_iff {S : Covector → ℝ} {x : Covector}
    {m c h : ℝ} {v : Spatial} (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (hm : 0 < m) (hc : 0 < c) (hh : 0 < h) (hv : speedSq v < c^2) (dx : Spatial) :
    phaseForm S h x ![displacement c 0 dx] ≠ 0 ↔ spatialDot v dx ≠ 0 := by
  rw [phaseForm_equal_time hS hp]
  simp [(gamma_pos hc hv).ne',hm.ne',hh.ne']

/-- Dividing a scalar action lift by a fixed scale preserves its local differentiability order. -/
theorem contDiffAt_phase {S : Covector → ℝ} {x : Covector} {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ n S x) (h : ℝ) : ContDiffAt ℝ n (phase S h) x :=
  hS.div_const h

/-- The actual local phase differential is closed under local C2 regularity. -/
theorem phaseForm_closed {S : Covector → ℝ} {x : Covector}
    (hS : ContDiffAt ℝ 2 S x) (h : ℝ) : extDeriv (phaseForm S h) x = 0 :=
  HamiltonJacobiPullback.extDeriv_phaseDifferential_zero (contDiffAt_phase hS h)

/-- The actual phase differential equals minus the Compton angular frequency times the exact phase-clock form. -/
theorem phaseForm_eq_clock {S : Covector → ℝ} {x : Covector}
    (hS : DifferentiableAt ℝ S x) (p : MassiveParameters) :
    phaseForm S p.hbar x = (-p.omega0) • HamiltonJacobiPullback.clockForm S p.m p.c x := by
  ext v
  change phaseForm S p.hbar x v = (-p.omega0) * HamiltonJacobiPullback.clockForm S p.m p.c x v
  rw [phaseForm_apply hS, HamiltonJacobiPullback.clockForm_apply]
  unfold MassiveParameters.omega0
  field_simp [p.m_pos.ne',p.c_pos.ne',p.hbar_pos.ne']

/-- Derivative-defined momentum equal to a physical boosted massive velocity places the section on the actual future shell. -/
theorem physical_section_onShell {S : Covector → ℝ} {x : Covector} {m c : ℝ} {v : Spatial}
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (hm : 0 < m) (hc : 0 < c) (hv : speedSq v < c^2) :
    ContactReeb.OnShell m c (HamiltonJacobiPullback.sectionMap S x).2 :=
  HamiltonJacobiPullback.sectionMap_onShell_of_velocity hm hp
    (fourVelocity_normalized hc hv) (fourVelocity_future hc hv)

/-- Along the actual laboratory worldline tangent the local phase has the proper-time frequency divided by gamma. -/
theorem phaseForm_worldline {S : Covector → ℝ} {x : Covector} {m c h : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (hc : 0 < c) (hv : speedSq v < c^2) (dt : ℝ) :
    phaseForm S h x ![displacement c dt (dt • v)] = -m*c^2*dt/(gamma c v*h) := by
  rw [phaseForm_momentum hS, hp, ContactReeb.pairing_smul_left,
    ContactReeb.pairing_sharp_left]
  change -(m*minkowski (fourVelocity c v) (displacement c dt (dt • v)))/h = _
  have ht := properTime_worldline hc hv dt
  unfold properTime at ht
  have he := (div_eq_iff (pow_ne_zero _ hc.ne')).mp ht
  rw [he]
  ring

/-- The actual phase decreases along every forward physical worldline tangent. -/
theorem phaseForm_worldline_neg {S : Covector → ℝ} {x : Covector} {m c h dt : ℝ} {v : Spatial}
    (hS : DifferentiableAt ℝ S x)
    (hp : HamiltonJacobiPullback.momentum S x = m • ContactReeb.sharp (fourVelocity c v))
    (hm : 0 < m) (hc : 0 < c) (hh : 0 < h) (hv : speedSq v < c^2) (hdt : 0 < dt) :
    phaseForm S h x ![displacement c dt (dt • v)] < 0 := by
  rw [phaseForm_worldline hS hp hc hv]
  have hg := gamma_pos hc hv
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hm) (sq_pos_of_pos hc)) hdt)
    (mul_pos hg hh)

/-- The unit-circle phase supplied by an available local real action lift. -/
def unitPhase (S : Covector → ℝ) (h : ℝ) (x : Covector) : Circle := Circle.exp (phase S h x)

/-- The adopted action-circle phase map agrees with the local real phase modulo two pi. -/
theorem actionToPhase_local_lift (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) :
    ActionClockCircle.actionToPhase p (S x : ActionClockCircle.ActionCircle p) =
      (phase S p.hbar x : AddCircle (2*Real.pi)) :=
  ActionClockCircle.actionToPhase_coe p (S x)

/-- The adopted action quotient gives exactly the unit-circle phase of the available local real action lift. -/
theorem actionToUnitCircle_local_lift (p : MassiveParameters) (S : Covector → ℝ) (x : Covector) :
    ActionClockCircle.actionToUnitCircle p (S x : ActionClockCircle.ActionCircle p) =
      unitPhase S p.hbar x :=
  ActionClockCircle.actionToUnitCircle_coe p (S x)

end FoliationQM.DeBroglieDifferential
