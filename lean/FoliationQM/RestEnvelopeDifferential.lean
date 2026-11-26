module

public import FoliationQM.RestPhaseDerivatives
public import FoliationQM.PolarRegularity

/-!
# Actual spacetime derivatives of the rest envelope

Source: v13 `cor:schrodinger`, component kinds C and D.
Here the zeroth coordinate is physical time.
The carrier is the actual rest exponential, and the envelope is an arbitrary
complex field, including fields with nodes. The second derivative follows
by differentiating the first derivative identity on a genuine neighborhood.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestEnvelopeDifferential

open Filter PolarSecondDifferential PolarRegularity
open scoped Topology ContDiff

/-- The physical rest carrier on spacetime with zeroth coordinate t. -/
def carrierField (p : MassiveParameters) (x : Covector) : ℂ :=
  RestPhaseDerivatives.carrier p (x 0)

/-- The actual spacetime field obtained by restoring the envelope's rest phase. -/
def dressedField (p : MassiveParameters) (u : Covector → ℂ) (x : Covector) : ℂ :=
  carrierField p x * u x

/-- The carrier is smooth as an actual spacetime function. -/
theorem contDiff_carrierField (p : MassiveParameters) : ContDiff ℝ ∞ (carrierField p) := by
  have ht : ContDiff ℝ ∞ (fun x : Covector => -p.omega0 * x 0) :=
    contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)
  exact ((Complex.ofRealCLM.contDiff.comp ht).mul contDiff_const).cexp

/-- The carrier is nonzero without any nonvanishing assumption on the envelope. -/
theorem carrierField_ne_zero (p : MassiveParameters) (x : Covector) : carrierField p x ≠ 0 :=
  RestPhaseDerivatives.carrier_ne_zero p (x 0)

/-- Restoring the smooth carrier preserves local C² regularity of the actual envelope. -/
theorem contDiffAt_dressedField (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) : ContDiffAt ℝ 2 (dressedField p u) x :=
  ((contDiff_carrierField p).of_le (by simp)).contDiffAt.mul hu

private theorem directionalDerivative_carrierField (p : MassiveParameters)
    (x v : Covector) : directionalDerivative (carrierField p) v x =
      -Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * carrierField p x := by
  have hd := (RestPhaseDerivatives.hasDerivAt_carrier p (x 0)).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt (carrierField p) _ x at hd
  change (fderiv ℝ (carrierField p) x) v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.proj_apply, Complex.real_smul, carrierField]
  ring

/-- The actual derivative in a constant direction includes only that direction's time component
in the carrier term; spatial directions therefore leave the carrier fixed. -/
theorem directionalDerivative_dressedField (p : MassiveParameters) {u : Covector → ℂ}
    {x : Covector} (hu : DifferentiableAt ℝ u x) (v : Covector) :
    directionalDerivative (dressedField p u) v x = carrierField p x *
      (directionalDerivative u v x - Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * u x) := by
  have he := (contDiff_carrierField p).differentiable (by simp) x
  have hd := he.hasFDerivAt.mul hu.hasFDerivAt
  change HasFDerivAt (dressedField p u) _ x at hd
  change (fderiv ℝ (dressedField p u) x) v = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change carrierField p x * directionalDerivative u v x +
    u x * directionalDerivative (carrierField p) v x = _
  rw [directionalDerivative_carrierField]
  ring

/-- Local C² regularity gives the true second derivative of the carrier-envelope product,
including its mixed time term and the negative squared rest frequency. -/
theorem secondDirectionalDerivative_dressedField (p : MassiveParameters)
    {u : Covector → ℂ} {x : Covector} (hu : ContDiffAt ℝ 2 u x) (v : Covector) :
    secondDirectionalDerivative (dressedField p u) v x = carrierField p x *
      (secondDirectionalDerivative u v x -
        2 * Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * directionalDerivative u v x -
        (p.omega0 : ℂ) ^ 2 * (v 0 : ℂ) ^ 2 * u x) := by
  have hnear := eventually_differentiableAt_of_contDiffAt_two hu
  have heq : directionalDerivative (dressedField p u) v =ᶠ[𝓝 x]
      (fun y => carrierField p y * (directionalDerivative u v y -
        Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * u y)) := by
    filter_upwards [hnear] with y hy
    exact directionalDerivative_dressedField p hy v
  have he := (contDiff_carrierField p).differentiable (by simp) x
  have hdu := differentiableAt_directionalDerivative_of_contDiffAt_two hu v
  have hd := he.hasFDerivAt.mul (hdu.hasFDerivAt.sub
    (hnear.self_of_nhds.hasFDerivAt.const_mul
      (Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ))))
  change HasFDerivAt (fun y => carrierField p y * (directionalDerivative u v y -
    Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * u y)) _ x at hd
  change (fderiv ℝ (directionalDerivative (dressedField p u) v) x) v = _
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  change carrierField p x * (secondDirectionalDerivative u v x -
      Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * directionalDerivative u v x) +
    (directionalDerivative u v x - Complex.I * (p.omega0 : ℂ) * (v 0 : ℂ) * u x) *
      directionalDerivative (carrierField p) v x = _
  rw [directionalDerivative_carrierField]
  ring_nf
  simp only [Complex.I_sq]
  ring

end FoliationQM.RestEnvelopeDifferential
