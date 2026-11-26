module

public import FoliationQM.Conventions
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual physical-time derivatives after restoring the rest phase

Source: v13 `cor:schrodinger`, component kinds C and D. The carrier is the
actual complex exponential with physical-time frequency m c² / hbar. Its
product with a complex envelope is differentiated as a genuine function.
The second derivative uses the first-derivative formula on a neighborhood,
not merely an equality of jets at the point under consideration.

No Klein–Gordon equation, remainder estimate, or limiting equation is assumed
or asserted here. Coordinate conversion and rest-mass cancellation are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestPhaseDerivatives
open Filter
open scoped Topology

/-- The actual rest-energy carrier exp(-i omega0 t), with time measured in seconds. -/
def carrier (p : MassiveParameters) (t : ℝ) : ℂ :=
  phase (-p.omega0 * t)

/-- Restoring the same physical rest phase to an actual complex time curve. -/
def dressed (p : MassiveParameters) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  carrier p t * u t

/-- The rest carrier has unit modulus at every physical time. -/
theorem norm_carrier (p : MassiveParameters) (t : ℝ) : ‖carrier p t‖ = 1 := by
  simp only [carrier, phase, Complex.norm_exp_ofReal_mul_I]

/-- The actual rest carrier never vanishes, including when the envelope has a node. -/
theorem carrier_ne_zero (p : MassiveParameters) (t : ℝ) : carrier p t ≠ 0 :=
  Complex.exp_ne_zero _

/-- Actual exponential differentiation gives the negative imaginary rest frequency. -/
theorem hasDerivAt_carrier (p : MassiveParameters) (t : ℝ) :
    HasDerivAt (carrier p)
      ((-Complex.I * (p.omega0 : ℂ)) * carrier p t) t := by
  have hθ : HasDerivAt (fun s : ℝ => -p.omega0 * s) (-p.omega0) t := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id t).const_mul (-p.omega0)
  have he : HasDerivAt (carrier p)
      (carrier p t * (((-p.omega0 : ℝ) : ℂ) * Complex.I)) t := by
    simpa only [carrier, phase] using! (hθ.ofReal_comp.mul_const Complex.I).cexp
  exact he.congr_deriv (by push_cast; ring)

/-- Differentiating the actual carrier-envelope product retains its genuine envelope derivative. -/
theorem hasDerivAt_dressed (p : MassiveParameters) {u : ℝ → ℂ} {u' : ℂ} {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (dressed p u)
      (carrier p t * (u' - Complex.I * (p.omega0 : ℂ) * u t)) t := by
  change HasDerivAt (fun s => carrier p s * u s) _ t
  exact ((hasDerivAt_carrier p t).mul hu).congr_deriv (by ring)

/-- Neighborhood differentiability of the envelope and differentiability of its derivative
give the actual second derivative of the rest-dressed curve. -/
theorem second_deriv_dressed (p : MassiveParameters) {u : ℝ → ℂ} {t : ℝ}
    (hu : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ u s)
    (hu' : DifferentiableAt ℝ (deriv u) t) :
    deriv (deriv (dressed p u)) t = carrier p t *
      (deriv (deriv u) t - 2 * Complex.I * (p.omega0 : ℂ) * deriv u t -
        (p.omega0 : ℂ) ^ 2 * u t) := by
  have he : deriv (dressed p u) =ᶠ[𝓝 t]
      (fun s => carrier p s * (deriv u s - Complex.I * (p.omega0 : ℂ) * u s)) := by
    filter_upwards [hu] with s hs
    exact (hasDerivAt_dressed p hs.hasDerivAt).deriv
  have hd := (hasDerivAt_carrier p t).mul
    (hu'.hasDerivAt.sub (hu.self_of_nhds.hasDerivAt.const_mul
      (Complex.I * (p.omega0 : ℂ))))
  have hvalue : (-Complex.I * (p.omega0 : ℂ) * carrier p t) *
        (deriv u t - Complex.I * (p.omega0 : ℂ) * u t) +
      carrier p t * (deriv (deriv u) t - Complex.I * (p.omega0 : ℂ) * deriv u t) =
      carrier p t * (deriv (deriv u) t - 2 * Complex.I * (p.omega0 : ℂ) * deriv u t -
        (p.omega0 : ℂ) ^ 2 * u t) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  exact ((hd.congr_deriv hvalue).congr_of_eventuallyEq he).deriv

end FoliationQM.RestPhaseDerivatives
