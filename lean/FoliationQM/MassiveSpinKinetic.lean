module
public import FoliationQM.ReconstructedSpinFisher
public import FoliationQM.DiracFieldDensity

/-!
# The second-order kinetic density with the scalar mass term

The comparison of v13 `eq:spinor_quadratic_exact` with `eq:coupled_action`
uses the mass contribution of the scalar action. The Lorentzian kinetic
form is evaluated on the actual four derivatives of the original spinor.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace FoliationQM.MassiveSpinKinetic
open DiracMatrices DiracFieldDensity SpinorRegularity NeutralizedSpinorKinetic

/-- K₂ at the specified chiral angle with the mass term from the scalar action. -/
def density (p : MassiveParameters) (β : ℝ) (ψ : Covector → Spinor) (x : Covector) : ℝ :=
  fieldKineticRe p.hbar β ψ x coordinateDirections - invariantDensity (ψ x) * (p.m ^ 2 * p.c ^ 2)

/-- Restoring the mass contribution recovers precisely the original kinetic form. -/
theorem density_add_mass (p : MassiveParameters) (β : ℝ) (ψ : Covector → Spinor) (x : Covector) :
    density p β ψ x + invariantDensity (ψ x) * (p.m ^ 2 * p.c ^ 2) =
      fieldKineticRe p.hbar β ψ x coordinateDirections := sub_add_cancel _ _

/-- The value uses only the spinor germ at the point and the specified angle there. -/
theorem density_congr (p : MassiveParameters) (β : ℝ) {ψ φ : Covector → Spinor} {x : Covector}
    (he : ψ =ᶠ[𝓝 x] φ) : density p β ψ x = density p β φ x := by
  unfold density fieldKineticRe
  rw [ReconstructedSpinFisher.fieldKinetic_congr he, he.self_of_nhds]

/-- At positive invariant density the massive density is strictly smaller than K₂. -/
theorem density_lt_kinetic (p : MassiveParameters) (β : ℝ) {ψ : Covector → Spinor} {x : Covector}
    (hr : Regular (ψ x)) : density p β ψ x < fieldKineticRe p.hbar β ψ x coordinateDirections :=
  sub_lt_self _ (mul_pos hr (mul_pos (sq_pos_of_pos p.m_pos) (sq_pos_of_pos p.c_pos)))

end FoliationQM.MassiveSpinKinetic
