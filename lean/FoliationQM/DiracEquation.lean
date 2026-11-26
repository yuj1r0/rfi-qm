module

public import FoliationQM.DiracFieldDensity
public import FoliationQM.RealLorentzFrame

/-!
# The actual flat-coordinate Dirac equation

Source: v13 `eq:dirac` and the flat-space operator product preceding
`eq:spinor_quadratic_exact`. The finite jet and genuine field operators use
the concrete gamma matrices and the actual coordinate directions. Their
normalization is i hbar gamma^mu partial_mu minus m c. The opposite factor
has minus i hbar with the same mass term. The d'Alembertian is the actual
signed sum of second coordinate derivatives, not supplied Hessian data.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracEquation
open DiracMatrices RealLorentzFrame DiracFieldDensity

/-- The actual gamma contraction of four spinor jet directions. -/
def slashJet (jet : Fin 4 → Spinor) : Spinor := ∑ mu, (gamma mu).mulVec (jet mu)

/-- The flat Dirac first-jet equation with the source i-hbar and mass-times-c coefficients. -/
def jetEquation (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) : Prop :=
  (Complex.I*(hbar : ℂ)) • slashJet jet = ((m*c : ℝ) : ℂ) • psi

/-- The actual first-jet Dirac residual. -/
def diracJet (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) : Spinor :=
  (Complex.I*(hbar : ℂ)) • slashJet jet - ((m*c : ℝ) : ℂ) • psi

/-- The actual flat gamma contraction of the spinor field's real Frechet derivative on the four coordinate directions. -/
def slashField (psi : Covector → Spinor) (x : Covector) : Spinor :=
  slashJet (fun mu => fderiv ℝ psi x (coordinateDirections mu))

/-- The actual flat-coordinate Dirac field residual with the source normalization. -/
def diracField (hbar m c : ℝ) (psi : Covector → Spinor) (x : Covector) : Spinor :=
  diracJet hbar m c (psi x) (fun mu => fderiv ℝ psi x (coordinateDirections mu))

/-- The actual opposite first-order factor, with negative i-hbar and the same negative mass term. -/
def oppositeDiracField (hbar m c : ℝ) (psi : Covector → Spinor) (x : Covector) : Spinor :=
  (-Complex.I*(hbar : ℂ)) • slashField psi x - ((m*c : ℝ) : ℂ) • psi x

/-- The actual flat d'Alembertian is the diagonal Minkowski contraction of the genuine second coordinate derivatives. -/
def boxField (psi : Covector → Spinor) (x : Covector) : Spinor :=
  ∑ mu, (sign mu : ℂ) •
    fderiv ℝ (fun y => fderiv ℝ psi y (coordinateDirections mu)) x (coordinateDirections mu)

/-- Vanishing of the actual first-jet residual is equivalent to the shared Dirac jet equation. -/
theorem diracJet_eq_zero_iff (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    diracJet hbar m c psi jet = 0 ↔ jetEquation hbar m c psi jet := sub_eq_zero

/-- Vanishing of the genuine field residual is exactly the shared equation on the actual coordinate derivative jet. -/
theorem diracField_eq_zero_iff (hbar m c : ℝ) (psi : Covector → Spinor) (x : Covector) :
    diracField hbar m c psi x = 0 ↔
      jetEquation hbar m c (psi x) (fun mu => fderiv ℝ psi x (coordinateDirections mu)) :=
  diracJet_eq_zero_iff hbar m c _ _

end FoliationQM.DiracEquation
