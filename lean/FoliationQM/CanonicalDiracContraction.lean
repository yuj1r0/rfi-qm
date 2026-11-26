module
public import FoliationQM.PolarConnectionContraction
public import FoliationQM.PolarVectorGeometry
public import FoliationQM.LorentzConnectionCurvature

/-!
# Physical velocity and spin-connection splitting of the canonical contraction

Source: v13 `eq:canonical_P_L`, accompanying the polar Dirac density.
The actual epsilon contraction is split into the physical velocity term and
two transverse terms, with the explicit c normalization. The longitudinal
piece is the negative velocity pairing with the spin coefficient -(hbar/2)
omega_12. This identifies the scalar contraction in the source; it does not
select a unique momentum covector or claim a scalar phase potential.
-/
@[expose] public section
noncomputable section
namespace FoliationQM.CanonicalDiracContraction
open PolarConnectionContraction PolarVectorGeometry RealLorentzFrame

/-- The source spin coefficient in each of four directions, with its negative half-hbar normalization. -/
def spinCoefficient (hbar : ℝ) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (mu : Fin 4) : ℝ :=
  -(hbar/2)*omega mu 1 2

/-- The canonical contraction has the source physical-velocity term plus the two explicitly c-scaled transverse terms. -/
theorem canonicalContraction_velocity (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) :
    canonicalContraction hbar c u omega =
      (hbar/2)*∑ mu, velocity c u mu*omega mu 1 2 +
      (hbar*c/2)*∑ mu,
        (inverseCoefficients u mu 1*omega mu 2 0+inverseCoefficients u mu 2*omega mu 0 1) := by
  rw [canonicalContraction_three_terms hbar c u omega hanti]
  simp only [velocity, timeVector, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  ring

/-- The longitudinal half-hbar velocity term is the negative pairing with the actual spin coefficient. -/
theorem longitudinal_spin_pairing (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (hbar/2)*∑ mu, velocity c u mu*omega mu 1 2 =
      -∑ mu, velocity c u mu*spinCoefficient hbar omega mu := by
  simp only [spinCoefficient, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  ring

/-- The canonical scalar contraction is minus velocity paired with the spin connection plus the two transverse frame terms. -/
theorem canonicalContraction_spin_split (hbar c : ℝ) (u : Fin 4 → Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) :
    canonicalContraction hbar c u omega =
      -(∑ mu, velocity c u mu*spinCoefficient hbar omega mu) +
      (hbar*c/2)*∑ mu,
        (inverseCoefficients u mu 1*omega mu 2 0+inverseCoefficients u mu 2*omega mu 0 1) := by
  rw [canonicalContraction_velocity hbar c u omega hanti, longitudinal_spin_pairing]

/-- Evaluating the actual scalar spin-connection field on the specified directions gives exactly the spin coefficients used in the canonical density split. -/
theorem spinCoefficient_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hbar : ℝ) (omega : E → E → Fin 4 → Fin 4 → ℝ) (x : E)
    (directions : Fin 4 → E) (mu : Fin 4) :
    spinCoefficient hbar (fun nu => omega x (directions nu)) mu =
      LorentzConnectionCurvature.spinConnection hbar omega x (directions mu) := rfl

end FoliationQM.CanonicalDiracContraction
