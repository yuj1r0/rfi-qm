module

public import FoliationQM.CliffordCommutators
public import FoliationQM.RealLorentzFrame

/-!
# Uniqueness of the real antisymmetric Lorentz coefficient expansion

Source: the real antisymmetric body-connection expansion in v13
`eq:maurer_cartan_def` and its recovery by `eq:ricci_rotation_coeffs`.
The indexed commutator recovers every coefficient column, up to its nonzero
Minkowski sign, through the actual injective real gamma expansion. Thus
actual generator equality determines the entire antisymmetric coefficient
array. This is uniqueness within the stated expansion domain; no existence
or arbitrary matrix-field reconstruction is asserted.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.LorentzCoefficientUniqueness
open DiracMatrices CliffordCommutators RealLorentzFrame

/-- The actual commutator with one gamma matrix is the real gamma expansion of the corresponding antisymmetric coefficient column times its metric sign. -/
theorem generator_commutator_eq_gammaExpansion (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) (A : Fin 4) :
    generator omega * gamma A - gamma A * generator omega =
      gammaExpansion (fun a => omega a A * sign A) := by
  rw [generator_gamma_commutator omega hanti A]
  unfold gammaExpansion
  apply Finset.sum_congr rfl
  intro a _
  simp only [eta, mul_ite, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : A=0 <;> simp [sign, h]

/-- Equal actual generators have equal real coefficient arrays when both arrays are antisymmetric. -/
theorem generator_injective_on_antisymmetric
    {omega theta : Fin 4 → Fin 4 → ℝ}
    (hantiOmega : ∀ a b, omega a b = -omega b a)
    (hantiTheta : ∀ a b, theta a b = -theta b a)
    (hgen : generator omega = generator theta) : omega = theta := by
  funext a A
  have hc := congrArg (fun M : Mat => M * gamma A - gamma A * M) hgen
  rw [generator_commutator_eq_gammaExpansion omega hantiOmega A,
    generator_commutator_eq_gammaExpansion theta hantiTheta A] at hc
  have he := congrFun (gammaExpansion_injective hc) a
  by_cases h : A=0 <;> simpa [sign, h] using he

/-- On real antisymmetric arrays, actual generator equality is equivalent to coefficient equality. -/
theorem generator_eq_iff {omega theta : Fin 4 → Fin 4 → ℝ}
    (hantiOmega : ∀ a b, omega a b = -omega b a)
    (hantiTheta : ∀ a b, theta a b = -theta b a) :
    generator omega = generator theta ↔ omega = theta :=
  ⟨generator_injective_on_antisymmetric hantiOmega hantiTheta, congrArg generator⟩

/-- A real antisymmetric coefficient array has zero actual generator exactly when every coefficient is zero. -/
theorem generator_eq_zero_iff (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) :
    generator omega = 0 ↔ omega = 0 := by
  have hz : generator (0 : Fin 4 → Fin 4 → ℝ) = 0 := by simp [generator]
  rw [← hz]
  exact generator_eq_iff hanti (by intros; simp)

end FoliationQM.LorentzCoefficientUniqueness
