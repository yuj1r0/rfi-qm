module
public import FoliationQM.DiracResidualPairing
public import FoliationQM.DiracActionSupport

/-!
# Continuity and integrability of the tested Dirac residual

For v13 `thm:dirac_lift`, the residual of the actual flat Dirac operator
is continuous at every C¹ point of the spinor field. Pairing with a compact
interior test gives an integrable real function on the open domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracResidualField
open MeasureTheory Matrix DiracMatrices DiracEquation DiracResidualPairing DiracActionSupport
open DiracJetFirstVariation

variable (hbar m c : ℝ)

/-- The jet residual is a continuous function of its spinor value and derivative slots. -/
theorem continuous_jetResidual : Continuous (fun z : Jet => diracJet hbar m c z.1 z.2) := by
  have hterm (μ : Fin 4) : Continuous (fun z : Jet => (gamma μ).mulVec (z.2 μ)) :=
    (gamma μ).mulVecLin.toContinuousLinearMap.continuous.comp ((continuous_apply μ).comp continuous_snd)
  have hsum := continuous_finsetSum Finset.univ (fun μ _ => hterm μ)
  exact ((continuous_const (y := Complex.I * (hbar : ℂ))).smul hsum).sub
    ((continuous_const (y := ((m*c : ℝ) : ℂ))).smul (continuous_fst (Y := Fin 4 → Spinor)))

/-- Continuity of the field residual follows from the actual spatial C¹ jet. -/
theorem continuousAt_diracField {ψ : Covector → Spinor} {x : Covector} (hψ : ContDiffAt ℝ 1 ψ x) :
    ContinuousAt (diracField hbar m c ψ) x := by
  change ContinuousAt ((fun z : Jet => diracJet hbar m c z.1 z.2) ∘ fieldJet ψ) x
  exact ((continuous_jetResidual hbar m c).continuousAt (x := fieldJet ψ x)).comp
    (continuousAt_fieldJet hψ)

/-- The tested residual is the real Dirac pairing with the actual flat operator. -/
def tested (ψ η : Covector → Spinor) (x : Covector) : ℝ :=
  pair (η x) (diracField hbar m c ψ x)

/-- Only continuity of the test itself is needed for continuity of the tested residual. -/
theorem continuousAt_tested {ψ η : Covector → Spinor} {x : Covector}
    (hψ : ContDiffAt ℝ 1 ψ x) (hη : ContinuousAt η x) :
    ContinuousAt (tested hbar m c ψ η) x :=
  (pairCLM.continuous.continuousAt.comp hη).clm_apply (continuousAt_diracField hbar m c hψ)

/-- A compact interior test makes the residual pairing integrable on the given domain. -/
theorem integrableOn_tested {ψ η : Covector → Spinor} {U : Set Covector}
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) (hη : ContinuousOn η U)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (tested hbar m c ψ η) U := by
  apply integrableOn_of_compact_support hc hs
  · intro x hx
    exact (pairCLM.continuous.continuousAt.comp_continuousWithinAt (hη x hx)).clm_apply (continuousAt_diracField hbar m c (hψ x hx)).continuousWithinAt
  · intro x hx
    change pairCLM (η x) _ = 0
    simp [image_eq_zero_of_notMem_tsupport hx]

end FoliationQM.DiracResidualField
