module
public import FoliationQM.ScalarKGGreen
public import FoliationQM.ScalarLocalTesting
public import FoliationQM.TwistedScalarStationarity
public import FoliationQM.RelativePolarStationaryAction

/-!
# Distributional and classical scalar limits of stationary chiral families

For v13 `thm:dirac_lift` and `thm:kahler`, compact tests move the two
spacetime derivatives onto the test field. Local L¹ convergence of the
fields and of their chiral potential times the field suffices to pass
the stationary equation to the limit. On a smooth positive scalar chart,
vanishing limiting source then gives the Hamilton–Jacobi equation and
the conservation law for the density current.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff ComplexConjugate
namespace FoliationQM.StationaryScalarLimit
open MeasureTheory Filter ScalarLocalTesting ScalarKGGreen DiracFieldDensity
open FlatIntegrationByParts TwistedScalarDensity TwistedScalarVariation TwistedScalarStationarity

/-- The chiral multiplication term in the Euler–Lagrange equation. -/
def source (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) : ℂ :=
  (potential p β x : ℂ) * z x

/-- The limiting equation with both spacetime derivatives on the compact test. -/
def WeakEquation (p : MassiveParameters) (z g : Covector → ℂ) (U : Set Covector) : Prop :=
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    tested U (kgOperator p η coordinateDirections) z + tested U η g = 0

variable (p : MassiveParameters) {U : Set Covector} {Z : ℕ → Covector → ℂ} {B : ℕ → Covector → ℝ}
variable {z g : Covector → ℂ}

/-- A sequence of genuine solutions has the stated distributional limit. An arbitrary surviving
source term is retained. Neither field-derivative convergence nor finite total actions are required. -/
theorem weak_of_solutions (hU : IsOpen U) (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hz : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x) (he : ∀ n, ∀ x ∈ U, force p (B n) (Z n) x = 0)
    (hZ : LocalL1 U Z z) (hG : LocalL1 U (fun n => source p (B n) (Z n)) g) :
    WeakEquation p z g U := by
  intro η hη hc hs
  have ht := tendsto_tested hU hZ (continuous_kg_test p hη) (compact_kg_test p η hc)
    ((tsupport_kg_subset p η).trans hs)
  have hg := tendsto_tested hU hG hη.continuous hc hs
  have heq (n : ℕ) : tested U (kgOperator p η coordinateDirections) (Z n) +
      tested U η (source p (B n) (Z n)) = 0 := by
    apply (tested_force p hU (hb n) (hz n) hη hc hs).symm.trans
    exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by simp [he n x hx])
  have ht' := ht.add hg
  simp_rw [heq] at ht'
  exact tendsto_nhds_unique ht' tendsto_const_nhds

/-- For C² approximants, affine stationarity gives the same distributional limit. -/
theorem weak_of_stationary (hU : IsOpen U) (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hz : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x) (hs : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z z) (hG : LocalL1 U (fun n => source p (B n) (Z n)) g) :
    WeakEquation p z g U :=
  weak_of_solutions p hU hb hz (fun n => (affine_iff_force p hU (hb n) (hz n)).mp (hs n)) hZ hG

/-- A C² limiting field and continuous source satisfy the distributional equation pointwise. -/
theorem classical_of_weak (hU : IsOpen U) (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) (hg : ContinuousOn g U)
    (hw : WeakEquation p z g U) : ∀ x ∈ U, kgOperator p z coordinateDirections x + g x = 0 := by
  apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU _
    ((OpenIntegrationByParts.continuousOn_kgOperator p hz coordinateDirections).add hg)
  intro η hη hc hs
  have hK := (OpenIntegrationByParts.integrable_test_kgOperator p (hη.of_le (by simp)) hz hc hs coordinateDirections).re
  simp only [RCLike.re_eq_complex_re] at hK
  have hG : IntegrableOn (fun x => (conj (η x) * g x).re) U := by
    apply DiracActionSupport.integrableOn_of_compact_support hc hs
    · exact Complex.continuous_re.comp_continuousOn (hη.continuous.star.continuousOn.mul hg)
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  calc
    _ = (∫ x in U, (conj (η x) * kgOperator p z coordinateDirections x).re) + tested U η g := by
      unfold tested
      rw [← integral_add hK hG]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp [Pi.add_apply, mul_add]
    _ = _ := by rw [green p hU hz hη hc hs]; exact hw η hη hc hs

/-- Vanishing source in local L¹ gives the pointwise original Klein–Gordon equation for a C² limit. -/
theorem kg_limit (hU : IsOpen U) (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hn : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x) (hs : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z z) (hV : LocalL1 U (fun n => source p (B n) (Z n)) (fun _ => 0))
    (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) : ∀ x ∈ U, kgOperator p z coordinateDirections x = 0 := by
  simpa using classical_of_weak p hU hz continuousOn_const (weak_of_stationary p hU hb hn hs hZ hV)

/-- The limit is a stationary field of the true scalar relative action on U. -/
theorem scalar_stationary_limit (hU : IsOpen U) (hb : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hn : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (Z n) x) (hs : ∀ n, AffineStationary p (B n) (Z n) U)
    (hZ : LocalL1 U Z z) (hV : LocalL1 U (fun n => source p (B n) (Z n)) (fun _ => 0))
    (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) :
    RelativeStationaryAction.RelativeStationaryOn p z coordinateDirections U :=
  (RelativeStationaryAction.relativeStationaryOn_iff_kgOperator p hU _ hz).mpr (kg_limit p hU hb hn hs hZ hV hz)

end FoliationQM.StationaryScalarLimit
