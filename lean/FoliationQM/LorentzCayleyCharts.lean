module
public import FoliationQM.LorentzCayleyCoordinates
public import FoliationQM.LorentzCayleyDomain
public import FoliationQM.LorentzCayleySmooth
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Intrinsic real Cayley charts for the proper future Lorentz group

Source scope: the independent Lorentz-frame target in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`.  The actual M+1 nonsingular
source is parametrized by the six independent metric-skew coordinates.
The target retains both the genuine 1-X denominator condition and the
strict future time-entry condition.  The algebraic Cayley roundtrips
prove the inverse identities on these domains.  Left translations give
an actual chart centered at every proper future Lorentz element.

Every chart is an open partial homeomorphism for the existing natural
matrix-unit subgroup topology.  No Spin identification defines a chart
or a topology.  The ambient forward and inverse formulas are smooth to
every order on their actual denominator domains.  The total identity
inverse is set to the group identity outside its target; only its
specified target values occur in inverse and regularity conclusions.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Topology
namespace FoliationQM.LorentzCayleyCharts
open LorentzMatrixGroup LorentzCayleyAlgebra LorentzCayleyCoordinates

/-- Six real independent metric-skew coordinates form the intrinsic Lorentz chart model. -/
abbrev Model := Coordinates

/-- The identity chart target retains genuine matrix invertibility and actual future orientation. -/
def target : Set Model :=
  {q | IsUnit (1 - matrixOf q) ∧ 0 < cayley (matrixOf q) 0 0}

/-- The actual inverse Cayley matrix followed by its six independent entries gives identity-chart coordinates. -/
def identityCoordinates (L : ProperFutureLorentz) : Model :=
  coordinatesOf (inverseCayley (matrix L.val))

/-- On the actual source, extracting and reassembling inverse Cayley coordinates recovers their full ambient matrix. -/
theorem matrixOf_identityCoordinates (L : ProperFutureLorentz)
    (hL : L ∈ LorentzCayleyDomain.source) :
    matrixOf (identityCoordinates L) = inverseCayley (matrix L.val) :=
  matrixOf_coordinatesOf _
    (inverseCayley_isEtaSkew _ (metric L.val) ((LorentzCayleyDomain.mem_source_iff L).mp hL))

/-- Actual identity coordinates send the nonsingular source into the full independent target conditions. -/
theorem identityCoordinates_mem_target (L : ProperFutureLorentz)
    (hL : L ∈ LorentzCayleyDomain.source) : identityCoordinates L ∈ target := by
  have hu := (LorentzCayleyDomain.mem_source_iff L).mp hL
  change IsUnit (1 - matrixOf (identityCoordinates L)) ∧
    0 < cayley (matrixOf (identityCoordinates L)) 0 0
  rw [matrixOf_identityCoordinates L hL, cayley_inverseCayley _ hu]
  exact ⟨isUnit_one_sub_inverseCayley _ hu, LorentzCayleyDomain.time_pos L⟩

/-- The actual Cayley reconstruction of an independent skew coordinate is smooth at every genuine denominator unit. -/
theorem contDiffAt_cayley_matrixOf (n : WithTop ℕ∞) {q : Model}
    (hq : IsUnit (1 - matrixOf q)) :
    ContDiffAt ℝ n (fun p : Model => cayley (matrixOf p)) q :=
  (LorentzCayleySmooth.contDiffAt_cayley n hq).comp q matrixOf.contDiff.contDiffAt

/-- The independent Cayley coordinate target is open in ordinary six-dimensional real space. -/
theorem isOpen_target : IsOpen target := by
  let U : Set Model := {q | IsUnit (1 - matrixOf q)}
  have hU : IsOpen U := by
    have he : U = {q : Model | (1 - matrixOf q).det ≠ 0} := by
      ext q
      exact cayley_domain_iff (matrixOf q)
    rw [he]
    exact isOpen_ne_fun (continuous_const.sub matrixOf.continuous).matrix_det continuous_const
  have hc : ContinuousOn (fun q : Model => cayley (matrixOf q) 0 0) U := by
    intro q hq
    exact ((continuous_apply 0).continuousAt.comp
      ((continuous_apply 0).continuousAt.comp
        (contDiffAt_cayley_matrixOf 0 hq).continuousAt)).continuousWithinAt
  exact hc.isOpen_inter_preimage hU isOpen_Ioi

/-- The total identity-chart inverse reconstructs the actual Lorentz matrix on target and equals identity elsewhere. -/
def identityInverse (q : Model) : ProperFutureLorentz := by
  classical
  exact if hq : q ∈ target then
    LorentzCayleyDomain.ofMatrix (cayley (matrixOf q))
      (cayley_metric _ (matrixOf_mem q) hq.1)
      (cayley_det _ (matrixOf_mem q) hq.1) hq.2
  else 1

/-- On the explicit target, the identity-chart inverse has exactly the actual Cayley matrix. -/
theorem identityInverse_matrix {q : Model} (hq : q ∈ target) :
    matrix (identityInverse q).val = cayley (matrixOf q) := by
  simp only [identityInverse, dite_eq_left hq]
  rfl

/-- The inverse reconstructed matrix lies in the actual nonsingular identity-chart source. -/
theorem identityInverse_mem_source {q : Model} (hq : q ∈ target) :
    identityInverse q ∈ LorentzCayleyDomain.source := by
  rw [LorentzCayleyDomain.mem_source_iff, identityInverse_matrix hq]
  exact isUnit_cayley_add_one _ hq.1

/-- Genuine identity-chart reconstruction recovers every original Lorentz element in the stated source. -/
theorem identityInverse_identityCoordinates (L : ProperFutureLorentz)
    (hL : L ∈ LorentzCayleyDomain.source) : identityInverse (identityCoordinates L) = L := by
  apply Subtype.ext
  apply matrix_injective
  rw [identityInverse_matrix (identityCoordinates_mem_target L hL),
    matrixOf_identityCoordinates L hL]
  exact cayley_inverseCayley _ ((LorentzCayleyDomain.mem_source_iff L).mp hL)

/-- Reading the actual inverse Cayley coordinates recovers every target coordinate tuple. -/
theorem identityCoordinates_identityInverse {q : Model} (hq : q ∈ target) :
    identityCoordinates (identityInverse q) = q := by
  change coordinatesOf (inverseCayley (matrix (identityInverse q).val)) = q
  rw [identityInverse_matrix hq, inverseCayley_cayley _ hq.1, coordinatesOf_matrixOf]

/-- Identity-chart coordinates are continuous on their actual nonsingular source in the natural subgroup topology. -/
theorem continuousOn_identityCoordinates :
    ContinuousOn identityCoordinates LorentzCayleyDomain.source := by
  intro L hL
  have hv : ContinuousAt (fun K : ProperFutureLorentz => matrix K.val) L :=
    (continuous_matrix.comp continuous_subtype_val).continuousAt
  have hi : ContinuousAt (fun K : ProperFutureLorentz => inverseCayley (matrix K.val)) L :=
    (LorentzCayleySmooth.contDiffAt_inverseCayley 0
      ((LorentzCayleyDomain.mem_source_iff L).mp hL)).continuousAt.comp (f := fun K : ProperFutureLorentz => matrix K.val) hv
  exact (coordinatesOf.continuous.continuousAt.comp
    (f := fun K : ProperFutureLorentz => inverseCayley (matrix K.val)) hi).continuousWithinAt

/-- The identity inverse is continuous on its target in the pre-existing Lorentz subgroup topology. -/
theorem continuousOn_identityInverse : ContinuousOn identityInverse target := by
  apply LorentzMatrixTopology.isClosedEmbedding_properMatrix.isEmbedding.isInducing.continuousOn_iff.mpr
  have hc : ContinuousOn (fun q : Model => cayley (matrixOf q)) target :=
    fun _ hq => (contDiffAt_cayley_matrixOf 0 hq.1).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact identityInverse_matrix hq

/-- The independent six-coordinate identity chart is a genuine open partial homeomorphism for the natural Lorentz topology. -/
def identityChart : OpenPartialHomeomorph ProperFutureLorentz Model where
  toFun := identityCoordinates
  invFun := identityInverse
  source := LorentzCayleyDomain.source
  target := target
  map_source' := identityCoordinates_mem_target
  map_target' := fun _ hq => identityInverse_mem_source hq
  left_inv' := identityInverse_identityCoordinates
  right_inv' := fun _ hq => identityCoordinates_identityInverse hq
  open_source := LorentzCayleyDomain.isOpen_source
  open_target := isOpen_target
  continuousOn_toFun := continuousOn_identityCoordinates
  continuousOn_invFun := continuousOn_identityInverse

/-- The identity chart has exactly the original nonsingular M+1 source. -/
theorem identityChart_source : identityChart.source = LorentzCayleyDomain.source := rfl

/-- The identity chart has exactly the independently specified future Cayley target. -/
theorem identityChart_target : identityChart.target = target := rfl

/-- The identity chart reads exactly the six actual inverse Cayley matrix entries. -/
theorem identityChart_apply (L : ProperFutureLorentz) :
    identityChart L = coordinatesOf (inverseCayley (matrix L.val)) := rfl

/-- The identity-chart inverse has the exact Cayley matrix on its actual target. -/
theorem identityChart_symm_matrix {q : Model} (hq : q ∈ target) :
    matrix (identityChart.symm q).val = cayley (matrixOf q) :=
  identityInverse_matrix hq

/-- The actual identity has zero Cayley coordinates. -/
theorem identityChart_one : identityChart (1 : ProperFutureLorentz) = 0 := by
  change coordinatesOf (inverseCayley (1 : Mat4)) = 0
  rw [inverseCayley_one, map_zero]

/-- The origin belongs to the actual six-dimensional future Cayley target. -/
theorem zero_mem_target : (0 : Model) ∈ target := by
  change IsUnit (1 - matrixOf 0) ∧ 0 < cayley (matrixOf 0) 0 0
  rw [map_zero, sub_zero, cayley_zero]
  norm_num

/-- Every group element obtains a genuine translated Cayley chart by the original topological group action. -/
def chart (L : ProperFutureLorentz) : OpenPartialHomeomorph ProperFutureLorentz Model :=
  (Homeomorph.mulLeft L⁻¹).transOpenPartialHomeomorph identityChart

/-- The translated chart is precisely the composition of left inverse translation and the identity open partial homeomorphism. -/
theorem chart_eq_trans (L : ProperFutureLorentz) :
    chart L = (Homeomorph.mulLeft L⁻¹).toOpenPartialHomeomorph.trans identityChart :=
  Homeomorph.transOpenPartialHomeomorph_eq_trans _ _

/-- The translated chart source is exactly the nonsingular source of the actual relative matrix. -/
theorem chart_source (L : ProperFutureLorentz) :
    (chart L).source = LorentzCayleyDomain.translatedSource L := rfl

/-- Every translated Cayley chart has the same independent open six-coordinate target. -/
theorem chart_target (L : ProperFutureLorentz) : (chart L).target = target := rfl

/-- Ambient translated coordinates are actual inverse Cayley matrix coordinates after fixed left matrix multiplication. -/
def ambientCoordinates (L : ProperFutureLorentz) (M : Mat4) : Model :=
  coordinatesOf (inverseCayley (matrix (L⁻¹).val * M))

/-- The chart's actual forward function agrees globally with its ambient rational matrix formula. -/
theorem chart_apply (L K : ProperFutureLorentz) :
    chart L K = ambientCoordinates L (matrix K.val) := rfl

/-- Source membership is precisely invertibility of the actual translated M+1 denominator. -/
theorem mem_chart_source_iff (L K : ProperFutureLorentz) :
    K ∈ (chart L).source ↔ IsUnit (matrix (L⁻¹).val * matrix K.val + 1) := by
  change L⁻¹ * K ∈ LorentzCayleyDomain.source ↔ _
  exact LorentzCayleyDomain.mem_source_iff (L⁻¹ * K)

/-- Every Lorentz element belongs to the source of its own actual translated chart. -/
theorem mem_chart_source (L : ProperFutureLorentz) : L ∈ (chart L).source :=
  LorentzCayleyDomain.mem_translatedSource L

/-- Each translated Cayley chart sends its actual center to the zero coordinate tuple. -/
theorem chart_self (L : ProperFutureLorentz) : chart L L = 0 := by
  change identityChart (L⁻¹ * L) = 0
  rw [inv_mul_cancel, identityChart_one]

/-- On the target, the inverse translated chart has exactly fixed left matrix multiplication times Cayley reconstruction. -/
theorem chart_symm_matrix (L : ProperFutureLorentz) {q : Model} (hq : q ∈ target) :
    matrix ((chart L).symm q).val = matrix L.val * cayley (matrixOf q) := by
  change matrix ((L⁻¹)⁻¹ * identityInverse q).val = _
  rw [inv_inv]
  change matrix L.val * matrix (identityInverse q).val = _
  rw [identityInverse_matrix hq]

/-- The actual inverse chart sends the zero coordinate tuple back to its Lorentz center. -/
theorem chart_symm_zero (L : ProperFutureLorentz) : (chart L).symm 0 = L := by
  rw [← chart_self L]
  exact (chart L).left_inv (mem_chart_source L)

/-- The globally defined ambient chart formula is smooth at every point where its actual translated denominator is a unit. -/
theorem contDiffAt_ambientCoordinates (n : WithTop ℕ∞) (L : ProperFutureLorentz)
    {M : Mat4} (hM : IsUnit (matrix (L⁻¹).val * M + 1)) :
    ContDiffAt ℝ n (ambientCoordinates L) M :=
  coordinatesOf.contDiff.contDiffAt.comp M
    ((LorentzCayleySmooth.contDiffAt_inverseCayley n hM).comp M
      (contDiffAt_const.mul contDiffAt_id))

/-- The ambient matrix values of the actual inverse translated chart are smooth to every order on its full target. -/
theorem contDiffOn_inverse_matrix (n : WithTop ℕ∞) (L : ProperFutureLorentz) :
    ContDiffOn ℝ n (fun q : Model => matrix ((chart L).symm q).val) target := by
  have hc : ContDiffOn ℝ n (fun q : Model => matrix L.val * cayley (matrixOf q)) target :=
    fun _ hq => (contDiffAt_const.mul (contDiffAt_cayley_matrixOf n hq.1)).contDiffWithinAt
  apply hc.congr
  intro q hq
  exact chart_symm_matrix L hq

end FoliationQM.LorentzCayleyCharts
