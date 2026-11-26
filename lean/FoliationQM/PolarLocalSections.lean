module
public import FoliationQM.PolarDatumTopology
public import FoliationQM.RotatedPolarChart

/-!
# Explicit continuous local sections of the polar realization

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The existing
principal and rotated reconstructions define concrete polar data for
every regular spinor. Each realizes that same spinor exactly; the rotated
amplitude compensates the actual matrix rotation by its factor of i.

The ordinary determinant-branch domains induce two open patches in the
regular-spinor subtype. In the natural datum topology, the principal
section is continuous on the first patch and the rotated section on the
second. Their union covers every regular spinor and therefore supplies
an actual local continuous section around every point. No continuous
global choice of a real angle or of one datum representative is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.PolarLocalSections
open DiracMatrices SpinorMatrix SpinorRegularity PolarMatrixFibers RegularPolarReconstruction
open PolarSignQuotient PrincipalPolarSmooth RotatedPolarChart
open PolarDatumTopology

/-- The actual principal reconstruction, regarded as concrete nonzero polar data. -/
def principalSection : RegularSpinor → Datum := inverseDatum

/-- The actual rotated reconstruction compensates the minus-i matrix rotation by an i factor in its nonzero amplitude. -/
def rotatedSection (q : RegularSpinor) : Datum where
  t := Complex.I * amplitudePhase (rotate q.val)
  A := normalizedMatrix (rotate q.val)
  t_ne_zero := mul_ne_zero Complex.I_ne_zero
    (amplitudePhase_ne_zero ((regular_rotate_iff q.val).mpr q.property))
  det_eq_one := normalizedMatrix_det ((regular_rotate_iff q.val).mpr q.property)

/-- The concrete principal section realizes its original regular spinor at every point. -/
theorem realize_principalSection (q : RegularSpinor) :
    realize (principalSection q) = q := realize_inverseDatum q

/-- The concrete rotated section realizes its original regular spinor at every point, including outside its continuity patch. -/
theorem realize_rotatedSection (q : RegularSpinor) :
    realize (rotatedSection q) = q := by
  apply Subtype.ext
  apply toMatrix_injective
  change toMatrix (parameterSpinor (Complex.I * amplitudePhase (rotate q.val))
    (normalizedMatrix (rotate q.val))) = toMatrix q.val
  rw [toMatrix_parameterSpinor, mul_smul,
    amplitudePhase_smul_normalizedMatrix ((regular_rotate_iff q.val).mpr q.property),
    toMatrix_rotate, smul_smul]
  simp

/-- The rotated datum amplitude is exactly the positive density square root times the existing rotated half-angle exponential. -/
theorem rotatedSection_amplitude (q : RegularSpinor) :
    (rotatedSection q).t = (Real.sqrt (invariantDensity q.val) : ℂ) *
      Complex.exp (Complex.I * (rotatedPhase q.val : ℂ) / 2) := by
  have he : Complex.I * ((Real.pi + determinantPhase (rotate q.val) : ℝ) : ℂ) / 2 =
      (Real.pi : ℂ) / 2 * Complex.I + Complex.I * (determinantPhase (rotate q.val) : ℂ) / 2 := by
    push_cast
    ring
  change Complex.I * amplitudePhase (rotate q.val) =
    (Real.sqrt (invariantDensity q.val) : ℂ) *
      Complex.exp (Complex.I * ((Real.pi + determinantPhase (rotate q.val) : ℝ) : ℂ) / 2)
  rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  simp only [amplitudePhase, invariantDensity_rotate]
  ring

/-- The principal determinant branch restricted to the actual regular-spinor subtype. -/
def principalPatch : Set RegularSpinor := Subtype.val ⁻¹' PrincipalDomain

/-- The rotated determinant branch restricted to the actual regular-spinor subtype. -/
def rotatedPatch : Set RegularSpinor := Subtype.val ⁻¹' RotatedDomain

/-- The principal regular-spinor patch is open in its ordinary subtype topology. -/
theorem principalPatch_isOpen : IsOpen principalPatch :=
  principalDomain_isOpen.preimage continuous_subtype_val

/-- The rotated regular-spinor patch is open in its ordinary subtype topology. -/
theorem rotatedPatch_isOpen : IsOpen rotatedPatch :=
  rotatedDomain_isOpen.preimage continuous_subtype_val

/-- The two concrete reconstruction patches cover every actual regular spinor. -/
theorem patch_cover (q : RegularSpinor) : q ∈ principalPatch ∨ q ∈ rotatedPatch :=
  regular_two_chart_cover q.property

/-- The actual principal datum section is continuous at each point of its principal determinant patch. -/
theorem continuousAt_principalSection {q : RegularSpinor} (hq : q ∈ principalPatch) :
    ContinuousAt principalSection q := by
  apply PolarDatumTopology.continuousAt_iff.mpr
  constructor
  · exact (contDiffAt_amplitudePhase 0 hq).continuousAt.comp continuous_subtype_val.continuousAt
  · exact (contDiffAt_normalizedMatrix 0 hq).continuousAt.comp continuous_subtype_val.continuousAt

/-- The actual rotated datum section is continuous at each point of its rotated determinant patch. -/
theorem continuousAt_rotatedSection {q : RegularSpinor} (hq : q ∈ rotatedPatch) :
    ContinuousAt rotatedSection q := by
  apply PolarDatumTopology.continuousAt_iff.mpr
  constructor
  · exact continuousAt_const.mul (((contDiffAt_amplitudePhase 0 hq).continuousAt.comp
      (contDiff_rotate 0).continuous.continuousAt).comp continuous_subtype_val.continuousAt)
  · exact (contDiffAt_rotatedMatrix 0 hq).continuousAt.comp continuous_subtype_val.continuousAt

/-- The concrete principal datum section is continuous throughout its open reconstruction patch. -/
theorem continuousOn_principalSection : ContinuousOn principalSection principalPatch :=
  fun _ hq => (continuousAt_principalSection hq).continuousWithinAt

/-- The concrete rotated datum section is continuous throughout its open reconstruction patch. -/
theorem continuousOn_rotatedSection : ContinuousOn rotatedSection rotatedPatch :=
  fun _ hq => (continuousAt_rotatedSection hq).continuousWithinAt

/-- Every regular spinor admits an explicit datum section continuous at that point and realizing every input spinor exactly. -/
theorem exists_continuous_local_section (q : RegularSpinor) :
    ∃ s : RegularSpinor → Datum, ContinuousAt s q ∧ ∀ y, realize (s y) = y := by
  rcases patch_cover q with hq | hq
  · exact ⟨principalSection, continuousAt_principalSection hq, realize_principalSection⟩
  · exact ⟨rotatedSection, continuousAt_rotatedSection hq, realize_rotatedSection⟩

/-- Every regular spinor lies in an explicit open neighborhood carrying a continuous datum section of the actual realization. -/
theorem exists_open_local_section (q : RegularSpinor) :
    ∃ U : Set RegularSpinor, ∃ s : RegularSpinor → Datum,
      IsOpen U ∧ q ∈ U ∧ ContinuousOn s U ∧ ∀ y, realize (s y) = y := by
  rcases patch_cover q with hq | hq
  · exact ⟨principalPatch, principalSection, principalPatch_isOpen, hq,
      continuousOn_principalSection, realize_principalSection⟩
  · exact ⟨rotatedPatch, rotatedSection, rotatedPatch_isOpen, hq,
      continuousOn_rotatedSection, realize_rotatedSection⟩

end FoliationQM.PolarLocalSections
