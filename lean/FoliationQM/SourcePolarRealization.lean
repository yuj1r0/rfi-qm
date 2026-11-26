module
public import FoliationQM.SourcePolarDatum
public import FoliationQM.PrincipalPolarChart

/-!
# Actual spinor realization and exact fibers of the source polar coordinates

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The source
positive density, full angle modulo four pi and actual determinant-one
matrix realize a regular spinor through their concrete amplitude datum.
The realization agrees exactly with the existing chiral-angle polar
spinor and with the real-angle matrix expression on every representative.

Actual invariant density and the full complex determinant recover the
prescribed density and squared half-angle phase. Principal phase and
normalized-matrix recovery are stated only on the open principal angle
interval. The exact fibers are proved independently of a source quotient:
the two possibilities are equality and the simultaneous two-pi angle
shift with matrix negation. The realization is continuous and surjective.
No global real-angle choice or abstract Spin-group classification is used.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SourcePolarRealization
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSignQuotient PolarMatrixFibers PolarSpinorBilinears RegularPolarReconstruction
open PolarAmplitudeTopology ChiralAngleCircle SourcePolarDatum

/-- Realize the literal source density, four-pi angle and determinant-one matrix as its actual regular spinor. -/
def realizeSource (d : SourceDatum) : RegularSpinor := realize (toDatum d)

/-- The source realization is exactly the actual matrix-encoded spinor with its positive square-root amplitude and half-angle phase. -/
theorem realizeSource_parameterSpinor (d : SourceDatum) :
    (realizeSource d).val = parameterSpinor
      ((Real.sqrt (d.1 : ℝ) : ℂ) * (phaseEquiv d.2.1 : ℂ)) (d.2.2 : Mat2) := rfl

/-- For every quotient angle the actual source realization equals the existing four-pi chiral polar spinor. -/
theorem realizeSource_polarOnAngle (d : SourceDatum) :
    (realizeSource d).val = polarOnAngle (d.1 : ℝ) d.2.1 (spin (d.2.2 : Mat2)) := by
  rcases d with ⟨rho, q, A⟩
  induction q using QuotientAddGroup.induction_on
  rename_i beta
  rw [realizeSource_parameterSpinor, phaseEquiv_coe_complex, polarOnAngle_coe,
    parameterSpinor_polarAmplitude]

/-- On every real angle representative the actual source realization is the genuine matrix polar expression. -/
theorem realizeSource_coe (rho : PositiveDensity) (beta : ℝ) (A : SpecialLinearMatrix) :
    (realizeSource (rho, (beta : Angle), A)).val =
      polarSpinor (rho : ℝ) beta (spin (A : Mat2)) := by
  rw [realizeSource_polarOnAngle, polarOnAngle_coe]

/-- The actual source realization is continuous for the natural source product and regular-spinor subtype topologies. -/
theorem continuous_realizeSource : Continuous realizeSource :=
  PolarDatumTopology.continuous_realize.comp datumHomeomorph.continuous

/-- The actual scalar-pseudoscalar invariant density of a realized spinor is exactly the source density coordinate. -/
theorem density_realizeSource (d : SourceDatum) :
    invariantDensity (realizeSource d).val = (d.1 : ℝ) := by
  rw [realizeSource_parameterSpinor, density_parameterSpinor _ _ d.2.2.property]
  exact norm_amplitude_sq (d.1, phaseEquiv d.2.1)

/-- The actual spinor determinant is the source density times the square of its half-angle circle phase. -/
theorem determinant_realizeSource (d : SourceDatum) :
    Matrix.det (toMatrix (realizeSource d).val) =
      (d.1 : ℂ) * (phaseEquiv d.2.1 : ℂ)^2 := by
  rw [realizeSource_parameterSpinor, det_parameterSpinor _ _ d.2.2.property, mul_pow]
  have hs : (Real.sqrt (d.1 : ℝ) : ℂ)^2 = (d.1 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt d.1.property.le
  rw [hs]

/-- On a real angle representative the actual determinant is the positive density times the full-angle complex exponential. -/
theorem determinant_realizeSource_coe (rho : PositiveDensity) (beta : ℝ)
    (A : SpecialLinearMatrix) :
    Matrix.det (toMatrix (realizeSource (rho, (beta : Angle), A)).val) =
      (rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ)) := by
  rw [realizeSource_coe]
  exact PrincipalPolarChart.determinant_polar _ _ _ rho.property.le A.property

/-- The actual principal determinant phase recovers the source real angle when that angle lies strictly in the principal interval. -/
theorem determinantPhase_realizeSource_coe (rho : PositiveDensity) (beta : ℝ)
    (A : SpecialLinearMatrix) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    determinantPhase (realizeSource (rho, (beta : Angle), A)).val = beta := by
  rw [realizeSource_coe]
  exact PrincipalPolarChart.determinantPhase_polar _ _ _ rho.property A.property hbeta

/-- Actual principal reconstruction recovers the prescribed determinant-one matrix on the principal source angle interval. -/
theorem normalizedMatrix_realizeSource_coe (rho : PositiveDensity) (beta : ℝ)
    (A : SpecialLinearMatrix) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    normalizedMatrix (realizeSource (rho, (beta : Angle), A)).val = (A : Mat2) := by
  rw [realizeSource_coe]
  exact PrincipalPolarChart.normalizedMatrix_polar _ _ _ rho.property A.property hbeta

/-- Two actual source data realize the same spinor exactly when they agree or undergo the simultaneous two-pi angle shift and matrix sign reversal. -/
theorem realizeSource_eq_iff (d e : SourceDatum) :
    realizeSource d = realizeSource e ↔ d = e ∨ d = shiftNeg e := by
  change realize (toDatum d) = realize (toDatum e) ↔ _
  rw [realize_eq_iff_related]
  change (toDatum d = toDatum e ∨ toDatum d = negDatum (toDatum e)) ↔ _
  rw [← toDatum_shiftNeg]
  constructor
  · rintro (h | h)
    · exact Or.inl (datumHomeomorph.injective h)
    · exact Or.inr (datumHomeomorph.injective h)
  · rintro (h | h)
    · exact Or.inl (congrArg toDatum h)
    · exact Or.inr (congrArg toDatum h)

/-- The exact source fibers have equal density and either equal angle and matrix or a two-pi angle shift with the opposite matrix. -/
theorem realizeSource_coordinate_fibers (d e : SourceDatum) :
    realizeSource d = realizeSource e ↔ (d.1 : ℝ) = (e.1 : ℝ) ∧
      ((d.2.1 = e.2.1 ∧ (d.2.2 : Mat2) = (e.2.2 : Mat2)) ∨
       (d.2.1 = e.2.1 + ((2 * Real.pi : ℝ) : Angle) ∧
         (d.2.2 : Mat2) = -(e.2.2 : Mat2))) := by
  rw [realizeSource_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨hrho, h | h⟩
    · exact Or.inl (Prod.ext (Subtype.ext hrho) (Prod.ext h.1 (Subtype.ext h.2)))
    · exact Or.inr (Prod.ext (Subtype.ext hrho) (Prod.ext h.1 (Subtype.ext h.2)))

/-- The literal simultaneous two-pi angle shift and matrix negation leaves the actual realized spinor unchanged. -/
theorem realizeSource_shiftNeg (d : SourceDatum) :
    realizeSource (shiftNeg d) = realizeSource d :=
  (realizeSource_eq_iff _ _).mpr (Or.inr rfl)

/-- Each actual realization fiber is precisely its source datum and its simultaneous sign transform. -/
theorem realizeSource_fiber (d : SourceDatum) :
    {e | realizeSource e = realizeSource d} = {d, shiftNeg d} := by
  ext e
  simp only [Set.mem_ofPred_eq, realizeSource_eq_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every actual regular spinor is realized by literal positive-density, four-pi-angle and determinant-one matrix coordinates. -/
theorem realizeSource_surjective : Function.Surjective realizeSource := by
  intro q
  obtain ⟨d, hd⟩ := datumHomeomorph.surjective (inverseDatum q)
  refine ⟨d, ?_⟩
  change toDatum d = inverseDatum q at hd
  change realize (toDatum d) = q
  rw [hd, realize_inverseDatum]

end FoliationQM.SourcePolarRealization
