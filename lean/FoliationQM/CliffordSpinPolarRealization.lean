module
public import FoliationQM.CliffordSpinPolarDatum
public import FoliationQM.SourcePolarRealization
public import FoliationQM.CliffordSpinRepresentation

/-!
# Actual Clifford Spin polar realization and its exact sign fibers

Source scope: the actual Spin polar coordinates of v13 `prop:takabayasi`
and `eq:takabayasi_polar`. The data retain positive density, the full
four-pi chiral angle circle, and the literal generated Clifford Spin
group. The existing concrete realization is composed with the already
proved actual Pauli identification; its physical formula is proved to be
the positive square-root amplitude times the chiral matrix times the
universal Clifford Dirac representation acting on the fixed rest spinor.

The actual scalar-pseudoscalar density and determinant recover the
prescribed scalar coordinates. Every strictly regular spinor is realized,
and every fiber is exactly the two genuine source representatives related
by the simultaneous two-pi shift and multiplication by the Clifford
negative identity. The principal inverse formulas retain their strict
principal-angle hypothesis. No global real phase or individual global
Spin representative is selected, and dynamics remain separate.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CliffordSpinPolarRealization
open CliffordSpinPolarDatum CliffordSpinMap
open DiracMatrices PolarSignQuotient PolarAmplitudeTopology ChiralAngleCircle
open SpinorRegularity SpinorMatrix

/-- Actual polar realization of positive density, the four-pi angle, and a genuine Clifford Spin element. -/
def realizeSource (d : SourceDatum) : RegularSpinor :=
  SourcePolarRealization.realizeSource (sourceHomeomorph d)

/-- The actual Clifford polar realization agrees exactly with the established matrix realization through the proved Pauli coordinate identification. -/
theorem realizeSource_eq_matrix (d : SourceDatum) :
    realizeSource d = SourcePolarRealization.realizeSource (sourceHomeomorph d) := rfl

/-- For every angle-circle value the realized spinor is the actual chiral polar expression with the universal Clifford Dirac representation. -/
theorem realizeSource_polarOnAngle (d : SourceDatum) :
    (realizeSource d).val = polarOnAngle (d.1 : ℝ) d.2.1
      (CliffordMinkowski.dirac d.2.2.val) := by
  rw [realizeSource_eq_matrix, SourcePolarRealization.realizeSource_polarOnAngle,
    CliffordSpinMap.dirac_eq_spin]
  rfl

/-- On every real angle representative the actual Clifford polar map equals the source polar spinor with its literal Dirac representation. -/
theorem realizeSource_coe (rho : PositiveDensity) (beta : ℝ) (s : Spin) :
    (realizeSource (rho, (beta : Angle), s)).val =
      PolarSpinorBilinears.polarSpinor (rho : ℝ) beta (CliffordMinkowski.dirac s.val) := by
  rw [realizeSource_polarOnAngle, polarOnAngle_coe]

/-- The real-angle formula is the actual positive square-root amplitude, chiral matrix, and universal Clifford representation acting on the fixed rest spinor. -/
theorem realizeSource_explicit (rho : PositiveDensity) (beta : ℝ) (s : Spin) :
    (realizeSource (rho, (beta : Angle), s)).val =
      (Real.sqrt (rho : ℝ) : ℂ) •
        ((ChiralMatrix.chiral beta * CliffordMinkowski.dirac s.val).mulVec restSpinor) :=
  realizeSource_coe rho beta s

/-- The actual Clifford polar realization is continuous in the unchanged product and regular-spinor topologies. -/
theorem continuous_realizeSource : Continuous realizeSource :=
  SourcePolarRealization.continuous_realizeSource.comp sourceHomeomorph.continuous

/-- The invariant scalar-pseudoscalar density of the actual realization equals the prescribed positive density. -/
theorem density_realizeSource (d : SourceDatum) :
    invariantDensity (realizeSource d).val = (d.1 : ℝ) :=
  SourcePolarRealization.density_realizeSource (sourceHomeomorph d)

/-- The determinant of the realized spinor encoding is the prescribed density times the square of the actual half-angle phase. -/
theorem determinant_realizeSource (d : SourceDatum) :
    Matrix.det (SpinorMatrix.toMatrix (realizeSource d).val) =
      (d.1 : ℂ) * (phaseEquiv d.2.1 : ℂ)^2 :=
  SourcePolarRealization.determinant_realizeSource (sourceHomeomorph d)

/-- On a real angle representative the actual determinant is the positive density times the full-angle complex exponential. -/
theorem determinant_realizeSource_coe (rho : PositiveDensity) (beta : ℝ) (s : Spin) :
    Matrix.det (SpinorMatrix.toMatrix (realizeSource (rho, (beta : Angle), s)).val) =
      (rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ)) :=
  SourcePolarRealization.determinant_realizeSource_coe rho beta (CliffordSpinMap.toMatrix s)

/-- Principal determinant-phase reconstruction recovers the actual input angle on its strict principal interval. -/
theorem determinantPhase_realizeSource_coe (rho : PositiveDensity) (beta : ℝ) (s : Spin)
    (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    RegularPolarReconstruction.determinantPhase
      (realizeSource (rho, (beta : Angle), s)).val = beta :=
  SourcePolarRealization.determinantPhase_realizeSource_coe rho beta
    (CliffordSpinMap.toMatrix s) hbeta

/-- Principal matrix reconstruction recovers precisely the genuine Spin element's Pauli matrix on the principal angle interval. -/
theorem normalizedMatrix_realizeSource_coe (rho : PositiveDensity) (beta : ℝ) (s : Spin)
    (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    RegularPolarReconstruction.normalizedMatrix
      (realizeSource (rho, (beta : Angle), s)).val = (CliffordSpinMap.toMatrix s).val :=
  SourcePolarRealization.normalizedMatrix_realizeSource_coe rho beta
    (CliffordSpinMap.toMatrix s) hbeta

/-- Two actual Clifford polar data realize the same spinor exactly when they agree or differ by the literal two-pi shift and Clifford sign. -/
theorem realizeSource_eq_iff (d e : SourceDatum) :
    realizeSource d = realizeSource e ↔ d = e ∨ d = shiftNeg e := by
  rw [realizeSource_eq_matrix, realizeSource_eq_matrix,
    SourcePolarRealization.realizeSource_eq_iff, ← sourceHomeomorph_shiftNeg]
  exact or_congr sourceHomeomorph.injective.eq_iff sourceHomeomorph.injective.eq_iff

/-- Exact actual Spin polar fibers have equal density and either equal angle and Spin or the simultaneous two-pi angle shift and multiplication by the genuine Clifford negative identity. -/
theorem realizeSource_coordinate_fibers (d e : SourceDatum) :
    realizeSource d = realizeSource e ↔ (d.1 : ℝ) = (e.1 : ℝ) ∧
      ((d.2.1 = e.2.1 ∧ d.2.2 = e.2.2) ∨
       (d.2.1 = e.2.1 + ((2 * Real.pi : ℝ) : Angle) ∧
         d.2.2 = CliffordSpinEquivalence.negativeOne * e.2.2)) := by
  rw [realizeSource_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨hrho, h | h⟩
    · exact Or.inl (Prod.ext (Subtype.ext hrho) (Prod.ext h.1 h.2))
    · exact Or.inr (Prod.ext (Subtype.ext hrho) (Prod.ext h.1 h.2))

/-- The literal simultaneous angle shift and Clifford sign leave the actual realized spinor unchanged. -/
theorem realizeSource_shiftNeg (d : SourceDatum) :
    realizeSource (shiftNeg d) = realizeSource d :=
  (realizeSource_eq_iff _ _).mpr (Or.inr rfl)

/-- Every actual realization fiber is precisely its representative and the genuine simultaneous sign transform. -/
theorem realizeSource_fiber (d : SourceDatum) :
    {e | realizeSource e = realizeSource d} = {d, shiftNeg d} := by
  ext e
  simp only [Set.mem_ofPred_eq, realizeSource_eq_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every strictly regular spinor is realized by genuine positive-density, four-pi-angle, and actual Clifford Spin data. -/
theorem realizeSource_surjective : Function.Surjective realizeSource :=
  SourcePolarRealization.realizeSource_surjective.comp sourceHomeomorph.surjective

end FoliationQM.CliffordSpinPolarRealization
