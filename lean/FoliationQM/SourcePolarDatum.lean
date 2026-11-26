module
public import FoliationQM.PolarAmplitudeTopology
public import FoliationQM.PolarDatumTopology
public import FoliationQM.ChiralAngleCircle

/-!
# Natural source polar coordinates and their simultaneous sign operation

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The literal
source data consist of a positive density, the full chiral angle modulo
four pi, and a determinant-one complex two-by-two matrix. They carry the
ordinary product of the inherited subtype and angle-quotient topologies.

The existing amplitude homeomorphism and half-angle circle homeomorphism
give an explicit homeomorphism to the independently topologized concrete
polar datum. Adding two pi to the angle while negating the matrix is
exactly simultaneous amplitude/matrix negation under this homeomorphism.
The operation is a free continuous involution. No global real angle,
abstract spin-group identification, or covering theorem is asserted here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SourcePolarDatum
open SpinorMatrix PolarSignQuotient PolarAmplitudeTopology ChiralAngleCircle

/-- Actual determinant-one complex matrices with their natural matrix-subspace topology. -/
abbrev SpecialLinearMatrix := {A : Mat2 // A.det = 1}

/-- Literal source coordinates with the natural product topology: positive density, four-pi angle, and actual determinant-one matrix. -/
abbrev SourceDatum := PositiveDensity × Angle × SpecialLinearMatrix

/-- Convert literal source coordinates to actual nonzero amplitude and determinant-one matrix data. -/
def toDatum (d : SourceDatum) : Datum where
  t := (amplitude (d.1, phaseEquiv d.2.1) : ℂ)
  A := d.2.2.val
  t_ne_zero := (amplitude (d.1, phaseEquiv d.2.1)).property
  det_eq_one := d.2.2.property

/-- Recover literal density, four-pi angle, and matrix coordinates from the actual amplitude datum. -/
def ofDatum (d : Datum) : SourceDatum :=
  ((coordinates ⟨d.t, d.t_ne_zero⟩).1,
    phaseEquiv.symm (coordinates ⟨d.t, d.t_ne_zero⟩).2, ⟨d.A, d.det_eq_one⟩)

/-- The actual amplitude in source coordinates is the positive density square root times the half-angle unit phase. -/
theorem toDatum_t (d : SourceDatum) :
    (toDatum d).t = (Real.sqrt (d.1 : ℝ) : ℂ) * (phaseEquiv d.2.1 : ℂ) := rfl

/-- The actual matrix coordinate is preserved exactly by conversion from source coordinates. -/
theorem toDatum_A (d : SourceDatum) : (toDatum d).A = (d.2.2 : Mat2) := rfl

/-- Recovering source coordinates from their actual amplitude datum returns all three original coordinates. -/
theorem ofDatum_toDatum (d : SourceDatum) : ofDatum (toDatum d) = d := by
  change ((coordinates (amplitude (d.1, phaseEquiv d.2.1))).1,
    phaseEquiv.symm (coordinates (amplitude (d.1, phaseEquiv d.2.1))).2, d.2.2) = d
  rw [coordinates_amplitude]
  simp

/-- The actual datum is recovered exactly from its density, angle-circle and matrix coordinates. -/
theorem toDatum_ofDatum (d : Datum) : toDatum (ofDatum d) = d := by
  apply datum_ext
  · change (amplitude ((coordinates ⟨d.t, d.t_ne_zero⟩).1,
      phaseEquiv (phaseEquiv.symm (coordinates ⟨d.t, d.t_ne_zero⟩).2)) : ℂ) = d.t
    rw [phaseEquiv.apply_symm_apply]
    exact congrArg Subtype.val (amplitude_coordinates ⟨d.t, d.t_ne_zero⟩)
  · rfl

/-- The actual source-to-amplitude conversion is continuous for the ordinary source product topology and the natural datum topology. -/
theorem continuous_toDatum : Continuous toDatum := by
  apply PolarDatumTopology.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.comp (continuous_amplitude.comp
      (continuous_fst.prodMk (phaseEquiv.continuous.comp (continuous_fst.comp continuous_snd))))
  · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)

/-- The actual inverse source-coordinate map is continuous in the independently defined natural topologies. -/
theorem continuous_ofDatum : Continuous ofDatum := by
  have ht : Continuous (fun d : Datum => (⟨d.t, d.t_ne_zero⟩ : NonzeroComplex)) :=
    PolarDatumTopology.continuous_t.subtype_mk _
  have hc := continuous_coordinates.comp ht
  exact hc.fst.prodMk ((phaseEquiv.symm.continuous.comp hc.snd).prodMk
    (PolarDatumTopology.continuous_A.subtype_mk _))

/-- The literal positive-density, four-pi-angle, determinant-one-matrix data are homeomorphic to the actual amplitude datum with its natural topology. -/
def datumHomeomorph : SourceDatum ≃ₜ Datum where
  toFun := toDatum
  invFun := ofDatum
  left_inv := ofDatum_toDatum
  right_inv := toDatum_ofDatum
  continuous_toFun := continuous_toDatum
  continuous_invFun := continuous_ofDatum

/-- The source coordinate homeomorphism evaluates to the actual datum conversion. -/
theorem datumHomeomorph_apply (d : SourceDatum) : datumHomeomorph d = toDatum d := rfl

/-- The inverse source coordinate homeomorphism evaluates to the actual density, angle and matrix recovery. -/
theorem datumHomeomorph_symm_apply (d : Datum) : datumHomeomorph.symm d = ofDatum d := rfl

/-- The literal source sign operation preserves density, adds two pi to the full angle, and negates the actual determinant-one matrix. -/
def shiftNeg (d : SourceDatum) : SourceDatum :=
  (d.1, d.2.1 + ((2 * Real.pi : ℝ) : Angle),
    ⟨-(d.2.2 : Mat2), by simp [Matrix.det_neg, d.2.2.property]⟩)

/-- The literal two-pi angle shift and matrix negation become exactly simultaneous amplitude and matrix negation. -/
theorem toDatum_shiftNeg (d : SourceDatum) :
    toDatum (shiftNeg d) = negDatum (toDatum d) := by
  apply datum_ext
  · change (amplitude (d.1, phaseEquiv (d.2.1 + ((2 * Real.pi : ℝ) : Angle))) : ℂ) =
      -(amplitude (d.1, phaseEquiv d.2.1) : ℂ)
    rw [phaseEquiv_shift]
    exact congrArg Subtype.val (amplitude_antipode d.1 (phaseEquiv d.2.1))
  · rfl

/-- The literal source sign operation is an involution because its actual amplitude-data operation is simultaneous negation. -/
theorem shiftNeg_involutive (d : SourceDatum) : shiftNeg (shiftNeg d) = d := by
  apply datumHomeomorph.injective
  change toDatum (shiftNeg (shiftNeg d)) = toDatum d
  rw [toDatum_shiftNeg, toDatum_shiftNeg, negDatum_involutive]

/-- The literal source sign operation has no fixed point, as its corresponding nonzero amplitude negation has none. -/
theorem shiftNeg_ne_self (d : SourceDatum) : shiftNeg d ≠ d := by
  intro h
  have he := congrArg toDatum h
  rw [toDatum_shiftNeg] at he
  exact negDatum_ne_self (toDatum d) he

/-- The actual two-pi angle translation and matrix negation are continuous in the natural source product topology. -/
theorem continuous_shiftNeg : Continuous shiftNeg := by
  exact continuous_fst.prodMk (((continuous_fst.comp continuous_snd).add continuous_const).prodMk
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).neg.subtype_mk _))

/-- The actual source sign involution is a homeomorphism of the natural source datum space. -/
def shiftNegHomeomorph : SourceDatum ≃ₜ SourceDatum where
  toFun := shiftNeg
  invFun := shiftNeg
  left_inv := shiftNeg_involutive
  right_inv := shiftNeg_involutive
  continuous_toFun := continuous_shiftNeg
  continuous_invFun := continuous_shiftNeg

/-- The source sign homeomorphism evaluates to the literal two-pi angle shift and matrix negation. -/
theorem shiftNegHomeomorph_apply (d : SourceDatum) : shiftNegHomeomorph d = shiftNeg d := rfl

end FoliationQM.SourcePolarDatum
