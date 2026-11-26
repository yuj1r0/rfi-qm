module
public import FoliationQM.PolarMatrixFibers
public import FoliationQM.RegularPolarReconstruction

/-!
# The explicit polar sign quotient and regular-spinor equivalence

Source: v13 `prop:takabayasi` and `eq:takabayasi_polar`. A concrete datum
contains a nonzero complex amplitude and an actual determinant-one
complex two-by-two matrix. The sign relation is defined explicitly as
literal equality or simultaneous negation of both coordinates. Its setoid
laws and lack of fixed points are proved before identifying its exact fibers
under the actual spinor realization. The relation is not defined through
equality of realized spinors.

The genuine quotient maps to the subtype of strictly invariant-regular
spinors. Its explicit inverse is the class of the amplitude and normalized
matrix constructed in RegularPolarReconstruction. Both inverse identities
are proved, yielding an algebraic Equiv and bijectivity. This is the precise
complex-amplitude sign quotient; the four-pi angle-circle and integer angle
fiber descriptions are separate bridges. No topological or smooth quotient
equivalence, globally continuous real angle, abstract Spin classification,
or Lorentz covering result is asserted here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarSignQuotient
open DiracMatrices SpinorMatrix SpinorRegularity PolarMatrixFibers RegularPolarReconstruction

/-- Concrete polar data consist of a nonzero complex amplitude and an actual determinant-one two-by-two matrix. -/
structure Datum where
  /-- The nonzero complex amplitude containing magnitude and half-angle phase. -/
  t : ℂ
  /-- The actual determinant-one matrix. -/
  A : Mat2
  /-- The amplitude is nonzero. -/
  t_ne_zero : t ≠ 0
  /-- The matrix has determinant one. -/
  det_eq_one : A.det = 1

/-- Concrete polar data are equal when their actual amplitude and matrix agree. -/
@[ext]
theorem datum_ext {d e : Datum} (ht : d.t = e.t) (hA : d.A = e.A) : d = e := by
  cases d
  cases e
  simp_all

/-- The simultaneous sign transformation negates both the actual amplitude and actual matrix. -/
def negDatum (d : Datum) : Datum where
  t := -d.t
  A := -d.A
  t_ne_zero := neg_ne_zero.mpr d.t_ne_zero
  det_eq_one := by simp [Matrix.det_neg, d.det_eq_one]

/-- Applying the simultaneous sign transformation twice recovers the original concrete datum. -/
theorem negDatum_involutive (d : Datum) : negDatum (negDatum d) = d := by
  apply datum_ext <;> simp [negDatum]

/-- The simultaneous sign action has no fixed point because its actual complex amplitude is nonzero. -/
theorem negDatum_ne_self (d : Datum) : negDatum d ≠ d := by
  intro h
  have ht := congrArg Datum.t h
  change -d.t = d.t at ht
  apply d.t_ne_zero
  linear_combination -(1/2 : ℂ)*ht

/-- The explicit polar sign relation identifies equal data or the simultaneous sign transform, independently of their spinor images. -/
def Related (d e : Datum) : Prop := d = e ∨ d = negDatum e

/-- The explicit relation has exactly the equality or simultaneous sign-reversal conditions on its actual two coordinates. -/
theorem related_iff_coordinates (d e : Datum) :
    Related d e ↔ (d.t=e.t ∧ d.A=e.A) ∨ (d.t= -e.t ∧ d.A= -e.A) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨congrArg Datum.t h, congrArg Datum.A h⟩
    · exact Or.inr ⟨congrArg Datum.t h, congrArg Datum.A h⟩
  · rintro (⟨ht,hA⟩ | ⟨ht,hA⟩)
    · exact Or.inl (datum_ext ht hA)
    · exact Or.inr (datum_ext ht hA)

/-- The explicit sign relation is reflexive. -/
theorem related_refl (d : Datum) : Related d d := Or.inl rfl

/-- The explicit sign relation is symmetric because the simultaneous sign transformation is an involution. -/
theorem related_symm {d e : Datum} (h : Related d e) : Related e d := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, negDatum_involutive])

/-- Two successive explicit sign identifications again give an equal datum or one simultaneous sign transform. -/
theorem related_trans {d e f : Datum} (hde : Related d e) (hef : Related e f) : Related d f := by
  rcases hde with hde | hde <;> rcases hef with hef | hef
  · exact Or.inl (hde.trans hef)
  · exact Or.inr (hde.trans hef)
  · exact Or.inr (by rw [hde, hef])
  · exact Or.inl (by rw [hde, hef, negDatum_involutive])

/-- The actual setoid is built from the explicit simultaneous sign relation. -/
def signSetoid : Setoid Datum where
  r := Related
  iseqv := ⟨related_refl, related_symm, related_trans⟩

/-- The quotient of concrete nonzero polar data by their explicit simultaneous sign transformation. -/
abbrev PolarQuotient := Quotient signSetoid

/-- The target consists of actual spinors in the strict invariant regular domain. -/
abbrev RegularSpinor := {psi : Spinor // Regular psi}

/-- Realize a concrete polar datum as its actual regular spinor by the inverse matrix encoding. -/
def realize (d : Datum) : RegularSpinor :=
  ⟨parameterSpinor d.t d.A, regular_parameterSpinor d.t d.A d.t_ne_zero d.det_eq_one⟩

/-- Equality of actual realized spinors is proved equivalent to the independently defined explicit sign relation. -/
theorem realize_eq_iff_related (d e : Datum) : realize d = realize e ↔ Related d e := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change parameterSpinor d.t d.A = parameterSpinor e.t e.A at he
    rw [parameterSpinor_fibers_iff d.t e.t d.A e.A d.t_ne_zero e.t_ne_zero
      d.det_eq_one e.det_eq_one] at he
    rcases he with ⟨ht,hA⟩ | ⟨ht,hA⟩
    · exact Or.inl (datum_ext ht hA)
    · exact Or.inr (datum_ext ht hA)
  · rintro (h | h)
    · rw [h]
    · apply Subtype.ext
      change parameterSpinor d.t d.A = parameterSpinor e.t e.A
      rw [h]
      exact parameterSpinor_neg_neg e.t e.A

/-- The actual regular-spinor realization descends to the explicit sign quotient. -/
def toRegular : PolarQuotient → RegularSpinor :=
  Quotient.lift realize (fun d e h => (realize_eq_iff_related d e).mpr h)

/-- On a concrete representative the quotient realization is its actual reconstructed spinor. -/
theorem toRegular_mk (d : Datum) : toRegular (Quotient.mk signSetoid d) = realize d := rfl

/-- Equality of two explicit quotient representatives is exactly equality or simultaneous amplitude/matrix sign reversal. -/
theorem quotient_mk_eq_iff (d e : Datum) :
    Quotient.mk signSetoid d = Quotient.mk signSetoid e ↔ Related d e := Quotient.eq

/-- The quotient identifies the actual simultaneous sign transform with its original datum. -/
theorem quotient_negDatum (d : Datum) :
    Quotient.mk signSetoid (negDatum d) = Quotient.mk signSetoid d := Quotient.sound (Or.inr rfl)

/-- The previously constructed amplitude and normalized matrix give explicit nonzero polar data for every regular spinor. -/
def inverseDatum (psi : RegularSpinor) : Datum where
  t := amplitudePhase psi.val
  A := normalizedMatrix psi.val
  t_ne_zero := amplitudePhase_ne_zero psi.property
  det_eq_one := normalizedMatrix_det psi.property

/-- Realization of the explicit reconstructed datum returns the original actual regular spinor. -/
theorem realize_inverseDatum (psi : RegularSpinor) : realize (inverseDatum psi) = psi := by
  apply Subtype.ext
  apply toMatrix_injective
  change toMatrix (parameterSpinor (amplitudePhase psi.val) (normalizedMatrix psi.val)) = toMatrix psi.val
  rw [toMatrix_parameterSpinor, amplitudePhase_smul_normalizedMatrix psi.property]

/-- The inverse map sends a regular spinor to the quotient class of its explicit reconstructed polar datum. -/
def ofRegular (psi : RegularSpinor) : PolarQuotient := Quotient.mk signSetoid (inverseDatum psi)

/-- Realization after the explicit quotient inverse returns the original regular spinor. -/
theorem toRegular_ofRegular (psi : RegularSpinor) : toRegular (ofRegular psi) = psi :=
  realize_inverseDatum psi

/-- The explicit reconstruction returns the original sign class, using the proved exact fiber characterization. -/
theorem ofRegular_toRegular (q : PolarQuotient) : ofRegular (toRegular q) = q := by
  refine Quotient.inductionOn q ?_
  intro d
  apply Quotient.sound
  exact (realize_eq_iff_related _ _).mp (realize_inverseDatum (realize d))

/-- The actual explicit sign quotient is equivalent to the subtype of all regular spinors, with the constructed inverse. -/
def regularEquiv : PolarQuotient ≃ RegularSpinor where
  toFun := toRegular
  invFun := ofRegular
  left_inv := ofRegular_toRegular
  right_inv := toRegular_ofRegular

/-- The quotient realization is bijective because both actual inverse identities have been proved. -/
theorem toRegular_bijective : Function.Bijective toRegular := regularEquiv.bijective

end FoliationQM.PolarSignQuotient
