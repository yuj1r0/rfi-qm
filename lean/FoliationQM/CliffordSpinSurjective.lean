module
public import FoliationQM.CliffordSpinMap

/-!
# Constructive surjectivity of the genuine Clifford Spin representation

Source scope: the abstract Clifford identification supporting v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. Four explicit products of
negative unit Minkowski vectors represent the real and imaginary upper
and lower transvections. Their membership in Mathlib's literal spinGroup
uses the already proved generated-vector and normalization conditions;
it is not inferred from a normalizer equation or a supplied image claim.

A complex transvection is the product of its real and imaginary parts.
Mathlib's SL2 transvection induction then proves that the actual Spin
homomorphism is onto every determinant-one complex two-by-two matrix.
This is an algebraic surjectivity statement. Topological, smooth, and
universal-cover identifications are separate obligations.
-/

@[expose] public section
noncomputable section
open scoped Matrix
namespace FoliationQM.CliffordSpinSurjective
open CliffordMinkowski SpinLorentzPauli SourcePolarDatum
open CliffordSpinGenerators CliffordSpinMap

/-- The genuine Spin pair of (0,−1,0,0) and (−r/2,1,0,−r/2), both of quadratic value −1. -/
def upperRealLift (r : ℝ) : Spin :=
  pair quadratic ![0,-1,0,0] ![-r/2,1,0,-r/2] (by
    norm_num [quadratic_apply])

/-- The genuine Spin pair of (0,0,−1,0) and (r/2,0,1,r/2), both of quadratic value −1. -/
def upperImagLift (r : ℝ) : Spin :=
  pair quadratic ![0,0,-1,0] ![r/2,0,1,r/2] (by
    norm_num [quadratic_apply])

/-- The genuine Spin pair of (0,−1,0,0) and (−r/2,1,0,r/2), both of quadratic value −1. -/
def lowerRealLift (r : ℝ) : Spin :=
  pair quadratic ![0,-1,0,0] ![-r/2,1,0,r/2] (by
    norm_num [quadratic_apply]
    ring)

/-- The genuine Spin pair of (0,0,−1,0) and (−r/2,0,1,r/2), both of quadratic value −1. -/
def lowerImagLift (r : ℝ) : Spin :=
  pair quadratic ![0,0,-1,0] ![-r/2,0,1,r/2] (by
    norm_num [quadratic_apply]
    ring)


/-- The first actual Clifford pair represents the upper transvection with real coefficient. -/
theorem toMatrix_upperRealLift (r : ℝ) :
    toMatrix (upperRealLift r) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (r : ℂ) := by
  apply Subtype.ext
  rw [upperRealLift, toMatrix_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.SpecialLinearGroup.transvection_coe]

/-- The second actual Clifford pair represents the upper transvection with imaginary coefficient. -/
theorem toMatrix_upperImagLift (r : ℝ) :
    toMatrix (upperImagLift r) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide)
        (Complex.I * (r : ℂ)) := by
  apply Subtype.ext
  rw [upperImagLift, toMatrix_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.SpecialLinearGroup.transvection_coe]

/-- The third actual Clifford pair represents the lower transvection with real coefficient. -/
theorem toMatrix_lowerRealLift (r : ℝ) :
    toMatrix (lowerRealLift r) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (r : ℂ) := by
  apply Subtype.ext
  rw [lowerRealLift, toMatrix_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.SpecialLinearGroup.transvection_coe] <;> ring

/-- The fourth actual Clifford pair represents the lower transvection with imaginary coefficient. -/
theorem toMatrix_lowerImagLift (r : ℝ) :
    toMatrix (lowerImagLift r) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide)
        (Complex.I * (r : ℂ)) := by
  apply Subtype.ext
  rw [lowerImagLift, toMatrix_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.SpecialLinearGroup.transvection_coe] <;> ring_nf


/-- Every complex SL2 transvection is represented by a product of the actual normalized Clifford pairs. -/
theorem exists_transvection_lift (i j : Fin 2) (hij : i ≠ j) (z : ℂ) :
    ∃ s : Spin, toMatrix s = Matrix.SpecialLinearGroup.transvection hij z := by
  have hz : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    apply Complex.ext <;> simp
  fin_cases i
  · have hj : j = 1 := by fin_cases j <;> simp_all
    subst j
    refine ⟨upperRealLift z.re * upperImagLift z.im, ?_⟩
    rw [map_mul, toMatrix_upperRealLift, toMatrix_upperImagLift]
    have he := (Matrix.SpecialLinearGroup.transvection_add hij
      (z.re : ℂ) (Complex.I * (z.im : ℂ))).symm
    rw [hz] at he
    exact he
  · have hj : j = 0 := by fin_cases j <;> simp_all
    subst j
    refine ⟨lowerRealLift z.re * lowerImagLift z.im, ?_⟩
    rw [map_mul, toMatrix_lowerRealLift, toMatrix_lowerImagLift]
    have he := (Matrix.SpecialLinearGroup.transvection_add hij
      (z.re : ℂ) (Complex.I * (z.im : ℂ))).symm
    rw [hz] at he
    exact he

/-- The genuine Clifford Spin homomorphism is onto the entire existing determinant-one matrix group. -/
theorem toMatrix_surjective : Function.Surjective toMatrix := by
  intro A
  exact Matrix.SL2.transvection_induction
    (fun A => ∃ s : Spin, toMatrix s = A)
    exists_transvection_lift
    (fun A B ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s * t, by
      rw [map_mul, hs, ht]
      rfl⟩) A

end FoliationQM.CliffordSpinSurjective
