module
public import FoliationQM.SpinLorentzKernel
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Lifting the independent planar Lorentz stabilizer

Source scope: the proper Lorentz-frame representation in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. A real matrix preserving
(+---), with determinant one and fixed time and third spatial axes, is
proved to have an actual two-dimensional proper rotation block. No
represented-image assumption enters this normal form.

A complex square root of the unit rotation phase produces a diagonal
special linear matrix. Its determinant and its full Hermitian Pauli
sandwich are checked directly, yielding an actual spin lift of every
independently specified proper future Lorentz element in this stabilizer.
This is the planar step of the constructive image theorem; no global
choice of a continuous square root or covering statement is asserted.
-/

@[expose] public section

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzPlanar
open SpinorMatrix SourcePolarDatum SpinLorentzAction SpinLorentzOrientation
open LorentzMatrixGroup SpinLorentzPauli

private theorem planar_shape (M : Mat4) (hm : M.transpose * eta * M = eta)
    (ht : M *ᵥ (Pi.single 0 1) = Pi.single 0 1)
    (hz : M *ᵥ (Pi.single 3 1) = Pi.single 3 1) :
    M = !![1,0,0,0; 0,M 1 1,M 1 2,0; 0,M 2 1,M 2 2,0; 0,0,0,1] := by
  have hc0 (i : Fin 4) : M i 0 = (Pi.single 0 1 : Covector) i := by
    have he := congrFun ht i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he
  have hc3 (i : Fin 4) : M i 3 = (Pi.single 3 1 : Covector) i := by
    have he := congrFun hz i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he
  have hr0 (i : Fin 4) : M 0 i = (Pi.single 0 1 : Covector) i := by
    have he := minkowski_mulVec_of_metric M hm (Pi.single 0 1) (Pi.single i 1)
    rw [ht] at he
    fin_cases i <;> simpa [minkowski, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he
  have hr3 (i : Fin 4) : M 3 i = (Pi.single 3 1 : Covector) i := by
    have he := minkowski_mulVec_of_metric M hm (Pi.single 3 1) (Pi.single i 1)
    rw [hz] at he
    fin_cases i <;> simpa [minkowski, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc0, hc3, hr0, hr3]

private theorem block_det (a b c d : ℝ) :
    (!![1,0,0,0; 0,a,b,0; 0,c,d,0; 0,0,0,1] : Mat4).det = a*d-b*c := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, sub_eq_add_neg]

/-- Independent metric preservation, determinant one, and two fixed axes force
exactly the proper planar rotation block and its unit-circle equation. -/
theorem planar_normal_form (M : Mat4) (hm : M.transpose * eta * M = eta)
    (hd : M.det = 1) (ht : M *ᵥ (Pi.single 0 1) = Pi.single 0 1)
    (hz : M *ᵥ (Pi.single 3 1) = Pi.single 3 1) :
    M = !![1,0,0,0; 0,M 1 1,M 1 2,0; 0,-M 1 2,M 1 1,0; 0,0,0,1] ∧
      (M 1 1)^2+(M 1 2)^2=1 := by
  have hs := planar_shape M hm ht hz
  have hd2 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 1 := by
    rw [hs, block_det] at hd
    exact hd
  have hr := metric_rows_of_metric M hm
  rw [hs] at hr
  have h11 := congrArg (fun N : Mat4 => N 1 1) hr
  have h12 := congrArg (fun N : Mat4 => N 1 2) hr
  have h22 := congrArg (fun N : Mat4 => N 2 2) hr
  simp [eta, RealLorentzFrame.sign, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] at h11 h12 h22
  have hmem : (!![M 1 1,M 1 2; M 2 1,M 2 2] : Matrix (Fin 2) (Fin 2) ℝ) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
    · simpa [Matrix.det_fin_two] using hd2
  rcases Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.mp hmem with ⟨heq, hneg, hnorm⟩
  refine ⟨?_, hnorm⟩
  calc
    M = _ := hs
    _ = _ := by rw [← heq, show M 2 1 = -M 1 2 by linarith]



private theorem diagonal_sandwich (z : ℂ) (x y : ℝ)
    (hz : z^2=(x:ℂ)+Complex.I*y) (hn : Complex.normSq z = 1) (v : Covector) :
    (!![z,0;0,star z] : Mat2) * pauli v * (!![z,0;0,star z] : Mat2).conjTranspose =
      pauli ((!![1,0,0,0;0,x,y,0;0,-y,x,0;0,0,0,1] : Mat4) *ᵥ v) := by
  have hu : z * star z = 1 := by simpa [hn] using Complex.mul_conj z
  have hc : (star z)^2 = (x:ℂ)-Complex.I*y := by
    have he := congrArg star hz
    simpa [sub_eq_add_neg] using he
  have he : (!![z,0;0,star z] : Mat2) * pauli v *
      (!![z,0;0,star z] : Mat2).conjTranspose =
      !![z*star z*((v 0:ℂ)+v 3), z^2*((v 1:ℂ)-Complex.I*v 2);
        (star z)^2*((v 1:ℂ)+Complex.I*v 2),z*star z*((v 0:ℂ)-v 3)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pauli, Fin.sum_univ_succ] <;> ring
  rw [he, hu, hz, hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring_nf <;> simp

/-- Every real unit-circle rotation block has an actual determinant-one complex
lift, constructed from a complex square root and verified by its Pauli sandwich. -/
theorem exists_diagonal_lift (x y : ℝ) (hxy : x^2+y^2=1) :
    ∃ A : SpecialLinearMatrix,
      lorentzMatrix A.val = !![1,0,0,0;0,x,y,0;0,-y,x,0;0,0,0,1] := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x:ℂ)+Complex.I*y) (by norm_num : 0<2)
  have hxy' : Complex.normSq ((x:ℂ)+Complex.I*y) = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hxy
  have hn2 : Complex.normSq z ^ 2 = 1 := by
    rw [← map_pow, hz, hxy']
  have hn : Complex.normSq z = 1 := by nlinarith [Complex.normSq_nonneg z]
  have hd : (!![z,0;0,star z] : Mat2).det = 1 := by
    simpa [Matrix.det_fin_two, Complex.mul_conj] using congrArg (fun r : ℝ => (r:ℂ)) hn
  refine ⟨⟨!![z,0;0,star z],hd⟩, ?_⟩
  have hv (v : Covector) : lorentzMatrix !![z,0;0,star z] *ᵥ v =
      (!![1,0,0,0;0,x,y,0;0,-y,x,0;0,0,0,1] : Mat4) *ᵥ v := by
    apply pauli_injective
    exact (pauli_sandwich _ hd v).symm.trans (diagonal_sandwich z x y hz hn v)
  ext i j
  have he := congrFun (hv (Pi.single j 1)) i
  fin_cases j <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he


/-- Every independently specified proper future Lorentz matrix fixing the time
and third spatial basis vectors has an actual determinant-one spin lift. -/
theorem exists_planar_lift (L : ProperFutureLorentz)
    (htime : matrix L.val *ᵥ (Pi.single 0 1) = Pi.single 0 1)
    (haxis : matrix L.val *ᵥ (Pi.single 3 1) = Pi.single 3 1) :
    ∃ A : SpecialLinearMatrix, properFutureHom A = L := by
  have hshape := planar_normal_form (matrix L.val) (metric L.val) L.property.1 htime haxis
  obtain ⟨A,hA⟩ := exists_diagonal_lift (matrix L.val 1 1) (matrix L.val 1 2) hshape.2
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply matrix_injective
  exact hA.trans hshape.1.symm

end FoliationQM.SpinLorentzPlanar
