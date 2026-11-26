module
public import FoliationQM.SpecialLinearSpin
public import FoliationQM.RealLorentzFrame

/-!
# Constructed real Lorentz-frame coefficients of the concrete spin representation

Source: v13 `eq:tetrad_rotor_map` and the actual frame in
`prop:takabayasi`. The four coefficients are extracted from entries of the
actual Dirac-adjoint sandwich of the explicit two-by-two representation.
Their real gamma expansion is proved by exact finite matrix algebra for
all matrix inputs. Determinant one identifies the actual Dirac adjoint
with the actual matrix inverse, giving the required conjugated frame.

No real frame expansion or orthonormality is supplied as a premise.
The coefficients refer to the upper-index gamma basis in signature
(+---); physical lower-index columns are obtained by the existing metric
conversions. This construction does not classify the full Lorentz image
or identify it with an abstract Clifford spin group.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpecialLinearFrame
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin RealLorentzFrame

/-- The four real entry projections that recover coefficients of the upper-index Dirac gamma basis. -/
def coefficients (X : Mat) : Covector :=
  ![(X 0 0).re, (X 0 3).re, -(X 0 3).im, (X 0 2).re]

/-- The actual real coefficients extracted from the explicit Dirac-adjoint sandwich for each upper-index basis matrix. -/
def frame (A : Mat2) (a : Fin 4) : Covector :=
  coefficients (spin A * gamma a * diracAdjoint (spin A))

/-- Extracting coefficients from an actual real gamma expansion recovers its original real vector. -/
theorem coefficients_gammaExpansion (v : Covector) : coefficients (gammaExpansion v) = v := by
  rw [gammaExpansion_explicit]
  ext a
  fin_cases a <;> simp [coefficients]

private def vectorTable (t z w : ℂ) : Mat :=
  !![t,0,z,w; 0,t,star w,-z; -z,-w,-t,0; -star w,z,0,-t]

private theorem vectorTable_real (t z w : ℂ) (ht : t.im=0) (hz : z.im=0) :
    vectorTable t z w = gammaExpansion ![t.re,w.re,-w.im,z.re] := by
  rw [gammaExpansion_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [vectorTable, ht, hz]

set_option maxHeartbeats 1000000 in
private theorem sandwich_shape (A : Mat2) (a : Fin 4) :
    spin A * gamma a * diracAdjoint (spin A) =
      vectorTable ((spin A * gamma a * diracAdjoint (spin A)) 0 0)
        ((spin A * gamma a * diracAdjoint (spin A)) 0 2)
        ((spin A * gamma a * diracAdjoint (spin A)) 0 3) := by
  rw [spin_diracAdjoint]
  simp only [Matrix.adjugate_fin_two]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [vectorTable, spin, weylDual, gamma, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 500000 in
private theorem sandwich_real (A : Mat2) (a : Fin 4) :
    ((spin A * gamma a * diracAdjoint (spin A)) 0 0).im = 0 ∧
    ((spin A * gamma a * diracAdjoint (spin A)) 0 2).im = 0 := by
  rw [spin_diracAdjoint]
  simp only [Matrix.adjugate_fin_two]
  fin_cases a <;> constructor <;>
    simp [spin, weylDual, gamma, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual explicit Dirac-adjoint sandwich has a real gamma expansion for every complex two-by-two matrix, without a determinant premise. -/
theorem sandwich_expansion (A : Mat2) (a : Fin 4) :
    spin A * gamma a * diracAdjoint (spin A) = gammaExpansion (frame A a) := by
  have hr := sandwich_real A a
  exact (sandwich_shape A a).trans (vectorTable_real _ _ _ hr.1 hr.2)

/-- A determinant-one input gives the actual inverse conjugation as the real gamma expansion of the constructed frame, with no supplied frame premise. -/
theorem frame_expansion (A : Mat2) (hdet : A.det = 1) (a : Fin 4) :
    spin A * gamma a * (spin A)⁻¹ = gammaExpansion (frame A a) := by
  rw [spin_inverse A hdet]
  exact sandwich_expansion A a
end FoliationQM.SpecialLinearFrame
