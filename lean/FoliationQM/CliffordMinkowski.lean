module
public import FoliationQM.SpinLorentzPauli
public import FoliationQM.SpinorMatrixSmooth
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star

/-!
# The genuine Minkowski Clifford algebra and its Dirac representation

Source scope: v13 `eq:clifford_anticomm`, `eq:tetrad_rotor_map`, and
`prop:takabayasi`. The quadratic form is the actual real (+---) form.
The universal Clifford representation sends a contravariant coordinate
vector to the lower-index gamma expansion, matching the already proved
physical Lorentz action and standard Pauli signs. Its construction uses
the universal property of Mathlib's Clifford algebra. Faithfulness on
the even algebra and identification of the spin subgroup are separate.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.CliffordMinkowski
open DiracMatrices SpinorMatrix SpecialLinearSpin SpinLorentzPauli

/-- The actual real four-dimensional Minkowski vector space. -/
abbrev Vector := Fin 4 → ℝ

/-- The actual diagonal quadratic form with signature (+---). -/
def quadratic : QuadraticForm ℝ Vector :=
  QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1 -
    QuadraticMap.proj 2 2 - QuadraticMap.proj 3 3

/-- The quadratic form evaluates to the explicit signed sum of squares. -/
theorem quadratic_apply (v : Vector) :
    quadratic v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  simp [quadratic, pow_two]

/-- The Clifford quadratic form is exactly the established Minkowski pairing on the diagonal. -/
theorem quadratic_eq_minkowski (v : Vector) : quadratic v = minkowski v v := by
  simp [quadratic_apply, minkowski, pow_two]

/-- A coordinate vector in the actual Minkowski vector space. -/
def basisVector (a : Fin 4) : Vector := Pi.single a 1

/-- The quadratic value of each coordinate vector is its actual Minkowski sign. -/
theorem quadratic_basisVector (a : Fin 4) :
    quadratic (basisVector a) = RealLorentzFrame.sign a := by
  fin_cases a <;> norm_num [quadratic_apply, basisVector, RealLorentzFrame.sign]

/-- Lower-index gamma expansion of an actual contravariant Minkowski vector. -/
def lowerGamma (v : Vector) : Mat := ∑ a : Fin 4, (v a : ℂ) • gammaLower a

/-- The lower-index expansion retains the literal source gamma matrices on coordinate vectors. -/
theorem lowerGamma_basisVector (a : Fin 4) : lowerGamma (basisVector a) = gammaLower a := by
  simp [lowerGamma, basisVector]

/-- Lower-index gamma expansion preserves vector addition. -/
theorem lowerGamma_add (v w : Vector) : lowerGamma (v+w) = lowerGamma v + lowerGamma w := by
  simp [lowerGamma, add_smul, Finset.sum_add_distrib]

/-- Lower-index gamma expansion preserves real scalar multiplication. -/
theorem lowerGamma_smul (r : ℝ) (v : Vector) : lowerGamma (r • v) = r • lowerGamma v := by
  change (∑ a : Fin 4, ((r*v a : ℝ) : ℂ) • gammaLower a) = r • lowerGamma v
  rw [← IsScalarTower.algebraMap_smul ℂ r (lowerGamma v)]
  simp [lowerGamma, Finset.smul_sum, mul_smul]

/-- The actual lower-index gamma expansion bundled as a real linear map. -/
def lowerGammaLM : Vector →ₗ[ℝ] Mat where
  toFun := lowerGamma
  map_add' := lowerGamma_add
  map_smul' := lowerGamma_smul

/-- The bundled map evaluates to the literal lower-index gamma sum. -/
theorem lowerGammaLM_apply (v : Vector) : lowerGammaLM v = lowerGamma v := rfl

/-- The lower-index expansion has the explicit Dirac matrix with the physical spatial signs. -/
theorem lowerGamma_explicit (v : Vector) :
    lowerGamma v =
      !![(v 0 : ℂ), 0, -(v 3 : ℂ), -(v 1 : ℂ)+Complex.I*(v 2 : ℂ);
        0, (v 0 : ℂ), -(v 1 : ℂ)-Complex.I*(v 2 : ℂ), (v 3 : ℂ);
        (v 3 : ℂ), (v 1 : ℂ)-Complex.I*(v 2 : ℂ), -(v 0 : ℂ), 0;
        (v 1 : ℂ)+Complex.I*(v 2 : ℂ), -(v 3 : ℂ), 0, -(v 0 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerGamma, gammaLower, gamma, Fin.sum_univ_succ] <;> ring

/-- The real lower-index gamma expansion is injective. -/
theorem lowerGamma_injective : Function.Injective lowerGamma := by
  intro v w h
  have h0 := congrArg (fun M : Mat => (M 0 0).re) h
  have h1 := congrArg (fun M : Mat => (M 0 3).re) h
  have h2 := congrArg (fun M : Mat => (M 0 3).im) h
  have h3 := congrArg (fun M : Mat => (M 0 2).re) h
  simp [lowerGamma_explicit] at h0 h1 h2 h3
  ext i
  fin_cases i <;> assumption

/-- The actual gamma expansion satisfies precisely the Clifford square relation. -/
theorem lowerGamma_sq (v : Vector) :
    lowerGamma v * lowerGamma v = algebraMap ℝ Mat (quadratic v) := by
  rw [Algebra.algebraMap_eq_smul_one, lowerGamma_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadratic_apply, Complex.real_smul] <;>
    ring_nf <;> norm_num <;> ring

/-- The genuine Clifford algebra of real Minkowski space. -/
abbrev Algebra := CliffordAlgebra quadratic

/-- The universal real algebra homomorphism from the actual Minkowski Clifford algebra to Dirac matrices. -/
def dirac : Algebra →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift quadratic ⟨lowerGammaLM, lowerGamma_sq⟩

/-- The universal representation sends each actual Clifford vector to its lower-gamma expansion. -/
theorem dirac_ι (v : Vector) : dirac (CliffordAlgebra.ι quadratic v) = lowerGamma v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- The universal representation agrees with the original source gamma matrices on coordinate vectors. -/
theorem dirac_ι_basisVector (a : Fin 4) :
    dirac (CliffordAlgebra.ι quadratic (basisVector a)) = gammaLower a := by
  rw [dirac_ι, lowerGamma_basisVector]

/-- The canonical Minkowski vector inclusion in the genuine Clifford algebra is injective. -/
theorem ι_injective : Function.Injective (CliffordAlgebra.ι quadratic) := by
  intro v w h
  apply lowerGamma_injective
  simpa only [dirac_ι] using congrArg dirac h

/-- A product of two represented Clifford vectors has exactly the established Pauli-Weyl spin matrix. -/
theorem lowerGamma_mul (v w : Vector) :
    lowerGamma v * lowerGamma w = spin (pauli v * (pauli w).adjugate) := by
  rw [lowerGamma_explicit, lowerGamma_explicit, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, weylDual, pauli, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf

/-- The universal Clifford representation of each even vector pair agrees with the concrete spin model. -/
theorem dirac_pair (v w : Vector) :
    dirac (CliffordAlgebra.ι quadratic v * CliffordAlgebra.ι quadratic w) =
      spin (pauli v * (pauli w).adjugate) := by
  rw [map_mul, dirac_ι, dirac_ι, lowerGamma_mul]

end FoliationQM.CliffordMinkowski
