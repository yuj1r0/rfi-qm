module
public import FoliationQM.DiracAdjoint
public import FoliationQM.PolarSpinorBilinears
public import FoliationQM.RotorUnitary
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

/-!
# Real invariant spinor density and the strict regular domain

Sources: v13 `prop:takabayasi`, `eq:takabayasi_polar`, and
`eq:scalar_pseudoscalar_bilinears`; startup regular-domain requirement.
The real parts are faithful to proved-real actual matrix bilinears. Density
is the real square root of their squared sum. The explicit nonzero singular
spinor demonstrates why a positive Hermitian square cannot replace this
domain. No reconstruction of a general regular spinor is inferred.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinorRegularity
open DiracMatrices DiracAdjoint

/-- The real scalar invariant of an actual Dirac spinor. -/
def scalar (psi : Spinor) : ℝ := (bilinear psi 1 psi).re
/-- The real signed pseudoscalar invariant minus i times the actual gamma5 bilinear. -/
def pseudoscalar (psi : Spinor) : ℝ := (-Complex.I * bilinear psi gamma5 psi).re
/-- The actual nonnegative scalar-pseudoscalar invariant density. -/
def invariantDensity (psi : Spinor) : ℝ := Real.sqrt (scalar psi ^ 2 + pseudoscalar psi ^ 2)
/-- The source strict regular domain requires positive invariant density. -/
def Regular (psi : Spinor) : Prop := 0 < invariantDensity psi

/-- The actual nonnegative Hermitian square, distinct from the invariant density. -/
def hermitianSquare (psi : Spinor) : ℝ := ∑ i : Fin 4, Complex.normSq (psi i)
/-- A concrete nonzero singular spinor with both invariant bilinears zero. -/
def singularSpinor : Spinor := ![1,0,1,0]

/-- The real scalar invariant recovers the entire actual complex scalar bilinear. -/
theorem scalar_as_complex (psi : Spinor) : (scalar psi : ℂ) = bilinear psi 1 psi := by
  apply Complex.ext
  · rfl
  · simpa using (scalar_bilinear_real psi).symm

/-- The real pseudoscalar invariant recovers the entire actual signed complex bilinear. -/
theorem pseudoscalar_as_complex (psi : Spinor) :
    (pseudoscalar psi : ℂ) = -Complex.I * bilinear psi gamma5 psi := by
  apply Complex.ext
  · rfl
  · simpa using (pseudoscalar_bilinear_real psi).symm

/-- Changing the source pseudoscalar sign negates its real invariant. -/
theorem plus_I_pseudoscalar (psi : Spinor) :
    (Complex.I * bilinear psi gamma5 psi).re = -pseudoscalar psi := by
  simp [pseudoscalar]

/-- The invariant density is nonnegative for every spinor. -/
theorem invariantDensity_nonneg (psi : Spinor) : 0 ≤ invariantDensity psi := Real.sqrt_nonneg _

/-- The square of the actual invariant density is the sum of the two real invariant squares. -/
theorem invariantDensity_sq (psi : Spinor) :
    invariantDensity psi ^ 2 = scalar psi ^ 2 + pseudoscalar psi ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The invariant density also equals the startup formula using plus i in the squared pseudoscalar. -/
theorem invariantDensity_plus_sign (psi : Spinor) :
    invariantDensity psi = Real.sqrt (scalar psi ^ 2 + (Complex.I * bilinear psi gamma5 psi).re ^ 2) := by
  rw [plus_I_pseudoscalar, neg_sq]
  rfl

/-- Strict regularity is exactly positivity of the invariant squared sum. -/
theorem regular_iff_square_sum_pos (psi : Spinor) :
    Regular psi ↔ 0 < scalar psi ^ 2 + pseudoscalar psi ^ 2 := by
  exact Real.sqrt_pos

/-- A spinor is regular exactly when at least one invariant bilinear is nonzero. -/
theorem regular_iff_invariants_nonzero (psi : Spinor) :
    Regular psi ↔ scalar psi ≠ 0 ∨ pseudoscalar psi ≠ 0 := by
  rw [regular_iff_square_sum_pos]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    rcases hn with ⟨hs,hp⟩
    simp [hs,hp] at h
  · rintro (hs | hp)
    · nlinarith [sq_pos_of_ne_zero hs, sq_nonneg (pseudoscalar psi)]
    · nlinarith [sq_pos_of_ne_zero hp, sq_nonneg (scalar psi)]

/-- Zero invariant density is exactly simultaneous vanishing of both invariant bilinears. -/
theorem invariantDensity_zero_iff (psi : Spinor) :
    invariantDensity psi = 0 ↔ scalar psi = 0 ∧ pseudoscalar psi = 0 := by
  constructor
  · intro h
    have hs := invariantDensity_sq psi
    rw [h] at hs
    constructor <;> nlinarith [sq_nonneg (scalar psi), sq_nonneg (pseudoscalar psi)]
  · rintro ⟨hs,hp⟩
    simp [invariantDensity,hs,hp]

/-- The zero spinor is outside the strict regular domain. -/
theorem zero_not_regular : ¬Regular 0 := by
  simp [Regular,invariantDensity,scalar,pseudoscalar,bilinear]

/-- Strict invariant regularity implies that the actual spinor is nonzero. -/
theorem regular_ne_zero {psi : Spinor} (h : Regular psi) : psi ≠ 0 := by
  rintro rfl
  exact zero_not_regular h

/-- The concrete nonzero singular spinor has zero scalar invariant. -/
theorem singularSpinor_scalar : scalar singularSpinor = 0 := by
  norm_num [scalar, singularSpinor, bilinear, gamma, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The concrete nonzero singular spinor has zero pseudoscalar invariant. -/
theorem singularSpinor_pseudoscalar : pseudoscalar singularSpinor = 0 := by
  norm_num [pseudoscalar, singularSpinor, bilinear, gamma, gamma5_explicit,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The concrete singular spinor is not invariant-regular. -/
theorem singularSpinor_not_regular : ¬Regular singularSpinor := by
  rw [regular_iff_invariants_nonzero, singularSpinor_scalar, singularSpinor_pseudoscalar]
  simp

/-- The concrete singular spinor is nonetheless nonzero. -/
theorem singularSpinor_ne_zero : singularSpinor ≠ 0 := by
  intro h
  have he := congrArg (fun psi : Spinor => psi 0) h
  simp [singularSpinor] at he

/-- The concrete singular spinor has strictly positive Hermitian square equal to two. -/
theorem singularSpinor_hermitianSquare : hermitianSquare singularSpinor = 2 := by
  norm_num [hermitianSquare, singularSpinor, Fin.sum_univ_succ]

/-- A nonzero spinor with positive Hermitian square can fail invariant regularity. -/
theorem exists_nonzero_singular : ∃ psi : Spinor,
    psi ≠ 0 ∧ 0 < hermitianSquare psi ∧ ¬Regular psi := by
  exact ⟨singularSpinor, singularSpinor_ne_zero,
    by rw [singularSpinor_hermitianSquare]; norm_num, singularSpinor_not_regular⟩

/-- The Hermitian square is nonnegative for every actual spinor. -/
theorem hermitianSquare_nonneg (psi : Spinor) : 0 ≤ hermitianSquare psi :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (psi i))

/-- The Hermitian square is the literal conjugate spinor dot product. -/
theorem hermitianSquare_as_complex (psi : Spinor) :
    (hermitianSquare psi : ℂ) = star psi ⬝ᵥ psi := by
  simp only [hermitianSquare, dotProduct, Pi.star_apply, Complex.star_def]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.normSq_eq_conj_mul_self

/-- The Hermitian square equals the actual temporal vector bilinear. -/
theorem hermitianSquare_vector_time (psi : Spinor) :
    (hermitianSquare psi : ℂ) = bilinear psi (gamma 0) psi := by
  simp only [bilinear, gamma_zero_sq, Matrix.one_mulVec]
  exact hermitianSquare_as_complex psi

/-- The actual invariant density of the forward polar ansatz equals its nonnegative density parameter. -/
theorem invariantDensity_polar (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    invariantDensity (PolarSpinorBilinears.polarSpinor rho beta L) = rho := by
  unfold invariantDensity scalar pseudoscalar
  rw [PolarSpinorBilinears.polar_scalar_re rho beta L hrho hL h5,
    PolarSpinorBilinears.polar_pseudoscalar_re rho beta L hrho hL h5]
  have h : (rho*Real.cos beta)^2+(rho*Real.sin beta)^2 = rho^2 := by
    calc
      _ = rho^2*(Real.cos beta^2+Real.sin beta^2) := by ring
      _ = rho^2 := by rw [Real.cos_sq_add_sin_sq]; ring
  rw [h, Real.sqrt_sq hrho]

/-- On the nonnegative density parameter domain, the actual polar ansatz is regular exactly at positive density. -/
theorem regular_polar_iff (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    Regular (PolarSpinorBilinears.polarSpinor rho beta L) ↔ 0 < rho := by
  unfold Regular
  rw [invariantDensity_polar rho beta L hrho hL h5]

/-- A positive-density polar ansatz with the stated actual matrix premises belongs to the source regular domain. -/
theorem regular_polar_of_pos (rho beta : ℝ) (L : Mat) (hrho : 0 < rho)
    (hL : diracAdjoint L*L=1) (h5 : Commute L gamma5) :
    Regular (PolarSpinorBilinears.polarSpinor rho beta L) :=
  (regular_polar_iff rho beta L hrho.le hL h5).mpr hrho

/-- Every actual plane-rotated polar spinor with positive density is invariant-regular. -/
theorem regular_plane_polar (rho beta theta : ℝ) (hrho : 0 < rho) :
    Regular (PolarSpinorBilinears.polarSpinor rho beta (PlaneRotor.rotor theta)) :=
  regular_polar_of_pos rho beta _ hrho (RotorUnitary.rotor_diracAdjoint_mul theta)
    (RotorUnitary.rotor_commute_gamma5 theta)

/-- Positive-density actual plane-rotated polar spinors are nonzero by their proved invariant regularity. -/
theorem plane_polar_ne_zero (rho beta theta : ℝ) (hrho : 0 < rho) :
    PolarSpinorBilinears.polarSpinor rho beta (PlaneRotor.rotor theta) ≠ 0 :=
  regular_ne_zero (regular_plane_polar rho beta theta hrho)

end FoliationQM.SpinorRegularity
