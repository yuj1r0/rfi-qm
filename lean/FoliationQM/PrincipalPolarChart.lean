module
public import FoliationQM.PrincipalPolarSmooth
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.PolarMatrixFibers
public import Mathlib.Tactic.Ring

/-!
# Exact principal-branch polar chart

Source: v13 `prop:takabayasi` and `eq:takabayasi_polar`. Positive density,
a determinant-one matrix and a full angle strictly between minus pi and
pi give an actual source polar spinor whose determinant lies in the
complex slit plane. Its actual invariant density, principal determinant
angle and normalized matrix recover the input coordinates exactly.

These identities and the existing constructed reconstruction provide a
two-sided algebraic equivalence between this coordinate patch and the
actual slit-plane spinor domain. Smoothness of the actual inverse functions
is established separately in `PrincipalPolarSmooth`; the actual ambient
forward map is smooth to every order wherever the density is positive.
This equivalence
does not assert a global angle, a global branch or an abstract Spin-group
classification.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.PrincipalPolarChart
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSpinorBilinears ChiralSpinorMatrix RegularPolarReconstruction PrincipalPolarSmooth

/-- The actual polar spinor determinant is the invariant density times the exponential of the full chiral angle. -/
theorem determinant_polar (rho beta : ℝ) (A : Mat2) (hrho : 0 ≤ rho) (hA : A.det = 1) :
    Matrix.det (toMatrix (polarSpinor rho beta (spin A))) =
      (rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ)) := by
  rw [toMatrix_polarSpinor, spin_rest_matrix, Matrix.det_smul, hA]
  norm_num only [Fintype.card_fin, mul_one]
  rw [mul_pow]
  have hs : (Real.sqrt rho : ℂ)^2 = (rho : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hrho
  rw [hs, ← Complex.exp_nat_mul]
  congr 2
  norm_num only [Nat.cast_ofNat]
  ring

/-- On the open principal-angle interval the actual determinant phase recovers the full input angle. -/
theorem determinantPhase_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    determinantPhase (polarSpinor rho beta (spin A)) = beta := by
  rw [determinantPhase, determinant_polar rho beta A hrho.le hA,
    Complex.arg_real_mul _ hrho]
  rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I ⟨hbeta.1, hbeta.2.le⟩

/-- The actual determinant of principal-branch polar data belongs to the complex slit plane. -/
theorem determinant_polar_mem_slitPlane (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    Matrix.det (toMatrix (polarSpinor rho beta (spin A))) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  constructor
  · change determinantPhase (polarSpinor rho beta (spin A)) ≠ Real.pi
    rw [determinantPhase_polar rho beta A hrho hA hbeta]
    exact ne_of_lt hbeta.2
  · rw [determinant_polar rho beta A hrho.le hA]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hrho.ne') (Complex.exp_ne_zero _)

/-- The actual invariant density of positive-branch polar data recovers the input density. -/
theorem invariantDensity_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 ≤ rho) (hA : A.det = 1) :
    invariantDensity (polarSpinor rho beta (spin A)) = rho :=
  SpinorRegularity.invariantDensity_polar rho beta (spin A) hrho
    (spin_dirac_isometry A hA) (spin_gamma5_commute A)

/-- The constructed principal amplitude recovers the actual square-root density and half-angle phase. -/
theorem amplitudePhase_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    amplitudePhase (polarSpinor rho beta (spin A)) =
      (Real.sqrt rho : ℂ) * Complex.exp (Complex.I * (beta : ℂ) / 2) := by
  rw [amplitudePhase, invariantDensity_polar rho beta A hrho.le hA,
    determinantPhase_polar rho beta A hrho hA hbeta]

/-- The actual determinant normalization recovers the input determinant-one matrix on the principal branch. -/
theorem normalizedMatrix_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    normalizedMatrix (polarSpinor rho beta (spin A)) = A := by
  rw [normalizedMatrix, amplitudePhase_polar rho beta A hrho hA hbeta,
    toMatrix_polarSpinor, spin_rest_matrix, smul_smul]
  have hs : (Real.sqrt rho : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hrho).ne'
  rw [inv_mul_cancel₀ (mul_ne_zero hs (Complex.exp_ne_zero _)), one_smul]

/-- The reconstructed Dirac representative equals the actual input representative on the principal branch. -/
theorem reconstructedSpin_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    reconstructedSpin (polarSpinor rho beta (spin A)) = spin A := by
  rw [reconstructedSpin, normalizedMatrix_polar rho beta A hrho hA hbeta]

/-- The actual forward polar spinor belongs to the principal reconstruction domain. -/
theorem polar_mem_principalDomain (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) (hbeta : beta ∈ Set.Ioo (-Real.pi) Real.pi) :
    polarSpinor rho beta (spin A) ∈ PrincipalDomain :=
  determinant_polar_mem_slitPlane rho beta A hrho hA hbeta

/-- Polar coordinates on the principal branch, with positive density and an actual determinant-one matrix. -/
structure Coordinates where
  rho : ℝ
  beta : ℝ
  A : Mat2
  rho_pos : 0 < rho
  beta_mem : beta ∈ Set.Ioo (-Real.pi) Real.pi
  det_eq_one : A.det = 1

/-- Principal polar coordinates are equal when their density, angle and matrix are equal. -/
theorem coordinates_ext {p q : Coordinates} (hrho : p.rho = q.rho)
    (hbeta : p.beta = q.beta) (hA : p.A = q.A) : p = q := by
  cases p
  cases q
  cases hrho
  cases hbeta
  cases hA
  rfl

/-- The actual spinors whose encoded determinant lies in the complex slit plane. -/
abbrev PatchSpinor := {psi : Spinor // psi ∈ PrincipalDomain}

/-- The actual source polar map restricted to the principal coordinate patch. -/
def forward (p : Coordinates) : PatchSpinor :=
  ⟨polarSpinor p.rho p.beta (spin p.A),
    polar_mem_principalDomain p.rho p.beta p.A p.rho_pos p.det_eq_one p.beta_mem⟩

/-- The actual invariant density, determinant phase and normalized matrix restricted to the principal spinor patch. -/
def inverse (psi : PatchSpinor) : Coordinates where
  rho := invariantDensity psi.val
  beta := determinantPhase psi.val
  A := normalizedMatrix psi.val
  rho_pos := principalDomain_regular psi.property
  beta_mem := determinantPhase_bounds_strict psi.property
  det_eq_one := normalizedMatrix_det (principalDomain_regular psi.property)

/-- The constructed inverse recovers every principal coordinate tuple exactly. -/
theorem inverse_forward (p : Coordinates) : inverse (forward p) = p := by
  apply coordinates_ext
  · exact invariantDensity_polar p.rho p.beta p.A p.rho_pos.le p.det_eq_one
  · exact determinantPhase_polar p.rho p.beta p.A p.rho_pos p.det_eq_one p.beta_mem
  · exact normalizedMatrix_polar p.rho p.beta p.A p.rho_pos p.det_eq_one p.beta_mem

/-- The actual polar map reconstructs every spinor in the principal determinant branch. -/
theorem forward_inverse (psi : PatchSpinor) : forward (inverse psi) = psi := by
  apply Subtype.ext
  exact (regular_reconstruction (principalDomain_regular psi.property)).symm

/-- The genuine two-sided algebraic equivalence between principal polar coordinates and principal-branch spinors. -/
def patchEquiv : Coordinates ≃ PatchSpinor where
  toFun := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse

/-- The actual source polar map is bijective between the two principal-branch domains. -/
theorem forward_bijective : Function.Bijective forward := patchEquiv.bijective


open SpinorMatrixSmooth PolarMatrixFibers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth real density and angle fields and an actual smooth matrix field give a smooth actual polar spinor wherever the density is positive. -/
theorem contDiffAt_polar_fields (n : WithTop ℕ∞) {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : ContDiffAt ℝ n rho x) (hbeta : ContDiffAt ℝ n beta x)
    (hA : ContDiffAt ℝ n A x) (hpos : 0 < rho x) :
    ContDiffAt ℝ n (fun y => polarSpinor (rho y) (beta y) (spin (A y))) x := by
  have hs : ContDiffAt ℝ n (fun y => (Real.sqrt (rho y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (hrho.sqrt hpos.ne')
  have hb : ContDiffAt ℝ n (fun y => (beta y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hbeta
  have he : ContDiffAt ℝ n (fun y => Complex.exp (Complex.I * (beta y : ℂ) / 2)) x :=
    ((contDiffAt_const.mul hb).div_const 2).cexp
  have hm : ContDiffAt ℝ n (fun y =>
      (((Real.sqrt (rho y) : ℂ) * Complex.exp (Complex.I * (beta y : ℂ) / 2)) • A y)) x :=
    (hs.mul he).smul hA
  have hf := (contDiff_ofMatrix n).contDiffAt.comp x hm
  change ContDiffAt ℝ n (fun y => parameterSpinor
    ((Real.sqrt (rho y) : ℂ) * Complex.exp (Complex.I * (beta y : ℂ) / 2)) (A y)) x at hf
  simpa only [parameterSpinor_polarAmplitude] using hf

/-- The actual ambient polar map is real-smooth to every order at every positive-density input, without requiring a branch or determinant constraint. -/
theorem contDiffAt_polarMap (n : WithTop ℕ∞) {p : ℝ × ℝ × Mat2} (hpos : 0 < p.1) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ × Mat2 => polarSpinor q.1 q.2.1 (spin q.2.2)) p :=
  contDiffAt_polar_fields n contDiffAt_fst contDiffAt_snd.fst contDiffAt_snd.snd hpos

/-- The actual ambient polar map is real-smooth on the entire positive-density parameter domain. -/
theorem contDiffOn_polarMap (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun q : ℝ × ℝ × Mat2 => polarSpinor q.1 q.2.1 (spin q.2.2))
      {p | 0 < p.1} :=
  fun _ hp => (contDiffAt_polarMap n hp).contDiffWithinAt
end FoliationQM.PrincipalPolarChart
