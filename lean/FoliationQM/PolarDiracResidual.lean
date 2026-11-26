module

public import FoliationQM.CliffordSlashConnection
public import FoliationQM.DiracEquation

/-!
# The Dirac residual of a polar spinor

Source: v13 `rem:gordon_osmotic_bridge`, in the amended form approved by the
author on 2026-11-24 (`docs/ERRATA.md`), with `eq:d_psi_polar_main`. For the
polar spinor with a supplied frame and supplied first-order data (the
gradients of the logarithmic density and of the chiral angle, and the
connection coefficients of the rotor), the Dirac first-jet residual is an
explicit invertible matrix applied to a rest-spinor expression that is real
linear in two frame covectors: the defect of the density gradient against the
trace of the connection and a mass term along the spin leg, and the defect of
the angle gradient against the axial part of the connection and a mass term
along the spin leg. The residual vanishes exactly when both defects vanish.

The jet is supplied in the factored form proved for the actual derivative in
`PolarSpinorDifferential`. Identification with a differentiated field is a
separate step.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarDiracResidual
open DiracMatrices DiracAdjoint ChiralMatrix RealLorentzFrame CliffordGenerators
open CliffordCommutators PolarConnectionContraction MaurerCartanDifferential
open PolarSpinorBilinears CliffordSlashConnection DiracEquation

/-- A vector part and an axial part contracted with the Dirac matrices. -/
def frameSlash (x y : Fin 4 → ℂ) : Mat := ∑ A, (x A • gamma A + y A • (gamma A * gamma5))

/-- The contraction is additive in both coefficient arrays. -/
theorem frameSlash_add (x x' y y' : Fin 4 → ℂ) :
    frameSlash (x + x') (y + y') = frameSlash x y + frameSlash x' y' := by
  simp only [frameSlash, Pi.add_apply, add_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  abel

/-- The contraction is homogeneous in both coefficient arrays. -/
theorem frameSlash_smul (z : ℂ) (x y : Fin 4 → ℂ) :
    frameSlash (z • x) (z • y) = z • frameSlash x y := by
  simp only [frameSlash, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_add, smul_smul]

/-- Moving the contraction past the chiral matrix reverses the chiral angle. -/
theorem frameSlash_mul_chiral (x y : Fin 4 → ℂ) (beta : ℝ) :
    frameSlash x y * chiral beta = chiral (-beta) * frameSlash x y := by
  have h1 (A : Fin 4) : gamma A * chiral beta = chiral (-beta) * gamma A := by
    have h := chiral_gamma_swap (-beta) A
    rw [neg_neg] at h
    exact h.symm
  have h2 (A : Fin 4) : gamma A * gamma5 * chiral beta = chiral (-beta) * (gamma A * gamma5) := by
    rw [mul_assoc, ← (chiral_gamma5_commute beta).eq, ← mul_assoc, h1, mul_assoc]
  simp only [frameSlash, Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, h1, h2]

/-- A coordinate Dirac matrix is the frame conjugate of its inverse-frame expansion. -/
theorem gamma_eq_frame {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (mu : Fin 4) :
    gamma mu = L * (∑ A, (inverseCoefficients u mu A : ℂ) • gamma A) * L⁻¹ := by
  have hright := Matrix.mul_nonsing_inv L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have h := inverse_expansion hunit hu mu
  unfold gammaExpansion at h
  rw [← h]
  calc gamma mu = (L * L⁻¹) * gamma mu * (L * L⁻¹) := by rw [hright]; simp
    _ = _ := by noncomm_ring

/-- A coordinate contraction against a matrix commuting with the inverse frame
matrix is the frame conjugate of the contraction of its frame components. -/
theorem frame_sum {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) {B : Mat} (hB : Commute L⁻¹ B)
    (z : Fin 4 → ℂ) :
    ∑ mu, z mu • (gamma mu * B) =
      L * (∑ A, (∑ mu, z mu * (inverseCoefficients u mu A : ℂ)) • (gamma A * B)) * L⁻¹ := by
  have hterm (mu : Fin 4) : z mu • (gamma mu * B) =
      L * (∑ A, (z mu * (inverseCoefficients u mu A : ℂ)) • (gamma A * B)) * L⁻¹ := by
    conv_lhs => rw [gamma_eq_frame hunit hu mu]
    rw [mul_assoc (L * _), hB.eq, ← mul_assoc, mul_assoc L, Finset.sum_mul,
      ← smul_mul_assoc, ← mul_smul_comm, Finset.smul_sum]
    simp only [smul_mul_assoc, smul_smul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_smul]

/-- The frame components of a covector. -/
def frameComponents (u : Fin 4 → Covector) (g : Covector) (A : Fin 4) : ℝ :=
  ∑ mu, inverseCoefficients u mu A * g mu

/-- A lowered Dirac matrix times gamma5 is the signed upper one times gamma5. -/
theorem gammaLower_mul_gamma5 (d : Fin 4) :
    gammaLower d * gamma5 = (sign d : ℂ) • (gamma d * gamma5) := by
  by_cases h : d = 0 <;> simp [gammaLower, sign, h]

/-- The coordinate Dirac contraction of the factored polar connection is the
frame conjugate of a frame contraction of half the gradient components less
the trace and axial parts of the connection. -/
theorem slash_polar {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (h5 : Commute L gamma5) (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A))
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ mu, gamma mu * ((((g mu / 2 : ℝ) : ℂ) • (1 : Mat)) +
        (Complex.I * (b mu : ℂ) / 2) • gamma5 + transportedGenerator L (omega mu)) =
      L * frameSlash
        (fun A => (((frameComponents u g A -
          frameTrace (frameConnection u omega) A) / 2 : ℝ) : ℂ))
        (fun A => Complex.I * (((frameComponents u b A -
          sign A * frameAxial (frameConnection u omega) A) / 2 : ℝ) : ℂ)) * L⁻¹ := by
  have h1 := frame_sum hunit hu (Commute.one_right L⁻¹) (fun mu => ((g mu / 2 : ℝ) : ℂ))
  have h2 := frame_sum hunit hu (inverse_commute hunit h5)
    (fun mu => Complex.I * (b mu : ℂ) / 2)
  simp only [mul_one] at h1
  have hx (A : Fin 4) : (∑ mu, ((g mu / 2 : ℝ) : ℂ) * (inverseCoefficients u mu A : ℂ)) =
      ((frameComponents u g A / 2 : ℝ) : ℂ) := by
    unfold frameComponents
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  have hy (A : Fin 4) : (∑ mu, Complex.I * (b mu : ℂ) / 2 * (inverseCoefficients u mu A : ℂ)) =
      Complex.I * ((frameComponents u b A / 2 : ℝ) : ℂ) := by
    unfold frameComponents
    push_cast
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  simp only [hx] at h1
  simp only [hy] at h2
  simp only [mul_add, mul_smul_comm, mul_one, Finset.sum_add_distrib]
  rw [h1, h2, slash_transported hunit hu, slash_generator, ← add_mul, ← add_mul, ← mul_add,
    ← mul_add]
  congr 2
  simp only [frameSlash, gammaLower_mul_gamma5, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  push_cast
  module

/-- The Dirac contraction applied to the rest spinor, for a real vector part
and a real axial part. -/
def restVector (d1 d2 : Fin 4 → ℝ) : Spinor :=
  (frameSlash (fun A => (d1 A : ℂ)) (fun A => Complex.I * (d2 A : ℂ))).mulVec restSpinor

/-- The four components of the rest contraction. -/
theorem restVector_explicit (d1 d2 : Fin 4 → ℝ) :
    restVector d1 d2 =
      ![(d1 0 : ℂ) + Complex.I * d2 3, Complex.I * d2 1 - d2 2,
        -(d1 3 : ℂ) - Complex.I * d2 0, -(d1 1 : ℂ) - Complex.I * d1 2] := by
  unfold restVector frameSlash
  rw [gamma5_explicit]
  ext i
  fin_cases i
  · simp [gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
  · simp [gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    linear_combination (d2 2 : ℂ) * Complex.I_mul_I
  · simp [gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  · simp [gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    ring

/-- The rest contraction vanishes only for vanishing real coefficient arrays. -/
theorem restVector_eq_zero_iff (d1 d2 : Fin 4 → ℝ) :
    restVector d1 d2 = 0 ↔ (∀ A, d1 A = 0) ∧ (∀ A, d2 A = 0) := by
  rw [restVector_explicit]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at h0 h1 h2 h3
    have a0 := congrArg Complex.re h0
    have a1 := congrArg Complex.im h0
    have b0 := congrArg Complex.re h1
    have b1 := congrArg Complex.im h1
    have c0 := congrArg Complex.re h2
    have c1 := congrArg Complex.im h2
    have e0 := congrArg Complex.re h3
    have e1 := congrArg Complex.im h3
    simp at a0 a1 b0 b1 c0 c1 e0 e1
    constructor
    · intro A
      fin_cases A
      · exact a0
      · exact e0
      · exact e1
      · exact c0
    · intro A
      fin_cases A
      · exact c1
      · exact b1
      · exact b0
      · exact a1
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i <;> simp [h1, h2]

/-- The spin-leg axial matrix fixes the rest spinor. -/
theorem gamma3_gamma5_rest : (gamma 3 * gamma5).mulVec restSpinor = restSpinor := by
  rw [gamma5_explicit]
  ext i
  fin_cases i <;>
    simp [gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply]

/-- The mass matrix along the spin leg, moved past the chiral matrix. -/
theorem mass_matrix (beta : ℝ) :
    gamma 3 * ((Real.sin beta : ℂ) • (1 : Mat) + (Complex.I * (Real.cos beta : ℂ)) • gamma5) *
        chiral beta = Complex.I • (chiral beta * (gamma 3 * gamma5)) := by
  have hsq := chiral_squared (-beta)
  rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg] at hsq
  have hfac : (Real.sin beta : ℂ) • (1 : Mat) + (Complex.I * (Real.cos beta : ℂ)) • gamma5 =
      Complex.I • (gamma5 * (chiral (-beta) * chiral (-beta))) := by
    rw [hsq]
    simp only [mul_add, mul_smul_comm, mul_one, gamma5_sq, smul_add, smul_smul]
    have hI : Complex.I * (Complex.I * -(Real.sin beta : ℂ)) = (Real.sin beta : ℂ) := by
      linear_combination (-(Real.sin beta : ℂ)) * Complex.I_mul_I
    rw [hI, add_comm]
  rw [hfac]
  calc gamma 3 * (Complex.I • (gamma5 * (chiral (-beta) * chiral (-beta)))) * chiral beta
      = Complex.I • (gamma 3 * (gamma5 * chiral (-beta)) * (chiral (-beta) * chiral beta)) := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = Complex.I • (gamma 3 * (gamma5 * chiral (-beta))) := by
        rw [chiral_negative_mul, mul_one]
    _ = Complex.I • (gamma 3 * (chiral (-beta) * gamma5)) := by
        rw [(chiral_gamma5_commute (-beta)).eq]
    _ = Complex.I • (chiral beta * (gamma 3 * gamma5)) := by
        rw [← mul_assoc, ← chiral_gamma_swap, mul_assoc]

/-- A frame-conjugated matrix acting on the polar spinor, written on the rest spinor. -/
theorem conj_mulVec_polar {L : Mat} (hunit : IsUnit L) (h5 : Commute L gamma5)
    (rho beta : ℝ) (F : Mat) :
    (L * F * L⁻¹).mulVec (polarSpinor rho beta L) =
      (Real.sqrt rho : ℂ) • (L * (F * chiral beta)).mulVec restSpinor := by
  have hleft := Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hc : Commute L⁻¹ (chiral beta) := by
    have h := inverse_commute hunit h5
    unfold chiral
    exact (Commute.smul_right (Commute.one_right _) _).add_right (h.smul_right _)
  unfold polarSpinor
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  congr 2
  calc L * F * L⁻¹ * (chiral beta * L) = L * F * (L⁻¹ * chiral beta) * L := by noncomm_ring
    _ = L * F * (chiral beta * L⁻¹) * L := by rw [hc.eq]
    _ = L * (F * chiral beta) * (L⁻¹ * L) := by noncomm_ring
    _ = _ := by rw [hleft, mul_one]

/-- The defect of the density gradient in the frame: its components less the
trace of the connection, plus the mass term along the spin leg. -/
def densityDefect (hbar m c beta : ℝ) (u : Fin 4 → Covector) (g : Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4) : ℝ :=
  frameComponents u g A - frameTrace (frameConnection u omega) A +
    (if A = 3 then 2 * m * c / hbar * Real.sin beta else 0)

/-- The defect of the chiral-angle gradient in the frame: its components less
the lowered axial part of the connection, plus the mass term along the spin leg. -/
def angleDefect (hbar m c beta : ℝ) (u : Fin 4 → Covector) (b : Covector)
    (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) (A : Fin 4) : ℝ :=
  frameComponents u b A - sign A * frameAxial (frameConnection u omega) A +
    (if A = 3 then 2 * m * c / hbar * Real.cos beta else 0)

/-- The first jet of the polar spinor in the factored form, for supplied
gradients of the logarithmic density and the angle and supplied connection
coefficients. -/
def polarJet (rho beta : ℝ) (L : Mat) (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (mu : Fin 4) : Spinor :=
  ((((g mu / 2 : ℝ) : ℂ) • (1 : Mat)) + (Complex.I * (b mu : ℂ) / 2) • gamma5 +
    transportedGenerator L (omega mu)).mulVec (polarSpinor rho beta L)

/-- The Dirac contraction of the polar jet is a frame-conjugated contraction
acting on the polar spinor. -/
theorem slashJet_polarJet {L : Mat} {u : Fin 4 → Covector} (hunit : IsUnit L)
    (h5 : Commute L gamma5) (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A))
    (rho beta : ℝ) (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    slashJet (polarJet rho beta L g b omega) =
      (L * frameSlash
        (fun A => (((frameComponents u g A -
          frameTrace (frameConnection u omega) A) / 2 : ℝ) : ℂ))
        (fun A => Complex.I * (((frameComponents u b A -
          sign A * frameAxial (frameConnection u omega) A) / 2 : ℝ) : ℂ)) * L⁻¹).mulVec
        (polarSpinor rho beta L) := by
  unfold slashJet polarJet
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.sum_mulVec, slash_polar hunit h5 hu]

/-- The mass term of the Dirac residual as a frame-conjugated contraction
along the spin leg. -/
theorem mass_term {L : Mat} (hunit : IsUnit L) (h5 : Commute L gamma5)
    (hbar m c rho beta : ℝ) (hh : hbar ≠ 0) :
    (Complex.I * (hbar : ℂ)) • (L * frameSlash
        (fun A => if A = 3 then ((m * c / hbar * Real.sin beta : ℝ) : ℂ) else 0)
        (fun A => if A = 3 then Complex.I * ((m * c / hbar * Real.cos beta : ℝ) : ℂ) else 0) *
        L⁻¹).mulVec (polarSpinor rho beta L) =
      -(((m * c : ℝ) : ℂ) • polarSpinor rho beta L) := by
  have hF : frameSlash
      (fun A => if A = 3 then ((m * c / hbar * Real.sin beta : ℝ) : ℂ) else 0)
      (fun A => if A = 3 then Complex.I * ((m * c / hbar * Real.cos beta : ℝ) : ℂ) else 0) =
      ((m * c / hbar : ℝ) : ℂ) • (gamma 3 *
        ((Real.sin beta : ℂ) • (1 : Mat) + (Complex.I * (Real.cos beta : ℂ)) • gamma5)) := by
    have h0 : ((0 : Fin 4) = 3) = False := by decide
    have h1 : ((1 : Fin 4) = 3) = False := by decide
    have h2 : ((2 : Fin 4) = 3) = False := by decide
    simp only [frameSlash, Fin.sum_univ_four, h0, h1, h2, ite_false, ite_true, zero_smul, add_zero,
      zero_add]
    rw [Complex.ofReal_mul (m * c / hbar) (Real.sin beta),
      Complex.ofReal_mul (m * c / hbar) (Real.cos beta)]
    simp only [mul_add, mul_smul_comm, mul_one]
    module
  have hc : Commute L (chiral beta) := by
    unfold chiral
    exact (Commute.smul_right (Commute.one_right _) _).add_right (h5.smul_right _)
  rw [hF, conj_mulVec_polar hunit h5, smul_mul_assoc, mass_matrix, mul_smul_comm, mul_smul_comm,
    ← mul_assoc, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    gamma3_gamma5_rest, hc.eq]
  unfold polarSpinor
  simp only [smul_smul, ← neg_smul]
  congr 1
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp
  linear_combination ((m : ℂ) * c * Real.sqrt rho) * Complex.I_mul_I

/-- The Dirac first-jet residual of the polar spinor is an invertible matrix
applied to the rest contraction of the two frame defects. -/
theorem diracJet_polar (hbar m c rho beta : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hunit : IsUnit L) (h5 : Commute L gamma5)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hh : hbar ≠ 0)
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    diracJet hbar m c (polarSpinor rho beta L) (polarJet rho beta L g b omega) =
      (Complex.I * (hbar : ℂ) * (Real.sqrt rho : ℂ) / 2) • (L * chiral (-beta)).mulVec
        (restVector (densityDefect hbar m c beta u g omega)
          (angleDefect hbar m c beta u b omega)) := by
  unfold diracJet
  rw [slashJet_polarJet hunit h5 hu, sub_eq_add_neg, ← mass_term hunit h5 hbar m c rho beta hh,
    ← smul_add, ← Matrix.add_mulVec, ← add_mul, ← mul_add, ← frameSlash_add,
    conj_mulVec_polar hunit h5, frameSlash_mul_chiral]
  have hF : frameSlash
      ((fun A => (((frameComponents u g A -
          frameTrace (frameConnection u omega) A) / 2 : ℝ) : ℂ)) +
        fun A => if A = 3 then ((m * c / hbar * Real.sin beta : ℝ) : ℂ) else 0)
      ((fun A => Complex.I * (((frameComponents u b A -
          sign A * frameAxial (frameConnection u omega) A) / 2 : ℝ) : ℂ)) +
        fun A => if A = 3 then Complex.I * ((m * c / hbar * Real.cos beta : ℝ) : ℂ) else 0) =
      (1/2 : ℂ) • frameSlash (fun A => (densityDefect hbar m c beta u g omega A : ℂ))
        (fun A => Complex.I * (angleDefect hbar m c beta u b omega A : ℂ)) := by
    rw [← frameSlash_smul]
    congr 1 <;> funext A <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, densityDefect, angleDefect] <;>
      split_ifs <;> push_cast <;> ring
  rw [hF]
  unfold restVector
  rw [mul_smul_comm, mul_smul_comm, Matrix.smul_mulVec, ← mul_assoc, ← Matrix.mulVec_mulVec,
    smul_smul, smul_smul]
  congr 1
  ring

/-- For positive density the Dirac first-jet equation of the polar spinor
holds exactly when both frame defects vanish. -/
theorem diracJet_polar_eq_zero_iff (hbar m c : ℝ) {rho : ℝ} (beta : ℝ) {L : Mat}
    {u : Fin 4 → Covector} (hrho : 0 < rho) (hunit : IsUnit L) (h5 : Commute L gamma5)
    (hu : ∀ A, L * gamma A * L⁻¹ = gammaExpansion (u A)) (hh : hbar ≠ 0)
    (g b : Covector) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    diracJet hbar m c (polarSpinor rho beta L) (polarJet rho beta L g b omega) = 0 ↔
      (∀ A, densityDefect hbar m c beta u g omega A = 0) ∧
        (∀ A, angleDefect hbar m c beta u b omega A = 0) := by
  rw [diracJet_polar hbar m c rho beta hunit h5 hu hh, ← restVector_eq_zero_iff]
  have hscal : (Complex.I * (hbar : ℂ) * (Real.sqrt rho : ℂ) / 2) ≠ 0 := by
    have hs : (Real.sqrt rho : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hrho).ne'
    have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh
    exact div_ne_zero (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hb) hs) (by norm_num)
  have hM : IsUnit (L * chiral (-beta)) := hunit.mul (chiral_isUnit _)
  constructor
  · intro h
    have h' := (smul_eq_zero.mp h).resolve_left hscal
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hM) (h'.trans (Matrix.mulVec_zero _).symm)
  · intro h
    rw [h, Matrix.mulVec_zero, smul_zero]

end FoliationQM.PolarDiracResidual
