module

public import FoliationQM.GeneralCouplingAction

/-!
Sources: v13 `eq:general_lambda_action` and `eq:nonlinear_defect`.

The actual first variation of the real relative action is written directly
in density and phase variables. The two independent test coefficients are
the generalized Hamilton--Jacobi residual and minus twice the actual current
divergence. Background action finiteness is not assumed.
-/
@[expose] public section

namespace FoliationQM.GeneralCouplingFirstVariation

open MeasureTheory ActionDensity PolarTestVariations FlatIntegrationByParts
open PolarSecondDifferential
open scoped Topology ContDiff ComplexConjugate

/-- The polar test paired with the dimensional KG jet yields the two real
Euler--Lagrange coefficients, without assuming either field equation. -/
theorem tangent_kgResidual_real (p : MassiveParameters) (R S a b : ℝ)
    (dR dS : Covector) (boxR boxS : ℝ) (hR : 0 < R) :
    -2 * (conj (PolarTangentEquiv.tangent p (R ^ 2)
      (PolarSecondJet.wave p R S) a b) *
      ((p.hbar : ℂ) ^ 2 * PolarSecondJet.kgResidual p R S dR dS boxR boxS)).re =
      a * PolarSecondJet.hjResidual p R dS boxR -
        2 * b * PolarSecondJet.continuityResidual R dR dS boxS := by
  have hp : conj (phase (S / p.hbar)) * phase (S / p.hbar) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have hn : Complex.normSq (phase (S / p.hbar)) = 1 := by
      simp only [phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq (S / p.hbar)]
    rw [hn, Complex.ofReal_one]
  rw [PolarSecondJet.kgResidual_decomposition p R S dR dS boxR boxS hR]
  let z : ℂ := ((a / (2 * R ^ 2) : ℝ) : ℂ) + Complex.I * ((b / p.hbar : ℝ) : ℂ)
  let w : ℂ := ((-R / p.hbar ^ 2 * PolarSecondJet.hjResidual p R dS boxR : ℝ) : ℂ) +
    Complex.I * ((PolarSecondJet.continuityResidual R dR dS boxS / (p.hbar * R) : ℝ) : ℂ)
  have heq : conj ((R : ℂ) * phase (S / p.hbar) * z) *
      ((p.hbar : ℂ) ^ 2 * (phase (S / p.hbar) * w)) =
      (R : ℂ) * (p.hbar : ℂ) ^ 2 * conj z * w := by
    simp only [map_mul, Complex.conj_ofReal]
    calc
      _ = (conj (phase (S / p.hbar)) * phase (S / p.hbar)) *
          ((R : ℂ) * (p.hbar : ℂ) ^ 2 * conj z * w) := by ring
      _ = _ := by rw [hp, one_mul]
  change -2 * (conj ((R : ℂ) * phase (S / p.hbar) * z) *
    ((p.hbar : ℂ) ^ 2 * (phase (S / p.hbar) * w))).re = _
  rw [heq]
  rw [← Complex.ofReal_pow]
  simp only [z, w, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hh0 : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  field_simp
  ring

/-- Pointwise real form of the actual KG test pairing for the auxiliary
parameters: the coefficients contain only the original real source fields
and λ. The amplitude derivatives are justified by local C² regularity. -/
theorem testTangent_kgOperator_real (p : MassiveParameters) {lam : ℝ} (hlam : 0 < lam)
    {ρ S a b : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 2 ρ x) (hS : ContDiffAt ℝ 2 S x) (hpos : 0 < ρ x)
    (e : Fin 4 → Covector) :
    -2 * (conj (testTangent (GeneralCouplingAction.effectiveParameters p lam hlam) ρ S a b x) *
      kgOperator (GeneralCouplingAction.effectiveParameters p lam hlam)
        (actionField (GeneralCouplingAction.effectiveParameters p lam hlam) ρ S) e x).re =
      a x * (minkowski (fun μ => directionalDerivative S (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 -
          4 * lam * box (fun y => Real.sqrt (ρ y)) e x / Real.sqrt (ρ x)) -
        2 * b x * PolarRegularity.densityCurrentDivergence ρ S e x := by
  let q := GeneralCouplingAction.effectiveParameters p lam hlam
  obtain ⟨hR, hS', hR2, hS2⟩ :=
    PolarRegularity.sqrt_density_second_order_hypotheses hρ hS hpos e
  have hkg : kgOperator q (actionField q ρ S) e x = (q.hbar : ℂ) ^ 2 *
      PolarSecondJet.kgResidual q (Real.sqrt (ρ x)) (S x)
        (fun μ => directionalDerivative (fun y => Real.sqrt (ρ y)) (e μ) x)
        (fun μ => directionalDerivative S (e μ) x)
        (box (fun y => Real.sqrt (ρ y)) e x) (box S e x) := by
    rw [← Madelung.kgResidual_actionField q e hR hS' hR2 hS2]
    have hh0 : (q.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt q.hbar_pos)
    simp only [kgOperator, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    change _ = (q.hbar : ℂ) ^ 2 * (box (actionField q ρ S) e x +
      ((q.m : ℂ) ^ 2 * (q.c : ℂ) ^ 2 / (q.hbar : ℂ) ^ 2) * actionField q ρ S x)
    field_simp
  change -2 * (conj (testTangent q ρ S a b x) * kgOperator q (actionField q ρ S) e x).re = _
  rw [hkg]
  have ht : testTangent q ρ S a b x = PolarTangentEquiv.tangent q
      ((Real.sqrt (ρ x)) ^ 2) (PolarSecondJet.wave q (Real.sqrt (ρ x)) (S x)) (a x) (b x) := by
    rw [Real.sq_sqrt hpos.le]
    rfl
  rw [ht, tangent_kgResidual_real q _ _ _ _ _ _ _ _ (Real.sqrt_pos.2 hpos)]
  rw [← Madelung.currentDivergence_eq_continuityResidual e hR.self_of_nhds hS2,
    PolarRegularity.currentDivergence_sqrt_density hρ.continuousAt hpos e]
  simp only [PolarSecondJet.hjResidual, q,
    GeneralCouplingAction.effectiveParameters_hbar_sq p hlam]
  rfl

/-- The explicit real first-variation density is genuinely integrable on the
domain: the test pairing has compact interior support and local regularity
suffices for its background coefficients. -/
theorem integrableOn_firstVariationDensity (p : MassiveParameters)
    {lam : ℝ} (hlam : 0 < lam) {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    IntegrableOn (fun x => a x * (minkowski (fun μ => directionalDerivative S (e μ) x)
      (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 -
        4 * lam * box (fun y => Real.sqrt (ρ y)) e x / Real.sqrt (ρ x)) -
      2 * b x * PolarRegularity.densityCurrentDivergence ρ S e x) U := by
  let q := GeneralCouplingAction.effectiveParameters p lam hlam
  have ht := OpenPolarVariations.contDiff_testTangent q hρ hS ha hb hpos hsa hsb
  have htc := hasCompactSupport_testTangent q ρ S hca hcb
  have hts := (OpenPolarVariations.tsupport_testTangent_subset q ρ S a b).trans
    (Set.union_subset hsa hsb)
  have hψ : ∀ x ∈ U, ContDiffAt ℝ 2 (actionField q ρ S) x := by
    intro x hx
    exact (OpenPolarVariations.contDiffAt_actionField q (hρ x hx) (hS x hx)
      (hpos x hx)).of_le (by norm_num)
  have hi := OpenIntegrationByParts.integrable_test_kgOperator q
    (ht.of_le (by norm_num)) hψ htc hts e
  apply (hi.re.const_mul (-2)).congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact testTangent_kgOperator_real p hlam ((hρ x hx).of_le (by norm_num))
    ((hS x hx).of_le (by norm_num)) (hpos x hx) e

/-- Actual first variation of the relative real source action, expressed
directly through the generalized HJ residual and actual current divergence.
The tests vary density and phase independently inside the open domain. -/
theorem hasDerivAt_relativeHydroAction_affine_real (p : MassiveParameters)
    {lam : ℝ} (hlam : 0 < lam) {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    HasDerivAt (fun t : ℝ => GeneralCouplingAction.relativeHydroAction p lam ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U)
      (∫ x in U, a x * (minkowski (fun μ => directionalDerivative S (e μ) x)
        (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 -
          4 * lam * box (fun y => Real.sqrt (ρ y)) e x / Real.sqrt (ρ x)) -
        2 * b x * PolarRegularity.densityCurrentDivergence ρ S e x) 0 := by
  have hd := GeneralCouplingAction.hasDerivAt_relativeHydroAction_affine p hlam hU hρ hS
    ha hb hpos hca hcb hsa hsb e
  rw [← integral_const_mul] at hd
  convert hd using 1
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  exact (testTangent_kgOperator_real p hlam ((hρ x hx).of_le (by norm_num))
    ((hS x hx).of_le (by norm_num)) (hpos x hx) e).symm

end FoliationQM.GeneralCouplingFirstVariation
