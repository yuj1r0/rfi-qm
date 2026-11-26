module

public import FoliationQM.ConeRadialCompletion
public import FoliationQM.PowerMetric

/-!
# Euclidean completion in the stipulated degree-one power family

Sources: v13 `lem:uniqueness` and `eq:unique_params`.
The completion witness is an actual isometric equivalence of the genuine
intrinsic metric completion with the complex plane. On original points its
coordinate must be the source formula `rho^alpha * q`, with the physical
circle phase unchanged. This is a specified family of maps; no classification
of arbitrary alternative Euclidean charts is encoded in its definition.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.PowerConeCompletion

open ConeManifold ConeIntrinsicMetric ConeCompletion
open scoped NNReal

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The stipulated degree-one power coordinate on original positive-density points. -/
def powerCoordinate (α : ℝ) (p : Point hbar coupling) : ℂ :=
  (Real.rpow (canonicalEquiv hbar coupling p).density α : ℂ) *
    ((canonicalEquiv hbar coupling p).phase : ℂ)

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- Its modulus is the actual positive density to the prescribed real power. -/
theorem norm_powerCoordinate (α : ℝ) (p : Point hbar coupling) :
    ‖powerCoordinate hbar coupling α p‖ = Real.rpow (Complex.normSq p.value) α := by
  simp only [powerCoordinate, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, Real.rpow_eq_pow]
  rw [abs_of_pos (Real.rpow_pos_of_pos (canonicalEquiv hbar coupling p).density_pos α)]
  rfl

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- At exponent one half, the specified power coordinate is the original
physical Born coordinate on every point of the punctured cone. -/
theorem powerCoordinate_half (p : Point hbar coupling) :
    powerCoordinate hbar coupling (1 / 2) p = p.value := by
  have h := canonicalEquiv_toComplex hbar coupling p
  simpa only [powerCoordinate, CanonicalPolarMetric.toComplex, Real.sqrt_eq_rpow,
    Real.rpow_eq_pow] using h

/-- The actual completed physical coordinate is an isometry at canonical coupling. -/
theorem isometry_coordinate (hc : coupling = hbar ^ 2 / 4) :
    Isometry (coordinate hbar coupling) := by
  obtain ⟨hl, hu⟩ := canonical_factors hbar coupling hc
  apply Isometry.of_dist_eq
  intro x y
  have hlow := (coordinate_lipschitz hbar coupling).dist_le_mul x y
  have hhigh := (coordinate_antilipschitz hbar coupling).le_mul_dist x y
  change dist (coordinate hbar coupling x) (coordinate hbar coupling y) ≤
    (ConeSpeed.lowerFactor hbar coupling)⁻¹ * dist x y at hlow
  change dist x y ≤ ConeSpeed.upperFactor hbar coupling *
    dist (coordinate hbar coupling x) (coordinate hbar coupling y) at hhigh
  rw [hl, inv_one, one_mul] at hlow
  rw [hu, one_mul] at hhigh
  exact le_antisymm hlow hhigh

/-- Canonical coupling gives an actual Euclidean isometric equivalence of the
constructed general metric completion, preserving its physical coordinate. -/
def canonicalCompletionIsometry (hc : coupling = hbar ^ 2 / 4) :
    Completed hbar coupling ≃ᵢ ℂ :=
  { (complexHomeomorph hbar coupling).toEquiv with
    isometry_toFun := isometry_coordinate hbar coupling hc }

/-- The canonical completed isometry sends the genuinely added tip to the origin. -/
theorem canonicalCompletionIsometry_tip (hc : coupling = hbar ^ 2 / 4) :
    canonicalCompletionIsometry hbar coupling hc (tip hbar coupling) = 0 :=
  coordinate_tip hbar coupling

/-- On original points the canonical completed isometry has exactly the
source degree-one square-root power formula. -/
theorem canonicalCompletionIsometry_coe (hc : coupling = hbar ^ 2 / 4)
    (p : Point hbar coupling) :
    canonicalCompletionIsometry hbar coupling hc (p : Completed hbar coupling) =
      powerCoordinate hbar coupling (1 / 2) p := by
  change coordinate hbar coupling (p : Completed hbar coupling) = _
  rw [coordinate_coe, powerCoordinate_half]

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- On a supplied positive-density real phase lift, this is exactly the
source power field with the phase coefficient fixed at one. -/
theorem powerCoordinate_ofLift (α ρ Φ : ℝ) (hρ : 0 < ρ) :
    powerCoordinate hbar coupling α
      ((canonicalEquiv hbar coupling).symm (CanonicalPolarMetric.ofLift ρ Φ hρ)) =
      PowerMetric.powerField α (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (ρ, Φ) := by
  simp only [powerCoordinate, Equiv.apply_symm_apply]
  rfl

/-- An actual origin-preserving isometry agreeing with the stipulated power
formula forces both source parameters. The proof uses exact intrinsic radii,
not a presumed cone-angle or local tensor equality. -/
theorem parameters_of_power_isometry (α : ℝ) (E : Completed hbar coupling ≃ᵢ ℂ)
    (hzero : E (tip hbar coupling) = 0)
    (hagree : ∀ p : Point hbar coupling,
      E (p : Completed hbar coupling) = powerCoordinate hbar coupling α p) :
    α = 1 / 2 ∧ coupling = hbar ^ 2 / 4 := by
  have hr (p : Point hbar coupling) :
      Real.rpow (Complex.normSq p.value) α = ConeRadial.radialScale hbar coupling * ‖p.value‖ := by
    have he := E.dist_eq (p : Completed hbar coupling) (tip hbar coupling)
    rw [hagree, hzero, dist_zero_right, norm_powerCoordinate,
      ConeRadialCompletion.dist_coe_tip] at he
    exact he
  have hunit := hr ⟨1, one_ne_zero⟩
  have hs : ConeRadial.radialScale hbar coupling = 1 := by
    simpa only [Complex.normSq_one, Real.one_rpow, norm_one, mul_one, Real.rpow_eq_pow]
      using hunit.symm
  have htwo := hr ⟨2, by norm_num⟩
  have hpow : Real.rpow (4 : ℝ) α = Real.rpow 4 (1 / 2) := by
    norm_num [hs, Real.rpow_eq_pow] at htwo ⊢
    exact htwo
  have hα : α = 1 / 2 :=
    (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (4 : ℝ) ≠ 1)).mp hpow
  exact ⟨hα, (ConeRadial.radialScale_eq_one_iff hbar coupling Fact.out).mp hs⟩

/-- Within the specified degree-one power family, an actual Euclidean
isometric completion exists exactly for the Born exponent and Fisher coupling. -/
theorem exists_power_isometric_completion_iff (α : ℝ) :
    (∃ E : Completed hbar coupling ≃ᵢ ℂ,
      E (tip hbar coupling) = 0 ∧
      ∀ p : Point hbar coupling,
        E (p : Completed hbar coupling) = powerCoordinate hbar coupling α p) ↔
      α = 1 / 2 ∧ coupling = hbar ^ 2 / 4 := by
  constructor
  · rintro ⟨E, hzero, hagree⟩
    exact parameters_of_power_isometry hbar coupling α E hzero hagree
  · rintro ⟨rfl, hc⟩
    exact ⟨canonicalCompletionIsometry hbar coupling hc,
      canonicalCompletionIsometry_tip hbar coupling hc,
      canonicalCompletionIsometry_coe hbar coupling hc⟩

/-- The previously proved universal actual-differential condition is now
equivalent to existence of the genuine completed Euclidean isometry in the
same stipulated power family. Neither direction assumes the other as a premise. -/
theorem power_isometric_completion_iff_differential (α : ℝ) :
    (∃ E : Completed hbar coupling ≃ᵢ ℂ,
      E (tip hbar coupling) = 0 ∧
      ∀ p : Point hbar coupling,
        E (p : Completed hbar coupling) = powerCoordinate hbar coupling α p) ↔
    (∀ ρ : ℝ, 0 < ρ → ∀ Φ dρ dΦ : ℝ,
      Complex.normSq
        (fderiv ℝ (PowerMetric.powerField α (Prod.fst : ℝ × ℝ → ℝ) Prod.snd)
          (ρ, Φ) (dρ, dΦ)) =
        coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2) :=
  (exists_power_isometric_completion_iff hbar coupling α).trans
    (PowerMetric.powerMap_metric_iff α hbar coupling Fact.out Fact.out).symm

end FoliationQM.PowerConeCompletion
