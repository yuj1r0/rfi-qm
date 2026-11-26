module

public import FoliationQM.TidalAmplitudeVariation
public import FoliationQM.TidalCoefficient
public import FoliationQM.CurvedWaveDivergence

/-!
# The covariant form of the tidal density and divergence

Source: v13 `eq:tidal_lagrangian_thm` and `eq:tidal_KG_eq` (Conjecture 9.7),
component kinds A and C. The covariant divergence of a vector field is taken
in divergence form, `∇_μ V^μ = (√(-g))⁻¹ ∂_μ(√(-g) V^μ)`, the convention by
which the wave operator of this development is defined; the scalar wave
operator is the covariant divergence of the raised gradient. For the tidal
coefficient field `T^{μν} = κ √(-g) B^{μν}`:

* the tidal density is `κ √(-g) B^{μν} ∂_μ R ∂_ν R`;
* with indices raised by the inverse metric, `B^{μν} ∂_μ R ∂_ν R` is
  `B_{μν} ∇^μ R ∇^ν R`, so for `B_{μν} = R_{μανβ} u^α u^β` and
  `κ = ħ⁴/(12m²c⁴)` the density is the first line of the source display;
* the coordinate divergence `∂_μ(T^{μν} ∂_ν R)` is `κ √(-g)` times the
  covariant divergence `∇_μ(B^{μν} ∇_ν R)`.

The divergence-form expression is not rewritten with Christoffel
coefficients. The curvature components and the velocity are given fields;
nothing here supports the physical ansatz of the conjecture.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalCovariantDivergence

open Matrix LorentzMatrixGroup RNCVolumeDensity RNCCoordinateConnection RealLorentzFrame
open TidalAmplitudeVariation TidalCoefficient
open scoped Topology

variable {g Bup : Covector → Mat4} {R : Covector → ℝ} {x : Covector} {κ : ℝ}

/-- The covariant divergence of a vector field in divergence form. -/
def covariantDivergence (g : Covector → Mat4) (V : Covector → Fin 4 → ℝ) (x : Covector) : ℝ :=
  (volumeFactor (g x))⁻¹ * ∑ j, fderiv ℝ (fun y => volumeFactor (g y) * V y j) x (axis j)

/-- The scalar wave operator is the covariant divergence of the raised
gradient. -/
theorem wave_eq_covariantDivergence (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) :
    CurvedWaveDivergence.wave g f x =
      covariantDivergence g (fun y => (g y)⁻¹ *ᵥ grad f y) x := by
  have hfun (i : Fin 4) : (fun y => CurvedWaveDivergence.flux g f y i) =
      fun y => volumeFactor (g y) * ((g y)⁻¹ *ᵥ grad f y) i := by
    funext y
    simp only [CurvedWaveDivergence.flux, CurvedWaveDivergence.coefficient, mulVec, dotProduct,
      grad, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [CurvedWaveDivergence.wave, covariantDivergence, hfun, smul_eq_mul]

/-- The tidal coefficient field `κ √(-g) B^{μν}`. -/
def coefficientField (κ : ℝ) (g Bup : Covector → Mat4) (x : Covector) : Mat4 :=
  (κ * volumeFactor (g x)) • Bup x

/-- The coefficient field of a symmetric tensor is symmetric. -/
theorem coefficientField_isSymm (h : (Bup x).IsSymm) : (coefficientField κ g Bup x).IsSymm :=
  h.smul _

/-- The tidal density of the coefficient field is `κ √(-g) B^{μν} ∂_μ R ∂_ν R`. -/
theorem tidalDensity_coefficientField :
    tidalDensity (coefficientField κ g Bup) R x =
      κ * volumeFactor (g x) * (grad R x ⬝ᵥ (Bup x *ᵥ grad R x)) := by
  simp only [tidalDensity, coefficientField, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Raising the indices of a lower tensor with the inverse metric:
`B^{μν} ∂_μ R ∂_ν R = B_{μν} ∇^μ R ∇^ν R` with `∇^μ R = g^{μν} ∂_ν R`. -/
theorem raised_form (G B : Mat4) (v : Fin 4 → ℝ) :
    v ⬝ᵥ ((G⁻¹ᵀ * B * G⁻¹) *ᵥ v) = (G⁻¹ *ᵥ v) ⬝ᵥ (B *ᵥ (G⁻¹ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- Raising the indices of a symmetric lower tensor gives a symmetric upper
tensor. -/
theorem raised_isSymm {G B : Mat4} (hB : B.IsSymm) : (G⁻¹ᵀ * B * G⁻¹).IsSymm := by
  rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hB.eq, Matrix.mul_assoc]

/-- A bilinear form written with its components. -/
theorem form_sum (b : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    v ⬝ᵥ (Matrix.of b *ᵥ v) = ∑ μ, ∑ ν, b μ ν * v μ * v ν := by
  simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- The tidal Lagrangian density of the source:
`ħ⁴/(12m²c⁴) √(-g) R_{μανβ} u^α u^β ∇^μ R ∇^ν R`. -/
theorem tidal_lagrangian (p : MassiveParameters)
    (Riem : Covector → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (u : Covector → Fin 4 → ℝ) :
    tidalDensity (coefficientField (kappa p) g
        (fun y => (g y)⁻¹ᵀ * Matrix.of (contraction (Riem y) (u y)) * (g y)⁻¹)) R x =
      p.hbar ^ 4 / (12 * p.m ^ 2 * p.c ^ 4) * volumeFactor (g x) *
        ∑ μ, ∑ ν, contraction (Riem x) (u x) μ ν *
          ((g x)⁻¹ *ᵥ grad R x) μ * ((g x)⁻¹ *ᵥ grad R x) ν := by
  rw [tidalDensity_coefficientField, raised_form, form_sum, kappa]

/-- The coordinate divergence of the tidal flux of the coefficient field is
`κ √(-g)` times the covariant divergence `∇_μ(B^{μν} ∇_ν R)`. -/
theorem tidalDivergence_coefficientField (hvol : volumeFactor (g x) ≠ 0)
    (hV : ∀ j, DifferentiableAt ℝ
      (fun y => volumeFactor (g y) * (Bup y *ᵥ grad R y) j) x) :
    tidalDivergence (coefficientField κ g Bup) R x =
      κ * volumeFactor (g x) * covariantDivergence g (fun y => Bup y *ᵥ grad R y) x := by
  have hflux (j : Fin 4) : (fun y => tidalFlux (coefficientField κ g Bup) R y j) =
      fun y => κ * (volumeFactor (g y) * (Bup y *ᵥ grad R y) j) := by
    funext y
    simp only [tidalFlux, coefficientField, smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [tidalDivergence, covariantDivergence, hflux]
  have hd (j : Fin 4) : fderiv ℝ
      (fun y => κ * (volumeFactor (g y) * (Bup y *ᵥ grad R y) j)) x (axis j) =
      κ * fderiv ℝ (fun y => volumeFactor (g y) * (Bup y *ᵥ grad R y) j) x (axis j) := by
    rw [fderiv_const_mul (hV j)]
    simp only [_root_.smul_apply, smul_eq_mul]
  simp only [hd, ← Finset.mul_sum]
  field_simp

end FoliationQM.TidalCovariantDivergence
