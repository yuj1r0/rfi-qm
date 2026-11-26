module

public import FoliationQM.Conventions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The coefficient and tensor algebra of the tidal dispersion model

Source: v13 `thm:tidal_dispersion` (Conjecture 9.7), the derivation of
`eq:tidal_lagrangian_thm`, component kind A. With the proper-time variance
`⟨δτ²⟩ = ħ²/(4m²c⁴)` of the Compton geodesic-cell ansatz, averaging the
second-order normal-coordinate correction `(1/3) R_{μανβ} y^α y^β` of the
inverse metric over `y^α = u^α δτ` and contracting with `ħ²` times two
amplitude gradients gives `κ B_{μν} a^μ a^ν` with `κ = ħ⁴/(12m²c⁴)` and
`B_{μν} = R_{μανβ} u^α u^β`. Equivalently the coefficient is `ħ⁴/(12m²c²)`
times the gravito-electric tensor `E = c⁻² B`. Pair symmetry of the Riemann
components makes `B` symmetric, antisymmetry in the last pair makes it
transverse to `u`, and it vanishes when the curvature does.

These are algebraic identities for given components. The variance ansatz is
an input of the conjecture; nothing here supports it physically.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TidalCoefficient

open Finset

/-- The contraction `B_{μν} = R_{μανβ} u^α u^β` of curvature components with a velocity. -/
def contraction (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (u : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α, ∑ β, R μ α ν β * u α * u β

/-- The gravito-electric tidal tensor `E_{μν} = c⁻² R_{μανβ} u^α u^β`. -/
def tidalTensor (p : MassiveParameters) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (u : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  (p.c ^ 2)⁻¹ * contraction R u μ ν

/-- The proper-time variance of the Compton geodesic-cell ansatz. -/
def cellVariance (p : MassiveParameters) : ℝ := p.hbar ^ 2 / (4 * p.m ^ 2 * p.c ^ 4)

/-- The tidal coefficient `κ = ħ⁴/(12m²c⁴)`. -/
def kappa (p : MassiveParameters) : ℝ := p.hbar ^ 4 / (12 * p.m ^ 2 * p.c ^ 4)

/-- The coefficient arithmetic `ħ² · (1/3) · ħ²/(4m²c⁴) = ħ⁴/(12m²c⁴)`. -/
theorem kappa_eq (p : MassiveParameters) :
    p.hbar ^ 2 * (1 / 3 * cellVariance p) = kappa p := by
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  simp only [cellVariance, kappa]
  field_simp
  ring

/-- Averaging the normal-coordinate correction over the geodesic cell and
contracting with two amplitude gradients gives the tidal quadratic form. -/
theorem cell_average (p : MassiveParameters) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (u a : Fin 4 → ℝ) :
    p.hbar ^ 2 * ∑ μ, ∑ ν,
        (1 / 3 * ∑ α, ∑ β, R μ α ν β * (cellVariance p * u α * u β)) * a μ * a ν =
      kappa p * ∑ μ, ∑ ν, contraction R u μ ν * a μ * a ν := by
  rw [← kappa_eq]
  simp only [contraction, mul_sum, sum_mul]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun α _ =>
    sum_congr rfl fun β _ => ?_
  ring

/-- The same coefficient in terms of the gravito-electric tensor. -/
theorem kappa_contraction (p : MassiveParameters) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (u : Fin 4 → ℝ) (μ ν : Fin 4) :
    kappa p * contraction R u μ ν =
      p.hbar ^ 4 / (12 * p.m ^ 2 * p.c ^ 2) * tidalTensor p R u μ ν := by
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  simp only [kappa, tidalTensor]
  field_simp

/-- Pair symmetry of the curvature components makes the contraction symmetric. -/
theorem contraction_symm {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hpair : ∀ μ α ν β, R μ α ν β = R ν β μ α) (u : Fin 4 → ℝ) (μ ν : Fin 4) :
    contraction R u μ ν = contraction R u ν μ := by
  simp only [contraction]
  rw [sum_comm]
  refine sum_congr rfl fun β _ => sum_congr rfl fun α _ => ?_
  rw [hpair μ α ν β]
  ring

/-- Antisymmetry in the last index pair makes the contraction transverse to the velocity. -/
theorem contraction_transverse {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hanti : ∀ μ α ν β, R μ α ν β = -R μ α β ν) (u : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν, contraction R u μ ν * u ν = 0 := by
  have hS : ∑ ν, ∑ α, ∑ β, R μ α ν β * u α * u β * u ν =
      -(∑ ν, ∑ α, ∑ β, R μ α ν β * u α * u β * u ν) := by
    calc ∑ ν, ∑ α, ∑ β, R μ α ν β * u α * u β * u ν
        = ∑ α, ∑ ν, ∑ β, R μ α ν β * u α * u β * u ν := sum_comm
      _ = ∑ α, ∑ β, ∑ ν, R μ α ν β * u α * u β * u ν :=
          sum_congr rfl fun α _ => sum_comm
      _ = ∑ α, ∑ β, ∑ ν, -(R μ α β ν * u α * u ν * u β) :=
          sum_congr rfl fun α _ => sum_congr rfl fun β _ => sum_congr rfl fun ν _ => by
            rw [hanti μ α ν β]
            ring
      _ = -(∑ α, ∑ β, ∑ ν, R μ α β ν * u α * u ν * u β) := by
          simp only [sum_neg_distrib]
      _ = -(∑ ν, ∑ α, ∑ β, R μ α ν β * u α * u β * u ν) := by
          rw [sum_comm]
  have h0 : ∑ ν, ∑ α, ∑ β, R μ α ν β * u α * u β * u ν = 0 := by linarith
  simpa only [contraction, sum_mul] using h0

/-- The tidal contraction vanishes when the curvature components vanish. -/
theorem contraction_flat (u : Fin 4 → ℝ) (μ ν : Fin 4) :
    contraction (fun _ _ _ _ => 0) u μ ν = 0 := by
  simp [contraction]

end FoliationQM.TidalCoefficient
