module

public import FoliationQM.TwoBodySchrodingerResidual
public import FoliationQM.TwoBodyMarginalContinuity

/-!
# The two-particle Schrödinger and Madelung equations

The real and imaginary parts of the rotated wave equation yield the two
real conservation and Hamilton–Jacobi equations wherever the amplitude
is nonzero. A positive density at the point suffices for its square-root
chart, including the derivatives of the physical currents.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyMadelung

open MeasureTheory LorentzCoordinates ObserverGaussianFisher MasterMetricAndCone
open TwoBodyCoordinates TwoBodyActionDensity TwoBodyPolarWave TwoBodyPolarContinuity
open TwoBodySchrodingerResidual MarginalParameterIntegral
open scoped Topology BigOperators

/-- The source Schrödinger equation with the two independent Cartesian Laplacians. -/
def Equation (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) : Prop :=
  Complex.I * (h : ℂ) * Dt ψ p =
    -((h ^ 2 / (2 * m₁) : ℝ) : ℂ) * lap₁ ψ p -
      ((h ^ 2 / (2 * m₂) : ℝ) : ℂ) * lap₂ ψ p + (V p : ℂ) * ψ p

/-- Summing the two three-axis sectors gives the printed differential equation. -/
theorem equation_iff (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) :
    Equation h m₁ m₂ V ψ p ↔ schrodinger h m₁ m₂ V ψ p = 0 := by
  rw [schrodinger_laplacians]
  unfold Equation
  constructor <;> intro he <;> linear_combination he

/-- In local potentials the Hamilton–Jacobi equation uses both phase-gradient norms
and the amplitude Laplacian divided by the amplitude for each particle. -/
theorem local_hamiltonJacobi (h m₁ m₂ : ℝ) (V₁ V₂ : Base → ℝ) (R S : Point → ℝ) (p : Point) :
    hamiltonJacobi h m₁ m₂ (localPotential V₁ V₂) R S p =
      Dt S p + (∑ i, (D₁ i S p)^2) / (2*m₁) + (∑ i, (D₂ i S p)^2) / (2*m₂) +
      V₁ p.1 + V₂ (p.1.1,p.2) -
      (h^2/(2*m₁)) * (lap₁ R p / R p) - (h^2/(2*m₂)) * (lap₂ R p / R p) := by
  simp only [hamiltonJacobi, quantum_laplacians, localPotential, Fintype.sum_sum_type,
    axis, mass, Sum.elim_inl, Sum.elim_inr, D₁, D₂, ← Finset.sum_div]
  ring

/-- The complex wave equation is equivalent to both real polar equations at a nonzero amplitude. -/
theorem polar_iff {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {R S : Point → ℝ} {p : Point} (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p)
    (hn : R p ≠ 0) :
    Equation h m₁ m₂ V (wave h R S) p ↔
      continuity m₁ m₂ (fun z => R z ^ 2) S p = 0 ∧ hamiltonJacobi h m₁ m₂ V R S p = 0 := by
  rw [equation_iff]
  obtain ⟨hr, hi⟩ := rotated_parts hh m₁ m₂ V hR hS hn
  have hr' : -R p ≠ 0 := neg_ne_zero.mpr hn
  have hi' : h / (2 * R p) ≠ 0 := div_ne_zero hh (mul_ne_zero (by norm_num) hn)
  constructor
  · intro he
    rw [he, mul_zero, Complex.zero_re] at hr
    rw [he, mul_zero, Complex.zero_im] at hi
    exact ⟨(mul_eq_zero.mp hi.symm).resolve_left hi', (mul_eq_zero.mp hr.symm).resolve_left hr'⟩
  · rintro ⟨hc, hq⟩
    rw [hc, mul_zero] at hi
    rw [hq, mul_zero] at hr
    exact (TwoBodyPolarSecondJet.rotate_eq_zero_iff _ _).mp (Complex.ext hr hi)

/-- Changing a density on the complement of a neighborhood preserves the full continuity residual. -/
theorem continuity_congr {ρ σ : Point → ℝ} {p : Point} (he : ρ =ᶠ[𝓝 p] σ)
    (m₁ m₂ : ℝ) (S : Point → ℝ) :
    continuity m₁ m₂ ρ S p = continuity m₁ m₂ σ S p := by
  have hf (j : Index) : flux m₁ m₂ ρ S j =ᶠ[𝓝 p] flux m₁ m₂ σ S j := by
    filter_upwards [he] with z hz
    simp only [flux, hz]
  simp only [continuity, Dt, D, he.fderiv_eq]
  congr 1
  exact Finset.sum_congr rfl fun j _ => congrArg (fun L : Point →L[ℝ] ℝ => L (axis j)) (hf j).fderiv_eq

/-- The two equations in the original density and phase hold exactly when
their square-root wave solves the Schrödinger equation on the positive chart. -/
theorem density_iff {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {ρ S : Point → ℝ} {p : Point} (hρ : ContDiffAt ℝ 2 ρ p) (hS : ContDiffAt ℝ 2 S p)
    (hp : 0 < ρ p) :
    Equation h m₁ m₂ V (wave h (fun z => √(ρ z)) S) p ↔
      continuity m₁ m₂ ρ S p = 0 ∧ hamiltonJacobi h m₁ m₂ V (fun z => √(ρ z)) S p = 0 := by
  have he : (fun z => √(ρ z) ^ 2) =ᶠ[𝓝 p] ρ := by
    filter_upwards [hρ.continuousAt.eventually (Ioi_mem_nhds hp)] with z hz
    exact Real.sq_sqrt hz.le
  rw [polar_iff hh m₁ m₂ V (hρ.sqrt hp.ne') hS (Real.sqrt_pos.mpr hp).ne',
    continuity_congr he]

/-- The printed local-potential wave equation gives exactly the two-particle divergence law
and the Hamilton–Jacobi–Bohm equation in the same positive density chart. -/
theorem local_equations {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V₁ V₂ : Base → ℝ)
    {ρ S : Point → ℝ} {p : Point} (hρ : ContDiffAt ℝ 2 ρ p) (hS : ContDiffAt ℝ 2 S p)
    (hp : 0 < ρ p) :
    Equation h m₁ m₂ (localPotential V₁ V₂) (wave h (fun z => √(ρ z)) S) p ↔
    TwoBodyMarginalContinuity.residual ρ (fun i z => (ρ z / m₁) * D₁ i S z)
      (fun i z => (ρ z / m₂) * D₂ i S z) p = 0 ∧
    Dt S p + (∑ i, (D₁ i S p)^2) / (2*m₁) + (∑ i, (D₂ i S p)^2) / (2*m₂) +
      V₁ p.1 + V₂ (p.1.1,p.2) -
      (h^2/(2*m₁)) * (lap₁ (fun z => √(ρ z)) p / √(ρ p)) -
      (h^2/(2*m₂)) * (lap₂ (fun z => √(ρ z)) p / √(ρ p)) = 0 := by
  rw [density_iff hh m₁ m₂ _ hρ hS hp, continuity_eq_residual, local_hamiltonJacobi]
  rfl

end FoliationQM.TwoBodyMadelung
