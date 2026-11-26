module

public import FoliationQM.TwoBodyEulerLagrange
public import FoliationQM.TwoBodySourceVariations
public import FoliationQM.TwoBodyConditionalBohm

/-!
# Two-body Kähler linearization and variational stationarity

Both real fields vary independently in the printed time-slice action.
The fundamental lemma gives the two field equations, and the actual
polar substitution identifies them with the single complex wave equation.
The absolute formulation applies when the two background action terms
are integrable. The relative formulation uses compact changes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyKahlerStationarity

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyActions TwoBodyPolarWave
open TwoBodySchrodingerResidual TwoBodyPolarContinuity TwoBodyEulerLagrange
open scoped ContDiff

/-- Stationarity under independent compact smooth variations of the two fields
in the finite time-slice action from v13. -/
def SourceStationary (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ) : Prop :=
  (∀ a : Point → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a →
    HasDerivAt (fun s => sourceAction h m₁ m₂ V (fun z => ρ z + s*a z) S) 0 0) ∧
  (∀ b : Point → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b →
    HasDerivAt (fun s => sourceAction h m₁ m₂ V ρ (fun z => S z + s*b z)) 0 0)

/-- Stationarity under compact smooth complex wave variations in the absolute quadratic action. -/
def QuadraticStationary (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) : Prop :=
  ∀ η : Point → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
    HasDerivAt (fun s => quadraticAction h m₁ m₂ V (TwoBodyComplexVariation.variation s ψ η)) 0 0

private theorem same_variation {F G : ℝ → ℝ} {v : ℝ}
    (hF : HasDerivAt F v 0) (hG : HasDerivAt G v 0) :
    HasDerivAt F 0 0 ↔ HasDerivAt G 0 0 :=
  ⟨fun hz => hF.unique hz ▸ hG, fun hz => hG.unique hz ▸ hF⟩

/-- On finite backgrounds the printed and relative two-field stationarity conditions agree. -/
theorem source_iff_relative (h m₁ m₂ : ℝ) {V ρ S : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 2 S)
    (hC : Integrable (classicalDensity m₁ m₂ V ρ S)) (hF : Integrable (fisherL h m₁ m₂ ρ)) :
    SourceStationary h m₁ m₂ V ρ S ↔
      DensityStationary h m₁ m₂ V ρ S ∧ PhaseStationary h m₁ m₂ V ρ S := by
  have hS₁ : ContDiff ℝ 1 S := hS.of_le (by norm_num)
  have hρ₁ : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hd (a) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) := same_variation
    (TwoBodySourceVariations.density h m₁ m₂ hV hρ hp hS₁ (ha.of_le (by norm_num)) hc hC hF)
    (TwoBodyDensityVariation.hasDerivAt_relative h m₁ m₂ hV hρ hp hS₁ (ha.of_le (by norm_num)) hc)
  have hs (b) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) := same_variation
    (TwoBodySourceVariations.phase h m₁ m₂ hρ₁ hp hS (hb.of_le (by norm_num)) hc hC hF)
    (TwoBodyPhaseVariation.hasDerivAt_relative h m₁ m₂ V hρ₁ hS (hb.of_le (by norm_num)) hc)
  exact ⟨fun ⟨a,b⟩ => ⟨fun u hu hc => (hd u hu hc).mp (a u hu hc),
    fun u hu hc => (hs u hu hc).mp (b u hu hc)⟩,
    fun ⟨a,b⟩ => ⟨fun u hu hc => (hd u hu hc).mpr (a u hu hc),
    fun u hu hc => (hs u hu hc).mpr (b u hu hc)⟩⟩

/-- A finite quadratic action is stationary precisely when the complex wave
satisfies the printed two-Laplacian equation everywhere, including its nodes. -/
theorem quadratic_iff_equation (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 2 ψ) (hi : Integrable (complexL h m₁ m₂ V ψ)) :
    QuadraticStationary h m₁ m₂ V ψ ↔ ∀ p, TwoBodyMadelung.Equation h m₁ m₂ V ψ p := by
  have he (η) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) := same_variation
    (TwoBodyComplexVariation.first_variation_absolute h m₁ m₂ hV hψ (hη.of_le (by norm_num)) hc hi)
    (TwoBodyComplexVariation.first_variation h m₁ m₂ hV hψ (hη.of_le (by norm_num)) hc)
  have hrel : QuadraticStationary h m₁ m₂ V ψ ↔ ComplexStationary h m₁ m₂ V ψ :=
    ⟨fun q η hη hc => (he η hη hc).mp (q η hη hc), fun q η hη hc => (he η hη hc).mpr (q η hη hc)⟩
  rw [hrel, complex_iff h m₁ m₂ hV hψ]
  exact forall_congr' fun p => (TwoBodyMadelung.equation_iff h m₁ m₂ V ψ p).symm

/-- Independent relative stationarity is equivalent to the actual Schrödinger equation on a positive chart. -/
theorem relative_iff_equation {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) {V ρ S : Point → ℝ}
    (hV : Continuous V) (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 2 S) :
    (DensityStationary h m₁ m₂ V ρ S ∧ PhaseStationary h m₁ m₂ V ρ S) ↔
    ∀ p, TwoBodyMadelung.Equation h m₁ m₂ V (wave h (fun z => √(ρ z)) S) p := by
  rw [density_iff h m₁ m₂ hV hρ hp (hS.of_le (by norm_num)),
    phase_iff h m₁ m₂ V (hρ.of_le (by norm_num)) hS]
  have he (p) := TwoBodyMadelung.density_iff hh m₁ m₂ V (hρ.contDiffAt (x := p)) hS.contDiffAt (hp p)
  exact ⟨fun ⟨hq,hc⟩ p => (he p).mpr ⟨hc p,hq p⟩,
    fun hE => ⟨fun p => ((he p).mp (hE p)).2, fun p => ((he p).mp (hE p)).1⟩⟩

/-- The positive Kähler coordinate gives a C² wave from positive C² density and C² phase. -/
theorem contDiff_wave (h : ℝ) {ρ S : Point → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 2 S) :
    ContDiff ℝ 2 (wave h (fun z => √(ρ z)) S) := by
  have hR := hρ.sqrt fun p => (hp p).ne'
  exact (Complex.ofRealCLM.contDiff.comp hR).mul
    (((Complex.ofRealCLM.contDiff.comp (hS.div_const h)).mul (contDiff_const (c := Complex.I))).cexp)

/-- For the two local potentials the source and quadratic actions have equal
values and exactly corresponding stationary fields on a finite positive chart. -/
theorem kahler_linearization {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) {V₁ V₂ : Base → ℝ}
    (h₁ : Continuous V₁) (h₂ : Continuous V₂) {ρ S : Point → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 2 S)
    (hC : Integrable (classicalDensity m₁ m₂ (localPotential V₁ V₂) ρ S))
    (hF : Integrable (fisherL h m₁ m₂ ρ)) :
    let V := localPotential V₁ V₂
    let ψ := wave h (fun z => √(ρ z)) S
    quadraticAction h m₁ m₂ V ψ = sourceAction h m₁ m₂ V ρ S ∧
    (SourceStationary h m₁ m₂ V ρ S ↔ QuadraticStationary h m₁ m₂ V ψ) ∧
    (SourceStationary h m₁ m₂ V ρ S ↔ ∀ p, TwoBodyMadelung.Equation h m₁ m₂ V ψ p) := by
  intro V ψ
  have hV : Continuous V := (h₁.comp continuous_fst).add
    (h₂.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  have dρ := hρ.differentiable (by norm_num)
  have dS := hS.differentiable (by norm_num)
  have he := (source_iff_relative h m₁ m₂ hV hρ hp hS hC hF).trans
    (relative_iff_equation hh m₁ m₂ hV hρ hp hS)
  have hw := quadratic_iff_equation h m₁ m₂ hV (contDiff_wave h hρ hp hS)
    (quadratic_integrable hh m₁ m₂ V ρ S dρ dS hp hC hF)
  exact ⟨quadratic_eq_source hh m₁ m₂ V ρ S dρ dS hp hC hF, he.trans hw.symm, he⟩

end FoliationQM.TwoBodyKahlerStationarity
