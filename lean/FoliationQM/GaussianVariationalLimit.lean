module

public import FoliationQM.RelativeStationarySchrodingerLimit
public import FoliationQM.GaussianSchrodingerLimit

/-!
# The same Gaussian family from relative action to the Schrödinger limit

Source: v13 `cor:schrodinger`, component kinds C and D. One fixed positive
Gaussian width gives actual smooth original KG fields and their relative
stationarity. The same physical rest envelopes converge locally in L¹; the
variational source bridge yields their weak and classical Schrödinger limit.
The additional compact residual control comes from the proved spectral
estimates. No convergence of actions or global polar representation is used.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianVariationalLimit

open Filter Set PolarSecondDifferential ScalarLocalTesting
open GaussianSchrodingerLimit NonrelativisticParameterFamily
open RelativeStationaryAction RestEnvelopeKG LaboratoryKG
open Madelung (coordinateVector)
open scoped Topology ContDiff

/-- The same fixed-width Gaussian fields are genuinely relatively stationary and yield the weak and classical Schrödinger limit, with the separately proved compact residual control. -/
theorem stationary_limit (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    (∀ n, ContDiff ℝ ∞ (originalFamily p σ n) ∧
      RelativeStationaryOn (ramp p n) (originalFamily p σ n) coordinateVector univ) ∧
    ContDiff ℝ ∞ (limitField p σ) ∧
    LocalL1 univ (fun n => envelope (ramp p n) (originalFamily p σ n)) (limitField p σ) ∧
    WeakSchrodingerEquation.WeakEquation p (limitField p σ) (fun _ => 0) univ ∧
    (∀ K : Set Covector, IsCompact K →
      TendstoUniformlyOn
        (fun n => schrodingerResidual p (envelope (ramp p n) (originalFamily p σ n)))
        (fun _ => 0) atTop K) ∧
    ∀ x, Complex.I * (p.hbar : ℂ) *
        directionalDerivative (limitField p σ) (coordinateVector 0) x =
      -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian (limitField p σ) x) := by
  have hs := GaussianSpectralMoments.spectrum_data hσ
  have hsource (n : ℕ) : ContDiff ℝ ∞ (originalFamily p σ n) ∧
      ∀ x, FlatIntegrationByParts.kgOperator (ramp p n)
        (originalFamily p σ n) coordinateVector x = 0 := by
    have hd := SpectralRestEnvelope.source_data (ramp p n) hs.1 hs.2
    simpa only [originalFamily, GaussianPositiveFrequencyPacket.packet] using
      And.intro hd.1 hd.2.1
  have hψ : ∀ n, ∀ y ∈ (univ : Set Covector),
      ContDiffAt ℝ 2 (originalFamily p σ n) y := by
    intro n y _
    exact (hsource n).1.contDiffAt.of_le (by simp)
  have hstat : ∀ n, RelativeStationaryOn (ramp p n)
      (originalFamily p σ n) coordinateVector univ := by
    intro n
    apply (relativeStationaryOn_iff_kgOperator (ramp p n) isOpen_univ
      coordinateVector (hψ n)).2
    exact fun y _ => (hsource n).2 y
  have hc := GaussianSchrodingerLimit.controlled_limit p hσ
  have hr := ramp_spec p
  have hm : ∀ n, (ramp p n).m = p.m := fun n => (hr.1 n).1
  have hh : ∀ n, (ramp p n).hbar = p.hbar := fun n => (hr.1 n).2.1
  have hmap : ∀ n, MapsTo (LaboratoryCoordinates.toNormal (ramp p n).c)
      (univ : Set Covector) univ := fun _ _ _ => mem_univ _
  have hw := RelativeStationarySchrodingerLimit.weak_of_relative_stationary
    (P := ramp p) (V := fun _ => univ) p isOpen_univ (fun _ => isOpen_univ)
    hm hh hr.2 hmap hψ hstat hc.2.2.1
  have hpde := RelativeStationarySchrodingerLimit.classical_of_relative_stationary
    (P := ramp p) (V := fun _ => univ) p isOpen_univ (fun _ => isOpen_univ)
    hm hh hr.2 hmap hψ hstat hc.2.2.1
    (fun x _ => hc.2.1.contDiffAt.of_le (by simp))
  exact ⟨fun n => ⟨(hsource n).1, hstat n⟩, hc.2.1, hc.2.2.1, hw,
    hc.2.2.2.1, fun x => hpde x (mem_univ x)⟩

end FoliationQM.GaussianVariationalLimit
