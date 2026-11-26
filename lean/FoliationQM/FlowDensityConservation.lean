module

public import FoliationQM.SpatialFlowJacobian
public import FoliationQM.IntegralTrajectoryBound

/-!
# Density conservation along an actual smooth flow

The conservative continuity equation gives the material derivative of the
actual density. The actual spatial Jacobian evolution then cancels that
derivative. Closed-interval continuity includes both time endpoints.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FlowDensityConservation

open Set Filter MeasureTheory SpatialFlowJacobian
open scoped Topology BigOperators Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {D : ℝ × (Fin n → ℝ) → ℝ}
  {b : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
  {Phi : ℝ × (Fin n → ℝ) → (Fin n → ℝ)}
  {t T : ℝ} {x a : Fin n → ℝ}

/-- The divergence uses the actual spatial derivative of the velocity field. -/
def divergence (b : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, fderiv ℝ (b t) x (Pi.single i 1) i

/-- Restricting a genuine joint derivative to a spatial slice gives its spatial direction. -/
theorem fderiv_spatial_slice {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Fjoint : ℝ × E → F} {y : E}
    (hF : DifferentiableAt ℝ Fjoint (t, y)) (v : E) :
    fderiv ℝ (fun z => Fjoint (t, z)) y v = fderiv ℝ Fjoint (t, y) (0, v) := by
  have hf : HasFDerivAt (fun z => Fjoint (t, z))
      ((fderiv ℝ Fjoint (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    simpa only [Function.comp_def] using!
      hF.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  rw [hf.fderiv]
  rfl

/-- The product rule identifies the actual divergence of density times velocity. -/
theorem divergence_density_mul (hD : DifferentiableAt ℝ D (t, x))
    (hb : DifferentiableAt ℝ (b t) x) :
    (∑ i, fderiv ℝ (fun y => D (t, y) * b t y i) x (Pi.single i 1)) =
      fderiv ℝ D (t, x) (0, b t x) + D (t, x) * divergence b t x := by
  have hDs := hD.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have hcomp (i : Fin n) :
      fderiv ℝ (fun y => D (t, y) * b t y i) x (Pi.single i 1) =
        b t x i * fderiv ℝ D (t, x) (0, Pi.single i 1) +
          D (t, x) * fderiv ℝ (b t) x (Pi.single i 1) i := by
    have he := (hDs.mul (hasFDerivAt_pi'.mp hb.hasFDerivAt i)).fderiv
    simp only [Function.comp_def] at he
    change (fderiv ℝ ((fun y => D (t, y)) * (fun y => b t y i)) x) _ = _
    rw [he]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have hsplit : ((0 : ℝ), b t x) = ∑ i : Fin n, b t x i • (0, Pi.single i 1) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · ext j
      simp [Prod.snd_sum, Pi.single_apply]
  calc
    _ = (∑ i, b t x i * fderiv ℝ D (t, x) (0, Pi.single i 1)) +
        D (t, x) * divergence b t x := by
      simp_rw [hcomp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ = _ := by
      congr 1
      rw [hsplit, map_sum]
      simp only [map_smul, smul_eq_mul]

/-- The actual continuity equation and trajectory ODE imply the material density derivative. -/
theorem hasDerivAt_density_along_flow
    (hD : DifferentiableAt ℝ D (t, Phi (t, a)))
    (hb : DifferentiableAt ℝ (b t) (Phi (t, a)))
    (hODE : HasDerivAt (fun s => Phi (s, a)) (b t (Phi (t, a))) t)
    (hPDE : fderiv ℝ D (t, Phi (t, a)) (1, 0) +
      ∑ i, fderiv ℝ (fun y => D (t, y) * b t y i) (Phi (t, a)) (Pi.single i 1) = 0) :
    HasDerivAt (fun s => D (s, Phi (s, a)))
      (-D (t, Phi (t, a)) * divergence b t (Phi (t, a))) t := by
  have hpath : HasDerivAt (fun s => (s, Phi (s, a))) (1, b t (Phi (t, a))) t := by
    simpa only [id_eq] using! (hasDerivAt_id t).prodMk hODE
  have hd := hD.hasFDerivAt.comp_hasDerivAt t hpath
  have he : fderiv ℝ D (t, Phi (t, a)) (1, b t (Phi (t, a))) =
      -D (t, Phi (t, a)) * divergence b t (Phi (t, a)) := by
    rw [divergence_density_mul hD hb] at hPDE
    have hs : ((1 : ℝ), b t (Phi (t, a))) =
        (1, 0) + (0, b t (Phi (t, a))) := by simp
    rw [hs, map_add]
    linarith
  simpa only [he] using! hd

/-- The same actual divergence is the trace in Liouville's determinant formula. -/
theorem divergence_eq_trace (b : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (t : ℝ) (x : Fin n → ℝ) :
    divergence b t x = (coordinateMatrix (fderiv ℝ (b t) x)).trace := rfl

/-- The proved material derivative cancels the actual determinant Liouville derivative. -/
theorem hasDerivAt_density_jacobian_zero
    (hD : DifferentiableAt ℝ D (t, Phi (t, a)))
    (hb : DifferentiableAt ℝ (b t) (Phi (t, a)))
    (hODE : HasDerivAt (fun s => Phi (s, a)) (b t (Phi (t, a))) t)
    (hPDE : fderiv ℝ D (t, Phi (t, a)) (1, 0) +
      ∑ i, fderiv ℝ (fun y => D (t, y) * b t y i) (Phi (t, a)) (Pi.single i 1) = 0)
    (hJ : HasDerivAt (fun s => spatialJacobianDet Phi (s, a))
      (spatialJacobianDet Phi (t, a) * divergence b t (Phi (t, a))) t) :
    HasDerivAt (fun s => D (s, Phi (s, a)) * spatialJacobianDet Phi (s, a)) 0 t := by
  convert! (hasDerivAt_density_along_flow hD hb hODE hPDE).mul hJ using 1
  ring

/-- The actual conserved product includes both endpoints using continuity and the vector FTC. -/
theorem density_jacobian_eq_zero_time
    (hPhiC : ContinuousOn (fun s => Phi (s, a)) (Icc 0 T))
    (hDc : ∀ s ∈ Icc 0 T, ContinuousAt D (s, Phi (s, a)))
    (hJc : ContinuousOn (fun s => spatialJacobianDet Phi (s, a)) (Icc 0 T))
    (hD : ∀ s ∈ Ioo 0 T, DifferentiableAt ℝ D (s, Phi (s, a)))
    (hb : ∀ s ∈ Ioo 0 T, DifferentiableAt ℝ (b s) (Phi (s, a)))
    (hODE : ∀ s ∈ Ioo 0 T,
      HasDerivAt (fun τ => Phi (τ, a)) (b s (Phi (s, a))) s)
    (hPDE : ∀ s ∈ Ioo 0 T, fderiv ℝ D (s, Phi (s, a)) (1, 0) +
      ∑ i, fderiv ℝ (fun y => D (s, y) * b s y i) (Phi (s, a)) (Pi.single i 1) = 0)
    (hJ : ∀ s ∈ Ioo 0 T, HasDerivAt (fun τ => spatialJacobianDet Phi (τ, a))
      (spatialJacobianDet Phi (s, a) * divergence b s (Phi (s, a))) s) :
    ∀ t ∈ Icc 0 T,
      D (t, Phi (t, a)) * spatialJacobianDet Phi (t, a) =
        D (0, Phi (0, a)) * spatialJacobianDet Phi (0, a) := by
  have hc : ContinuousOn (fun s => D (s, Phi (s, a)) * spatialJacobianDet Phi (s, a))
      (Icc 0 T) := by
    intro s hs
    have hp : ContinuousWithinAt (fun τ => (τ, Phi (τ, a))) (Icc 0 T) s :=
      continuousWithinAt_id.prodMk (hPhiC s hs)
    exact (ContinuousAt.comp_continuousWithinAt
      (f := fun τ => (τ, Phi (τ, a))) (hDc s hs) hp).mul (hJc s hs)
  intro t ht
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => hasDerivAt_density_jacobian_zero
      (hD s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      (hb s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      (hODE s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      (hPDE s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      (hJ s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 t)
  rw [intervalIntegral.integral_zero] at hFTC
  exact sub_eq_zero.mp hFTC.symm

/-- Primitive smooth-flow, genuine inverse and initial-germ data imply the exact absolute-Jacobian density law. -/
theorem density_mul_abs_det_eq_initial (hT : 0 ≤ T)
    (hPhi : ∀ s ∈ Icc 0 T, ContDiffAt ℝ 2 Phi (s, a))
    (hD : ∀ s ∈ Icc 0 T, DifferentiableAt ℝ D (s, Phi (s, a)))
    (hb : ∀ s ∈ Ioo 0 T, DifferentiableAt ℝ (b s) (Phi (s, a)))
    (hODE : ∀ s ∈ Ioo 0 T, ∀ᶠ z in 𝓝 a,
      HasDerivAt (fun τ => Phi (τ, z)) (b s (Phi (s, z))) s)
    (hinv : ∀ s ∈ Icc 0 T, ∃ ψ : (Fin n → ℝ) → (Fin n → ℝ),
      DifferentiableAt ℝ ψ (Phi (s, a)) ∧ (fun z => ψ (Phi (s, z))) =ᶠ[𝓝 a] id)
    (hzero : (fun z => Phi (0, z)) =ᶠ[𝓝 a] id)
    (hPDE : ∀ s ∈ Ioo 0 T, fderiv ℝ D (s, Phi (s, a)) (1, 0) +
      ∑ i, fderiv ℝ (fun y => D (s, y) * b s y i) (Phi (s, a)) (Pi.single i 1) = 0) :
    ∀ t ∈ Icc 0 T,
      D (t, Phi (t, a)) * |spatialJacobianDet Phi (t, a)| = D (0, a) := by
  have hPhiC : ContinuousOn (fun s => Phi (s, a)) (Icc 0 T) := by
    intro s hs
    have hp : ContinuousAt (fun τ : ℝ => (τ, a)) s :=
      continuousAt_id.prodMk continuousAt_const
    exact (ContinuousAt.comp (f := fun τ : ℝ => (τ, a))
      (hPhi s hs).continuousAt hp).continuousWithinAt
  have hJc : ContinuousOn (fun s => spatialJacobianDet Phi (s, a)) (Icc 0 T) := by
    intro s hs
    exact (continuousAt_spatialJacobianDet (hPhi s hs)).continuousWithinAt
  have hJ : ∀ s ∈ Ioo 0 T, HasDerivAt (fun τ => spatialJacobianDet Phi (τ, a))
      (spatialJacobianDet Phi (s, a) * divergence b s (Phi (s, a))) s := by
    intro s hs
    obtain ⟨ψ, hψ, hleft⟩ := hinv s ⟨hs.1.le, hs.2.le⟩
    simpa only [divergence_eq_trace] using
      hasDerivAt_spatialJacobianDet (hPhi s ⟨hs.1.le, hs.2.le⟩)
        (hb s hs) (hODE s hs) hψ hleft
  have he := density_jacobian_eq_zero_time hPhiC (fun s hs => (hD s hs).continuousAt)
    hJc (fun s hs => hD s ⟨hs.1.le, hs.2.le⟩) hb
    (fun s hs => (hODE s hs).self_of_nhds) hPDE hJ
  have hz : Phi (0, a) = a := hzero.self_of_nhds
  have hj0 := spatialJacobianDet_zero
    ((hPhi 0 ⟨le_rfl, hT⟩).differentiableAt (by decide)) hzero
  intro t ht
  rw [abs_of_pos (spatialJacobianDet_pos hT hPhi hinv hzero t ht), he t ht, hz, hj0, mul_one]

end FoliationQM.FlowDensityConservation
