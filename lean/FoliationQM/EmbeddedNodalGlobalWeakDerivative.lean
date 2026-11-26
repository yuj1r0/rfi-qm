module

public import FoliationQM.EmbeddedNodalWeakDerivative
public import FoliationQM.EmbeddedNodalNullity
public import FoliationQM.CurvedChartTestPartition

/-!
# Weak derivatives across a closed embedded nodal surface

Source: v13 `thm:wallstrom` Part(c), the conclusion "showing `ψ ∈ H¹_loc(𝓜)`
uniquely" of the distributional-derivative argument, component kinds C and D.
Let `𝒩` be the closed image of a smooth embedding of a surface in coordinate
four-space. A field that is square integrable on a set `U`, differentiable at
every point of `U` off `𝒩`, and whose classical directional derivative is
square integrable on `U`, satisfies the weak directional-derivative identity
against every smooth compact test supported in `U`. A square-integrable
differential representative agreeing with the classical differential off `𝒩`
gives the same identity, because `𝒩` is null.

The proof sums the local adapted-chart identities and ordinary integration by
parts away from `𝒩` over a smooth partition of unity. No chart, nullity,
cutoff estimate or partition is a hypothesis. This is a statement in ambient
coordinates with coordinate volume; Hilbert Sobolev membership and the wave
equation are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalGlobalWeakDerivative

open MeasureTheory Set Manifold RealLorentzFrame AdaptedChartWeakDerivative
open CurvedChartTestPartition
open scoped ContDiff Topology Manifold ComplexConjugate

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Integration by parts for a smooth compact test whose closed support lies
where the field is differentiable. -/
theorem integration_by_parts {η ψ : Covector → ℂ} {C : Set Covector}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ C)
    (hψ : MemLp ψ 2 (volume.restrict C))
    (hdiff : ∀ x ∈ tsupport η, DifferentiableAt ℝ ψ x) (v : Covector)
    (hD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict C)) :
    (∫ x, star (fderiv ℝ η x v) * ψ x) = -(∫ x, star (η x) * fderiv ℝ ψ x v) := by
  have Qψ := smooth_pairing hη hc hψ v
  have QD := smooth_pairing hη hc hD v
  have hL := supported_pair ((tsupport_fderiv_apply_subset ℝ v).trans hs) Qψ.2
  have hR := supported_pair hs QD.1
  have hP := supported_pair hs Qψ.1
  have hconj (x : Covector) :
      fderiv ℝ (fun y => conj (η y)) x v = star (fderiv ℝ η x v) :=
    ActionDensity.fderiv_conj_apply (hη.differentiable (by simp) x) v
  have hfi : Integrable (fun x => fderiv ℝ (fun y => conj (η y)) x v * ψ x) volume := by
    simpa only [hconj] using hL.1
  have hcs : tsupport (fun x => conj (η x)) ⊆ tsupport η :=
    tsupport_comp_subset (g := Complex.conjCLE) (map_zero _) _
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfi hR.1 hP.1
    (fun x _ => Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp x
      (hη.differentiable (by simp) x))
    (fun x hx => hdiff x (hcs hx))
  simp only [hconj] at H
  exact (neg_neg _).symm.trans (congrArg Neg.neg H.symm)

/-- A weak identity that holds for all tests supported in suitable open
neighbourhoods of the points of the support of a test holds for that test. -/
theorem weak_identity_of_local {φ ψ D : Covector → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hψ : MemLp ψ 2 (volume.restrict (tsupport φ)))
    (hD : MemLp D 2 (volume.restrict (tsupport φ))) (v : Covector)
    (hloc : ∀ x ∈ tsupport φ, ∃ W : Set Covector, IsOpen W ∧ x ∈ W ∧
      ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
        tsupport η ⊆ tsupport φ → tsupport η ⊆ W →
        (∫ y, star (fderiv ℝ η y v) * ψ y) = -(∫ y, star (η y) * D y)) :
    (∫ y, star (fderiv ℝ φ y v) * ψ y) = -(∫ y, star (φ y) * D y) := by
  classical
  choose! W hWo hxW hW using hloc
  let Ucov : Covector → Set Covector := fun x => if x ∈ tsupport φ then W x else (tsupport φ)ᶜ
  have ho : ∀ x, IsOpen (Ucov x) := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · simpa only [Ucov, hx, ite_true] using hWo x hx
    · simpa only [Ucov, hx, ite_false] using (isClosed_tsupport φ).isOpen_compl
  have hcov : univ ⊆ ⋃ x, Ucov x := by
    intro x _
    refine mem_iUnion_of_mem x ?_
    by_cases hx : x ∈ tsupport φ
    · simpa only [Ucov, hx, ite_true] using hxW x hx
    · have hU : Ucov x = (tsupport φ)ᶜ := by simp only [Ucov, hx, ite_false]
      rw [hU]
      exact hx
  obtain ⟨χ, hχ, -⟩ := exists_partition (I := 𝓘(ℝ, Covector)) (F := ℂ) (n := (⊤ : ℕ∞))
    Ucov ho hcov
  have hsm (η : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞)) : ContDiff ℝ ∞ η.val :=
    contMDiff_iff_contDiff.mp η.property.1
  let Λ : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞) →+ ℂ := AddMonoidHom.mk'
    (fun η => (∫ y in tsupport φ, star (fderiv ℝ η.val y v) * ψ y) +
      ∫ y in tsupport φ, star (η.val y) * D y) (by
    intro a b
    have Pa := smooth_pairing (hsm a) a.property.2 hψ v
    have Pb := smooth_pairing (hsm b) b.property.2 hψ v
    have Qa := smooth_pairing (hsm a) a.property.2 hD v
    have Qb := smooth_pairing (hsm b) b.property.2 hD v
    have e1 : (fun y => star (fderiv ℝ (a + b).val y v) * ψ y) = fun y =>
        star (fderiv ℝ a.val y v) * ψ y + star (fderiv ℝ b.val y v) * ψ y := by
      funext y
      rw [show (a + b).val = a.val + b.val from rfl,
        fderiv_add ((hsm a).differentiable (by simp) y) ((hsm b).differentiable (by simp) y)]
      simp only [add_apply, star_add, add_mul]
    have e2 : (fun y => star ((a + b).val y) * D y) = fun y =>
        star (a.val y) * D y + star (b.val y) * D y := by
      funext y
      simp only [show (a + b).val = a.val + b.val from rfl, Pi.add_apply, star_add, add_mul]
    change (∫ y in tsupport φ, star (fderiv ℝ (a + b).val y v) * ψ y) +
        (∫ y in tsupport φ, star ((a + b).val y) * D y) =
      ((∫ y in tsupport φ, star (fderiv ℝ a.val y v) * ψ y) +
        ∫ y in tsupport φ, star (a.val y) * D y) +
      ((∫ y in tsupport φ, star (fderiv ℝ b.val y v) * ψ y) +
        ∫ y in tsupport φ, star (b.val y) * D y)
    rw [e1, e2, integral_add Pa.2 Pb.2, integral_add Qa.1 Qb.1]
    ring)
  have hΛ : ∀ η : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞), tsupport η.val ⊆ tsupport φ →
      Λ η = (∫ y, star (fderiv ℝ η.val y v) * ψ y) + ∫ y, star (η.val y) * D y := by
    intro η hη
    have P := smooth_pairing (hsm η) η.property.2 hψ v
    have Q := smooth_pairing (hsm η) η.property.2 hD v
    change (∫ y in tsupport φ, star (fderiv ℝ η.val y v) * ψ y) +
      (∫ y in tsupport φ, star (η.val y) * D y) = _
    rw [(supported_pair ((tsupport_fderiv_apply_subset ℝ v).trans hη) P.2).2,
      (supported_pair hη Q.1).2]
  let Φ : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞) :=
    ⟨φ, contMDiff_iff_contDiff.mpr hφ, hc⟩
  have hzero : Λ Φ = 0 := by
    rw [variation_sum Λ χ Φ]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hpU : tsupport (piece χ Φ i).val ⊆ Ucov i := piece_tsupport χ Φ hχ i
    have hpK : tsupport (piece χ Φ i).val ⊆ tsupport φ :=
      tsupport_smul_subset_right (fun x => χ i x) φ
    rw [hΛ _ hpK]
    by_cases hi : i ∈ tsupport φ
    · have hpW : tsupport (piece χ Φ i).val ⊆ W i := by
        simpa only [Ucov, hi, ite_true] using hpU
      rw [hW i hi _ (hsm _) (piece χ Φ i).property.2 hpK hpW, neg_add_cancel]
    · have hempty : tsupport (piece χ Φ i).val = ∅ := by
        refine eq_empty_of_forall_notMem fun y hy => ?_
        have h1 : y ∈ (tsupport φ)ᶜ := by
          simpa only [Ucov, hi, ite_false] using hpU hy
        exact h1 (hpK hy)
      have hz : (piece χ Φ i).val = 0 := tsupport_eq_empty_iff.mp hempty
      simp [hz]
  rw [hΛ Φ subset_rfl] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- The classical directional derivative off a closed embedded surface is the
weak directional derivative across it, for every smooth compact test. -/
theorem weak_directional_identity {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    {φ ψ : Covector → ℂ} {U : Set Covector} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (hψ : MemLp ψ 2 (volume.restrict U))
    (hdiff : ∀ x ∈ U \ range f, DifferentiableAt ℝ ψ x) (v : Covector)
    (hD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict U)) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * fderiv ℝ ψ x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * fderiv ℝ ψ x v) := by
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hDK : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hD
  have Pψ := smooth_pairing hφ hc hψK v
  have PD := smooth_pairing hφ hc hDK v
  refine ⟨(supported_pair (tsupport_fderiv_apply_subset ℝ v) Pψ.2).1,
    (supported_pair (Subset.rfl : tsupport φ ⊆ tsupport φ) PD.1).1, ?_⟩
  refine weak_identity_of_local hφ hc hψK hDK v fun x hx => ?_
  by_cases hxN : x ∈ range f
  · obtain ⟨s, rfl⟩ := hxN
    obtain ⟨W, hWo, hsW, hW⟩ :=
      EmbeddedNodalWeakDerivative.exists_nhds_weak_directional_identity hf s
    exact ⟨W, hWo, hsW, fun η hη hηc hηK hηW =>
      (hW hη hηc (hηK.trans hs) hηW hψ hdiff v hD).2.2⟩
  · refine ⟨(range f)ᶜ, hN.isOpen_compl, hxN, fun η hη hηc hηK hηW => ?_⟩
    exact integration_by_parts hη hηc (hηK.trans hs) hψ
      (fun y hy => hdiff y ⟨hs (hηK hy), hηW hy⟩) v hD

/-- A square-integrable differential representative that is the classical
differential off the surface is a weak differential across it; its values on
the null surface are irrelevant. -/
theorem weak_of_representative {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    {φ ψ : Covector → ℂ} {U : Set Covector} {G : Covector → Covector →L[ℝ] ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (hderiv : ∀ x ∈ U \ range f, HasFDerivAt ψ (G x) x) (v : Covector) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * G x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * G x v) := by
  have hK : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hGK : MemLp G 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hG
  have hGv : MemLp (fun x => G x v) 2 (volume.restrict (tsupport φ)) :=
    (ContinuousLinearMap.apply ℝ ℂ v).comp_memLp' hGK
  have hoff : ∀ᵐ x ∂(volume : Measure Covector), x ∉ range f :=
    measure_eq_zero_iff_ae_notMem.mp (EmbeddedNodalNullity.volume_range_eq_zero hf)
  have hEq : (fun x => fderiv ℝ ψ x v) =ᵐ[volume.restrict (tsupport φ)] fun x => G x v := by
    filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hoff] with x hx hn
    exact congrArg (fun L : Covector →L[ℝ] ℂ => L v) (hderiv x ⟨hs hx, hn⟩).fderiv
  have hDK : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.ae_eq hEq.symm hGv
  have H := weak_directional_identity hf hN hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ) hψK
    (fun x hx => (hderiv x ⟨hs hx.1, hx.2⟩).differentiableAt) v hDK
  have hint : (fun x => star (φ x) * fderiv ℝ ψ x v) =ᵐ[volume] fun x => star (φ x) * G x v := by
    filter_upwards [(ae_restrict_iff' hK).mp hEq] with x hx
    by_cases hxK : x ∈ tsupport φ
    · rw [hx hxK]
    · simp only [image_eq_zero_of_notMem_tsupport hxK, star_zero, zero_mul]
  exact ⟨H.1, H.2.1.congr hint, by rw [← integral_congr_ae hint]; exact H.2.2⟩

end FoliationQM.EmbeddedNodalGlobalWeakDerivative
