module

public import FoliationQM.JointL2Sections

/-!
# The isometric passage from a joint wave to its remote fibers

For the two-particle wave in v13 `thm:entanglement_nosignaling`, taking
remote sections defines a complex linear isometry from the joint scalar
`L²` space to the iterated, Hilbert-valued `L²` space. Fubini identifies
the squared norms and transports equality of joint representatives to
almost every remote fiber.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointL2Curry

open MeasureTheory LorentzCoordinates JointL2Sections

/-- The squared norm in complex Hilbert-valued `L²` is the integral of the squared pointwise norms. -/
theorem norm_sq_integral {A H : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : Lp H 2 μ) :
    ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) u, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
  exact integral_congr_ae (ae_of_all _ fun a => (norm_sq_eq_re_inner (𝕜 := ℂ) (u a)).symm)

private theorem integrable_joint_sq (ψ : Joint) :
    Integrable (fun z : Spatial × Spatial => ‖ψ z‖ ^ 2) (volume.prod volume) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ)

private theorem sections_sq_ae (ψ : Joint) :
    (fun x => ‖sections ψ x‖ ^ 2) =ᵐ[volume] fun x => ∫ y, ‖ψ (x,y)‖ ^ 2 :=
  (memLp_ae ψ).mono (norm_sq_sections ψ)

/-- The family of remote sections is itself square integrable in the retained coordinate. -/
theorem sections_memLp (ψ : Joint) : MemLp (sections ψ) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (stronglyMeasurable_sections ψ).aestronglyMeasurable).mpr
    ((integrable_joint_sq ψ).integral_prod_left.congr (sections_sq_ae ψ).symm)

/-- The joint squared norm equals the integral of the squared fiber norms. -/
theorem norm_sq_eq_iterated (ψ : Joint) : ‖ψ‖ ^ 2 = ∫ x, ‖sections ψ x‖ ^ 2 :=
  (norm_sq_integral ψ).trans <| (integral_prod _ (integrable_joint_sq ψ)).trans
    (integral_congr_ae (sections_sq_ae ψ).symm)

private theorem sections_coe_ae (ψ : Joint) :
    ∀ᵐ x ∂volume, (sections ψ x : Spatial → ℂ) =ᵐ[volume] fun y => ψ (x,y) :=
  (memLp_ae ψ).mono (coe_sections ψ)

/-- Taking a section commutes almost everywhere with addition of joint waves. -/
theorem sections_add (ψ φ : Joint) :
    sections (ψ + φ) =ᵐ[volume] sections ψ + sections φ := by
  have hadd := Measure.ae_ae_eq_curry_of_prod
    (μ := (volume : Measure Spatial)) (ν := (volume : Measure Spatial)) (Lp.coeFn_add ψ φ)
  filter_upwards [sections_coe_ae (ψ + φ), sections_coe_ae ψ, sections_coe_ae φ, hadd]
    with x hs hψ hφ hx
  exact Lp.ext <| hs.trans <| hx.trans <| (hψ.add hφ).symm.trans
    (Lp.coeFn_add (sections ψ x) (sections φ x)).symm

/-- Taking a section commutes almost everywhere with complex scalar multiplication. -/
theorem sections_smul (c : ℂ) (ψ : Joint) :
    sections (c • ψ) =ᵐ[volume] c • sections ψ := by
  have hsmul := Measure.ae_ae_eq_curry_of_prod
    (μ := (volume : Measure Spatial)) (ν := (volume : Measure Spatial)) (Lp.coeFn_smul c ψ)
  filter_upwards [sections_coe_ae (c • ψ), sections_coe_ae ψ, hsmul] with x hs hψ hx
  apply Lp.ext
  filter_upwards [hs, hψ, hx, Lp.coeFn_smul c (sections ψ x)] with y hs' hψ' hx' hm
  change (c • ψ) (x,y) = c • ψ (x,y) at hx'
  change (c • sections ψ x) y = c • sections ψ x y at hm
  exact hs'.trans (hx'.trans ((congrArg (c • ·) hψ').symm.trans hm.symm))

/-- The iterated `L²` class of the remote section family. -/
def outerWave (ψ : Joint) : Outer := (sections_memLp ψ).toLp (sections ψ)

/-- The chosen representative of the iterated class agrees almost everywhere with the sections. -/
theorem outerWave_coe (ψ : Joint) :
    (outerWave ψ : Spatial → Remote) =ᵐ[volume] sections ψ :=
  (sections_memLp ψ).coeFn_toLp

/-- Currying joint scalar waves into Hilbert-valued waves is a complex linear isometry. -/
def curry : Joint →ₗᵢ[ℂ] Outer where
  toFun := outerWave
  map_add' ψ φ := Lp.ext <| (outerWave_coe _).trans <| (sections_add ψ φ).trans <|
    ((outerWave_coe ψ).add (outerWave_coe φ)).symm.trans (Lp.coeFn_add _ _).symm
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [outerWave_coe (c • ψ), sections_smul c ψ, outerWave_coe ψ,
      Lp.coeFn_smul c (outerWave ψ)] with x hs hψ hx hm
    exact hs.trans (hψ.trans ((congrArg (c • ·) hx).symm.trans hm.symm))
  norm_map' ψ := by
    change ‖outerWave ψ‖ = ‖ψ‖
    have hsq : ‖outerWave ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=
      (norm_sq_integral (outerWave ψ)).trans <| (integral_congr_ae <|
        (outerWave_coe ψ).mono fun x hx => congrArg (fun u => ‖u‖ ^ 2) hx).trans
        (norm_sq_eq_iterated ψ).symm
    simpa only [sq_eq_sq_iff_abs_eq_abs, abs_norm] using hsq

/-- The outer representative of the isometric image is the section family almost everywhere. -/
theorem coe_curry (ψ : Joint) : (curry ψ : Spatial → Remote) =ᵐ[volume] sections ψ :=
  outerWave_coe ψ

/-- The complex representative of the curried wave recovers the joint representative
almost everywhere in the remote variable for almost every retained position. -/
theorem coe_curry_joint (ψ : Joint) :
    ∀ᵐ x ∂volume, (curry ψ x : Spatial → ℂ) =ᵐ[volume] fun y => ψ (x,y) := by
  filter_upwards [coe_curry ψ, sections_coe_ae ψ] with x houter hinner
  change (curry ψ) x = sections ψ x at houter
  simpa only [houter] using hinner

/-- Currying the class of any square-integrable representative recovers that
representative on almost every fiber, independently of its null-set values. -/
theorem curry_toLp {f : Spatial × Spatial → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, (curry (hf.toLp f) x : Spatial → ℂ) =ᵐ[volume] fun y => f (x,y) := by
  have hrep := Measure.ae_ae_eq_curry_of_prod
    (μ := (volume : Measure Spatial)) (ν := (volume : Measure Spatial)) hf.coeFn_toLp
  filter_upwards [coe_curry_joint (hf.toLp f), hrep] with x hx he
  exact hx.trans he

end FoliationQM.JointL2Curry
