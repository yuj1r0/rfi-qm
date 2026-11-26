module
public import FoliationQM.SpecialLinearFrameSmooth
public import FoliationQM.SpecialLinearConnection
public import FoliationQM.RicciRotation
/-!
# Actual Ricci rotation formulas for constructed determinant-one frames

Sources: v13 `eq:ricci_rotation_coeffs`, `eq:maurer_cartan_def`,
`eq:tetrad_rotor_map`, and `lem:maurer_cartan`. The matrix field is actually
differentiable and has determinant one on a neighborhood. Its real frame
entries are differentiable by the proved polynomial frame construction;
the actual gamma expansion and the body-generator expansion are derived.
The existing Ricci differentiation therefore applies with none of those
frame or generator identities supplied as premises.

Both conventions are explicit. The stored bodyOmega multiplies upper-index
sigma matrices. The source lower-gamma tetrad uses sourceFrame, and its
raised coefficients paired with sigmaLower are sourceOmega bodyOmega.
Both metric signs are retained in the corresponding Ricci formulas,
including the negative swapped derivative. No abstract Spin covering,
global bundle classification, or differential equation is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearRicci
open DiracMatrices SpinorMatrix SpecialLinearSpin SpecialLinearFrame
open SpecialLinearSpinDifferential SpecialLinearConnection RealLorentzFrame RicciRotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actually differentiable two-by-two matrix field has differentiable constructed real frame rows. -/
theorem differentiableAt_frame_row {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (a : Fin 4) :
    DifferentiableAt ℝ (fun y => frame (A y) a) x :=
  ((SpecialLinearFrameSmooth.contDiff_frame_row 1 a).differentiable (by norm_num)).differentiableAt.comp x hA

/-- Every entry of the actual constructed real frame is differentiable when its two-by-two matrix field is differentiable. -/
theorem differentiableAt_frame_entry {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (a mu : Fin 4) :
    DifferentiableAt ℝ (fun y => frame (A y) a mu) x :=
  differentiableAt_pi.mp (differentiableAt_frame_row hA a) mu

omit [NormedSpace ℝ E] in
/-- A local determinant-one matrix field has the actual real gamma expansion of its constructed frame throughout that neighborhood. -/
theorem eventual_frame_expansion {A : E → Mat2} {x : E}
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) :
    ∀ᶠ y in 𝓝 x, ∀ a, spin (A y) * gamma a * (spin (A y))⁻¹ =
      gammaExpansion (frame (A y) a) :=
  hdet.mono fun y hy a => SpecialLinearFrame.frame_expansion (A y) hy a

/-- The actual derivative of each constructed upper-gamma frame row is transported by its derived body coefficients. -/
theorem fderiv_frame_row {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (a : Fin 4) :
    fderiv ℝ (fun y => frame (A y) a) x v =
      fun nu => ∑ b, bodyOmega A x v b a * sign a * frame (A x) b nu := by
  exact RicciRotation.fderiv_row (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) a

/-- Every actual constructed frame entry has the explicit metric-contracted derivative dictated by its derived connection. -/
theorem fderiv_frame_entry {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (a nu : Fin 4) :
    fderiv ℝ (fun y => frame (A y) a nu) x v =
      ∑ b, ∑ c, bodyOmega A x v b c * (eta c a).re * frame (A x) b nu := by
  exact RicciRotation.fderiv_coefficients_apply (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) a nu

/-- The actual signed contraction of constructed frame rows and their derivatives recovers the body coefficient with both frame-index metric signs. -/
theorem ricci_contraction {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    (∑ nu, sign nu * frame (A x) d nu * fderiv ℝ (fun y => frame (A y) e nu) x v) =
      sign d * sign e * bodyOmega A x v d e := by
  exact RicciRotation.ricci_contraction (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

/-- The constructed real body coefficient is recovered from the actual upper-gamma frame derivative, with both metric signs explicit. -/
theorem ricci_rotation {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    bodyOmega A x v d e = sign d * sign e *
      (∑ nu, sign nu * frame (A x) d nu * fderiv ℝ (fun y => frame (A y) e nu) x v) := by
  exact RicciRotation.ricci_rotation (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

/-- The actual upper-gamma Ricci formula also has the antisymmetric negative swapped-derivative form. -/
theorem ricci_rotation_swapped {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    bodyOmega A x v d e = -(sign d * sign e *
      (∑ nu, sign nu * frame (A x) e nu * fderiv ℝ (fun y => frame (A y) d nu) x v)) := by
  exact RicciRotation.ricci_rotation_swapped (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

/-- The constructed lower-gamma source tetrad gives the actual conjugation of lowered gamma matrices, without a supplied expansion premise. -/
theorem source_frame_expansion (A : Mat2) (hdet : A.det = 1) (a : Fin 4) :
    spin A * gammaLower a * (spin A)⁻¹ =
      ∑ nu, (sourceFrame (frame A) a nu : ℂ) • gammaLower nu :=
  RicciRotation.sourceFrame_expansion (spin A) (frame A) (SpecialLinearFrame.frame_expansion A hdet) a

/-- The actual body connection has the source lowered-sigma expansion with the derived, correctly raised coefficient array. -/
theorem body_eq_source {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    MaurerCartanDifferential.body (fun y => spin (A y)) x v =
      ∑ a, ∑ b, (-Complex.I * (sourceOmega (bodyOmega A x v) a b : ℂ) / 4) • sigmaLower a b :=
  RicciRotation.body_eq_source v (bodyOmega A x v) (body_eq_generator hA hdet v)

/-- The actual lower-gamma source frame derivative is transported by the derived source coefficient array with its exact index sign. -/
theorem sourceFrame_transport {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (a nu : Fin 4) :
    fderiv ℝ (fun y => sourceFrame (frame (A y)) a nu) x v =
      ∑ b, sourceOmega (bodyOmega A x v) b a * sign a * sourceFrame (frame (A x)) b nu := by
  exact RicciRotation.sourceFrame_transport (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) a nu

/-- The actual lower-gamma source frame contraction recovers the derived stored upper-sigma body coefficient exactly. -/
theorem source_ricci_contraction {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    (∑ nu, sign nu * sourceFrame (frame (A x)) d nu *
      fderiv ℝ (fun y => sourceFrame (frame (A y)) e nu) x v) = bodyOmega A x v d e := by
  exact RicciRotation.source_ricci_contraction (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

/-- The actual source raised Ricci coefficient is the lower-gamma frame derivative contraction with both raised index signs. -/
theorem source_ricci_rotation {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    sourceOmega (bodyOmega A x v) d e = sign d * sign e *
      (∑ nu, sign nu * sourceFrame (frame (A x)) d nu *
        fderiv ℝ (fun y => sourceFrame (frame (A y)) e nu) x v) := by
  exact RicciRotation.source_ricci_rotation (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

/-- The same derived source coefficient equals the negative swapped lower-gamma frame derivative contraction. -/
theorem source_ricci_rotation_swapped {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (d e : Fin 4) :
    sourceOmega (bodyOmega A x v) d e = -(sign d * sign e *
      (∑ nu, sign nu * sourceFrame (frame (A x)) e nu *
        fderiv ℝ (fun y => sourceFrame (frame (A y)) d nu) x v)) := by
  exact RicciRotation.source_ricci_rotation_swapped (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) d e

end FoliationQM.SpecialLinearRicci
