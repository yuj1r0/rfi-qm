module

public import FoliationQM.MaurerCartanDifferential
public import FoliationQM.CliffordCommutators
public import FoliationQM.RealLorentzFrame
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual tetrad derivatives and Ricci rotation coefficients

Source: v13 `eq:ricci_rotation_coeffs` and its derivation in
`lem:maurer_cartan`. The transported frame and its expansion both use the
actual upper-index gamma matrices. The real antisymmetric array `omega`
is paired with upper-index sigma matrices in `generator omega`; the two
metric signs in the contracted Ricci formula are explicit. The lower-gamma
source tetrad and lowered-sigma coefficient convention are then connected
by actual index-lowering identities, including the corresponding derivative
and both Ricci formulas.

A local actual real frame expansion and an actual body-connection generator
expansion are premises. Neither the coefficient derivative nor the Ricci
formula is assumed. Differentiating the frame, injectivity of the real gamma
expansion and its derived Minkowski normalization give the conclusions.
General existence of a real gamma expansion or a spin-group reconstruction
is not claimed.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.RicciRotation
open DiracMatrices MaurerCartanDifferential CliffordCommutators RealLorentzFrame Matrix

private theorem contracted_gamma_sum (omega : Fin 4 → Fin 4 → ℝ) (A : Fin 4) :
    (∑ a, ∑ b, ((omega a b : ℂ)*eta b A) • gamma a) =
      ∑ a, ((omega a A*sign A : ℝ) : ℂ) • gamma a := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [eta, mul_ite, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : A=0 <;> simp [sign, h]

private theorem contracted_real_sum (omega : Fin 4 → Fin 4 → ℝ)
    (u : Fin 4 → Fin 4 → ℝ) (A nu : Fin 4) :
    (∑ a, ∑ b, omega a b*(eta b A).re*u a nu) =
      ∑ a, omega a A*sign A*u a nu := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [eta, apply_ite Complex.re, Complex.zero_re, mul_ite, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : A=0 <;> simp [sign, h]

private theorem gammaExpansion_sum_rows (c : Fin 4 → ℝ) (u : Fin 4 → Fin 4 → ℝ) :
    gammaExpansion (fun nu => ∑ a, c a*u a nu) =
      ∑ a, (c a : ℂ) • gammaExpansion (u a) := by
  simp only [gammaExpansion, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual derivative of the transported gamma frame has the real coefficient combination dictated by its actual body-generator expansion. -/
theorem fderiv_frame_coefficients {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (u : Fin 4 → Fin 4 → ℝ)
    (hframe : ∀ A, L x*gamma A*(L x)⁻¹=gammaExpansion (u A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (A : Fin 4) :
    fderiv ℝ (frame L (gamma A)) x v =
      gammaExpansion (fun nu => ∑ a, omega a A*sign A*u a nu) := by
  rw [fderiv_frame_body hL hunit, hbody, generator_gamma_commutator omega hanti A,
    contracted_gamma_sum, gammaExpansion_sum_rows]
  simp only [Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro a _
  rw [hframe a]

/-- Differentiating a local actual gamma expansion recovers the actual row derivative through the real continuous-linear gamma map. -/
theorem fderiv_local_frame_expansion {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (A : Fin 4) (v : E) :
    fderiv ℝ (frame L (gamma A)) x v =
      gammaExpansion (fderiv ℝ (fun y => u y A) x v) := by
  have hrow : DifferentiableAt ℝ (fun y => u y A) x := differentiableAt_pi.mpr (hu A)
  have heq : frame L (gamma A) =ᶠ[𝓝 x] (fun y => gammaExpansion (u y A)) :=
    hframe.mono fun y h => h A
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v) heq.fderiv_eq
  have hg : HasFDerivAt (fun y => gammaExpansion (u y A))
      (gammaExpansionCLM.comp (fderiv ℝ (fun y => u y A) x)) x := by
    simpa only [Function.comp_def, gammaExpansionCLM_apply] using!
      gammaExpansionCLM.hasFDerivAt.comp x hrow.hasFDerivAt
  rw [hg.fderiv] at hd
  exact hd

/-- The actual Frechet derivative of each coefficient row is the real Lorentz-generator transport derived from the local matrix identity. -/
theorem fderiv_row {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (A : Fin 4) :
    fderiv ℝ (fun y => u y A) x v =
      fun nu => ∑ a, omega a A*sign A*u x a nu := by
  apply gammaExpansion_injective
  rw [← fderiv_local_frame_expansion hu hframe A v]
  exact fderiv_frame_coefficients hL hunit (u x) hframe.self_of_nhds v omega hanti hbody A

/-- The actual derivative of every real tetrad coefficient has the source double contraction with the Minkowski metric. -/
theorem fderiv_coefficients_apply {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (A nu : Fin 4) :
    fderiv ℝ (fun y => u y A nu) x v =
      ∑ a, ∑ b, omega a b*(eta b A).re*u x a nu := by
  have hrow : DifferentiableAt ℝ (fun y => u y A) x := differentiableAt_pi.mpr (hu A)
  rw [fderiv_apply hrow nu]
  change (fderiv ℝ (fun y => u y A) x v) nu = _
  rw [fderiv_row hL hunit hu hframe v omega hanti hbody, contracted_real_sum]

private theorem contract_normalized_rows (s : Fin 4 → ℝ) (u : Fin 4 → Fin 4 → ℝ)
    (omega : Fin 4 → Fin 4 → ℝ) (d e : Fin 4)
    (hn : ∀ a, ∑ nu, s nu*u d nu*u a nu = if d=a then s d else 0) :
    (∑ nu, s nu*u d nu*(∑ a, omega a e*s e*u a nu)) = s d*s e*omega d e := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (omega a e*s e)*(∑ nu, s nu*u d nu*u a nu) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nu _
      ring
    _ = _ := by simp [hn]; ring

/-- The actual normalized tetrad derivative contracts to the body coefficients with both explicit metric signs. -/
theorem ricci_contraction {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    (∑ nu, sign nu*u x d nu*fderiv ℝ (fun y => u y e nu) x v) =
      sign d*sign e*omega d e := by
  have htransport (nu : Fin 4) : fderiv ℝ (fun y => u y e nu) x v =
      ∑ a, omega a e*sign e*u x a nu := by
    rw [fderiv_coefficients_apply hL hunit hu hframe v omega hanti hbody,
      contracted_real_sum]
  simp_rw [htransport]
  apply contract_normalized_rows
  intro a
  exact row_orthonormal_sum hunit hframe.self_of_nhds d a

/-- The Ricci rotation coefficient is recovered from the actual tetrad derivative by the signed Minkowski contraction. -/
theorem ricci_rotation {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    omega d e = sign d*sign e*
      (∑ nu, sign nu*u x d nu*fderiv ℝ (fun y => u y e nu) x v) := by
  rw [ricci_contraction hL hunit hu hframe v omega hanti hbody]
  by_cases hd : d=0 <;> by_cases he : e=0 <;> simp [sign, hd, he]

/-- Antisymmetry gives the source negative swapped-derivative Ricci formula for the same actual frame. -/
theorem ricci_rotation_swapped {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    omega d e = -(sign d*sign e*
      (∑ nu, sign nu*u x e nu*fderiv ℝ (fun y => u y d nu) x v)) := by
  calc
    omega d e = -omega e d := hanti d e
    _ = -(sign e*sign d*
        (∑ nu, sign nu*u x e nu*fderiv ℝ (fun y => u y d nu) x v)) := by
      rw [ricci_rotation hL hunit hu hframe v omega hanti hbody e d]
    _ = _ := by ring

/-- The source lower-gamma tetrad coefficients, with both frame and spacetime index signs explicit. -/
def sourceFrame (u : Fin 4 → Fin 4 → ℝ) (A nu : Fin 4) : ℝ := sign A*sign nu*u A nu

/-- The source coefficient array paired with lowered sigma matrices, obtained by raising both stored coefficient indices. -/
def sourceOmega (omega : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ := sign a*sign b*omega a b

/-- The actual lowered-index sigma matrix defined from the lowered gamma commutator. -/
def sigmaLower (a b : Fin 4) : Mat :=
  (Complex.I/2 : ℂ) • (gammaLower a*gammaLower b-gammaLower b*gammaLower a)

/-- Lowering an actual gamma index multiplies by its real diagonal Minkowski sign. -/
theorem gammaLower_eq_sign (a : Fin 4) : gammaLower a=(sign a : ℂ) • gamma a := by
  by_cases h : a=0 <;> simp [gammaLower, sign, h]

/-- The actual lowered sigma commutator equals the upper sigma matrix multiplied by both index signs. -/
theorem sigmaLower_eq_sign (a b : Fin 4) :
    sigmaLower a b=((sign a*sign b : ℝ) : ℂ) • sigma a b := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    simp [sigmaLower, sigma, gammaLower, sign, ha, hb, sub_eq_add_neg]

/-- The actual body generator has exactly the equivalent source expansion in lowered sigma matrices and the raised coefficient array. -/
theorem generator_eq_source (omega : Fin 4 → Fin 4 → ℝ) :
    generator omega=∑a, ∑b, (-Complex.I*(sourceOmega omega a b : ℂ)/4) • sigmaLower a b := by
  unfold generator
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [sigmaLower_eq_sign]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    simp [sourceOmega, sign, ha, hb, neg_div]

/-- Raising both real coefficient indices preserves their actual antisymmetry. -/
theorem sourceOmega_antisymmetric (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) (a b : Fin 4) :
    sourceOmega omega a b = -sourceOmega omega b a := by
  unfold sourceOmega
  rw [hanti a b]
  ring

/-- The converted real tetrad reconstructs the actual conjugation of lowered gamma matrices in the lowered gamma basis. -/
theorem sourceFrame_expansion (L : Mat) (u : Fin 4 → Fin 4 → ℝ)
    (hframe : ∀ A, L*gamma A*L⁻¹=gammaExpansion (u A)) (A : Fin 4) :
    L*gammaLower A*L⁻¹ = ∑nu, (sourceFrame u A nu : ℂ) • gammaLower nu := by
  rw [gammaLower_eq_sign, mul_smul_comm, smul_mul_assoc, hframe A,
    gammaExpansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro nu _
  rw [gammaLower_eq_sign]
  by_cases hA : A=0 <;> by_cases hnu : nu=0 <;>
    simp [sourceFrame, sign, hA, hnu]

/-- The actual Frechet derivative of a converted source coefficient carries its two constant index signs. -/
theorem fderiv_sourceFrame_apply {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (A nu : Fin 4) (hu : DifferentiableAt ℝ (fun y => u y A nu) x) (v : E) :
    fderiv ℝ (fun y => sourceFrame (u y) A nu) x v =
      sign A*sign nu*fderiv ℝ (fun y => u y A nu) x v := by
  have hd := congrArg (fun T : E →L[ℝ] ℝ => T v)
    (hu.hasFDerivAt.const_mul (sign A*sign nu)).fderiv
  simpa only [sourceFrame, _root_.smul_apply, smul_eq_mul] using hd

private theorem lower_contraction (u D : Fin 4 → Fin 4 → ℝ) (d e : Fin 4) :
    (∑ nu, sign nu*sourceFrame u d nu*sourceFrame D e nu) =
      sign d*sign e*(∑ nu, sign nu*u d nu*D e nu) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nu _
  by_cases hnu : nu=0
  · have hs : sign nu=1 := by simp [sign, hnu]
    simp only [sourceFrame, hs]
    ring
  · have hs : sign nu= -1 := by simp [sign, hnu]
    simp only [sourceFrame, hs]
    ring


/-- An actual body-connection expansion in upper sigma matrices becomes the exact source expansion in lowered sigma matrices. -/
theorem body_eq_source {L : E → Mat} {x : E} (v : E)
    (omega : Fin 4 → Fin 4 → ℝ) (hbody : body L x v=generator omega) :
    body L x v = ∑ a, ∑ b, (-Complex.I*(sourceOmega omega a b : ℂ)/4) • sigmaLower a b := by
  rw [hbody, generator_eq_source]

/-- The actual lower-gamma source tetrad derivative has the converted antisymmetric connection transport coefficients. -/
theorem sourceFrame_transport {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (A nu : Fin 4) :
    fderiv ℝ (fun y => sourceFrame (u y) A nu) x v =
      ∑ a, sourceOmega omega a A*sign A*sourceFrame (u x) a nu := by
  rw [fderiv_sourceFrame_apply A nu (hu A nu),
    fderiv_coefficients_apply hL hunit hu hframe v omega hanti hbody,
    contracted_real_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a=0 <;> by_cases hA : A=0 <;> by_cases hnu : nu=0 <;>
    simp [sourceOmega, sourceFrame, sign, ha, hA, hnu]

/-- The actual Minkowski contraction of the lower-gamma source frame and its derivative equals the stored upper-sigma coefficient array. -/
theorem source_ricci_contraction {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    (∑ nu, sign nu*sourceFrame (u x) d nu*
      fderiv ℝ (fun y => sourceFrame (u y) e nu) x v) = omega d e := by
  simp_rw [fderiv_sourceFrame_apply e _ (hu e _) v]
  change (∑ nu, sign nu*sourceFrame (u x) d nu*
    sourceFrame (fun A nu => fderiv ℝ (fun y => u y A nu) x v) e nu) = _
  rw [lower_contraction, ricci_contraction hL hunit hu hframe v omega hanti hbody]
  by_cases hd : d=0 <;> by_cases he : e=0 <;> simp [sign, hd, he]

/-- The source raised connection coefficient equals the actual lower-frame Ricci contraction with both raised frame-index signs. -/
theorem source_ricci_rotation {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    sourceOmega omega d e = sign d*sign e*
      (∑ nu, sign nu*sourceFrame (u x) d nu*
        fderiv ℝ (fun y => sourceFrame (u y) e nu) x v) := by
  rw [source_ricci_contraction hL hunit hu hframe v omega hanti hbody]
  rfl

/-- The same actual source Ricci coefficient equals the negative swapped lower-frame derivative contraction. -/
theorem source_ricci_rotation_swapped {L : E → Mat} {u : E → Fin 4 → Fin 4 → ℝ} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (d e : Fin 4) :
    sourceOmega omega d e = -(sign d*sign e*
      (∑ nu, sign nu*sourceFrame (u x) e nu*
        fderiv ℝ (fun y => sourceFrame (u y) d nu) x v)) := by
  calc
    sourceOmega omega d e = -sourceOmega omega e d := sourceOmega_antisymmetric omega hanti d e
    _ = -(sign e*sign d*
        (∑ nu, sign nu*sourceFrame (u x) e nu*
          fderiv ℝ (fun y => sourceFrame (u y) d nu) x v)) := by
      rw [source_ricci_rotation hL hunit hu hframe v omega hanti hbody e d]
    _ = _ := by ring

end FoliationQM.RicciRotation
