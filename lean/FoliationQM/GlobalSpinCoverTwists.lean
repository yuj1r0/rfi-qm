module
public import FoliationQM.SmoothSpinHOneTorsor

/-!
# Comparing geometric twists presented on different covers

For the global Spin-frame component of v13 `prop:takabayasi`, two sign
cocycles on independently indexed covers can twist the same original
smooth lift. A diffeomorphism of the resulting physical Spin spaces
exists exactly when the signs agree in cohomology on a common refinement.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinCoverTwists
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SpinAllCoverHOne SpinSignHOne SpinSignOneCocycle SpinHOneRestriction
open GlobalSpinRealization SmoothSpinRelativeClass SmoothSpinHOneTorsor

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι κ τ σ : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  [IsManifold I n B] (A : SmoothLift I KP L n)
  {U : κ → TopologicalSpace.Opens B} (hU : ∀ x, ∃ i, x ∈ U i)
  {V : τ → TopologicalSpace.Opens B} (hV : ∀ x, ∃ i, x ∈ V i)

/-- Acting by a represented global sign gives the physical class of its explicit geometric realization. -/
theorem act_presented (z : Cocycle I U n) : act LM (ofCover U hU (classOf z)) (physicalClass A) =
    physicalClass (twistedFromCover LM A U hU z) :=
  (act_eq_iff LM _ _ _).mpr (relative_twistedFromCover LM A U hU z)

/-- An equivariant diffeomorphism over the original target between the two realized twists exists
exactly when the global classes of the presenting cocycles agree. -/
theorem twists_isomorphic_iff (z : Cocycle I U n) (w : Cocycle I V n) :
    Nonempty (SmoothBetween (twistedFromCover LM A U hU z) (twistedFromCover LM A V hV w)) ↔
    ofCover U hU (classOf z) = ofCover V hV (classOf w) := by
  let S := twistedFromCover LM A U hU z
  let T := twistedFromCover LM A V hV w
  have h : physicalClass S = physicalClass T ↔ Nonempty (SmoothBetween S T) := Quotient.eq
  apply h.symm.trans
  change physicalClass (twistedFromCover LM A U hU z) = physicalClass (twistedFromCover LM A V hV w) ↔ _
  rw [← act_presented LM A hU, ← act_presented LM A hV]
  exact (basedEquiv LM (physicalClass A)).injective.eq_iff

/-- Use any one specified common refinement of the two input covers to decide whether the
resulting geometric twists are physically isomorphic. -/
theorem twists_isomorphic_iff_common (W : σ → TopologicalSpace.Opens B) (hW : ∀ x, ∃ i, x ∈ W i)
    (p : σ → κ) (q : σ → τ) (hp : ∀ i, W i ≤ U (p i)) (hq : ∀ i, W i ≤ V (q i))
    (z : Cocycle I U n) (w : Cocycle I V n) :
    Nonempty (SmoothBetween (twistedFromCover LM A U hU z) (twistedFromCover LM A V hV w)) ↔
    restrictHom (⟨p, W, hW, hp⟩ : CliffordSpinCoverRefinement.Refinement U σ) (classOf z) =
      restrictHom (⟨q, W, hW, hq⟩ : CliffordSpinCoverRefinement.Refinement V σ) (classOf w) :=
  (twists_isomorphic_iff LM A hU hV z w).trans (ofCover_eq_iff_common hU hV W hW p q hp hq _ _)

end FoliationQM.GlobalSpinCoverTwists
