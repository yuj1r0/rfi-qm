module
public import FoliationQM.SpinAllCoverHTwo

/-!
# The universal property and exponent of all-cover Clifford sign cohomology

For the Spin-frame component of v13 `prop:takabayasi`, a family of
homomorphisms on anchored covers that agrees with restriction extends
uniquely over the all-cover group. The physical kernel has exponent two,
and so does its degree-two cohomology on every base.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinHTwoUniversal
open SpinHOneDirected SpinHTwoDirected SpinAllCoverHTwo SpinSignHTwo SpinSignCohomology

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Compatible homomorphisms on the cofinal anchored covers extend to the global group. -/
def descend {M : Type*} [Monoid M] (g : ∀ P : Cover B, ObstructionClass I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (SpinHTwoDirected.transition I n P Q h c) = g P c) : GlobalH2 I B n →* M where
  toFun := DirectLimit.lift _ (fun P c => g P c) (fun P Q h c => (hg P Q h c).symm)
  map_one' := DirectLimit.lift_one g _
  map_mul' := DirectLimit.lift_mul g _

/-- Evaluation on an anchored cover recovers its specified homomorphism. -/
theorem descend_ofPoint {M : Type*} [Monoid M] (g : ∀ P : Cover B, ObstructionClass I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (SpinHTwoDirected.transition I n P Q h c) = g P c) (P : Cover B) (c : ObstructionClass I P.domain n) :
    descend g hg (ofPoint P c) = g P c := rfl

/-- Agreement on all anchored covers determines a homomorphism on global sign cohomology. -/
theorem hom_ext {M : Type*} [Monoid M] {f g : GlobalH2 I B n →* M}
    (h : ∀ (P : Cover B) (c : ObstructionClass I P.domain n), f (ofPoint P c) = g (ofPoint P c)) : f = g := by
  ext c
  obtain ⟨P, a, rfl⟩ := exists_representative c
  exact h P a

/-- Every compatible family has exactly one extension. -/
theorem existsUnique_descend {M : Type*} [Monoid M] (g : ∀ P : Cover B, ObstructionClass I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (SpinHTwoDirected.transition I n P Q h c) = g P c) :
    ∃! F : GlobalH2 I B n →* M, ∀ (P : Cover B) (c : ObstructionClass I P.domain n), F (ofPoint P c) = g P c := by
  refine ⟨descend g hg, descend_ofPoint g hg, ?_⟩
  intro F hF
  exact hom_ext (fun P c => (hF P c).trans (descend_ofPoint g hg P c).symm)

/-- Every fixed-cover degree-two sign class squares to the identity. -/
theorem square_on_cover {ι : Type*} {U : ι → TopologicalSpace.Opens B} (c : ObstructionClass I U n) :
    c * c = 1 := by
  refine Quotient.inductionOn c ?_
  intro z
  change classOf (z * z) = classOf (neutralCocycle I U n)
  apply SignClassRestriction.classOf_eq_of_eqOn
  intro i j k x _ _ _
  change z.value i j k x * z.value i j k x = 1
  rcases CliffordSpinSignKernel.eq_one_or_generator (z.value i j k x) with h | h
  · rw [h, one_mul]
  · rw [h, ← pow_two, ← CliffordSpinSignKernel.generator_orderOf, pow_orderOf_eq_one]

/-- Every element of the all-cover degree-two sign group is its own inverse. -/
theorem global_square (c : GlobalH2 I B n) : c * c = 1 := by
  obtain ⟨P, a, rfl⟩ := exists_representative c
  rw [← map_mul, square_on_cover, map_one]

end FoliationQM.SpinHTwoUniversal
