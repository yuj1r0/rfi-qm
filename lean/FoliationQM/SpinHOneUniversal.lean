module
public import FoliationQM.SpinAllCoverHOne

/-!
# The universal property and exponent of all-cover Clifford sign cohomology

For the Spin-frame component of v13 `prop:takabayasi`, a family of
homomorphisms on anchored covers that agrees with restriction extends
uniquely over the all-cover group. The physical kernel has exponent two,
and so does its degree-one cohomology on every base.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinHOneUniversal
open SpinHOneDirected SpinAllCoverHOne SpinSignHOne

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Compatible homomorphisms on the cofinal anchored covers extend to the global group. -/
def descend {M : Type*} [Monoid M] (g : ∀ P : Cover B, H1 I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (transition I n P Q h c) = g P c) : GlobalH1 I B n →* M where
  toFun := DirectLimit.lift _ (fun P c => g P c) (fun P Q h c => (hg P Q h c).symm)
  map_one' := DirectLimit.lift_one g _
  map_mul' := DirectLimit.lift_mul g _

/-- Evaluation on an anchored cover recovers its specified homomorphism. -/
theorem descend_ofPoint {M : Type*} [Monoid M] (g : ∀ P : Cover B, H1 I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (transition I n P Q h c) = g P c) (P : Cover B) (c : H1 I P.domain n) :
    descend g hg (ofPoint P c) = g P c := rfl

/-- Agreement on all anchored covers determines a homomorphism on global sign cohomology. -/
theorem hom_ext {M : Type*} [Monoid M] {f g : GlobalH1 I B n →* M}
    (h : ∀ (P : Cover B) (c : H1 I P.domain n), f (ofPoint P c) = g (ofPoint P c)) : f = g := by
  ext c
  obtain ⟨P, a, rfl⟩ := exists_representative c
  exact h P a

/-- Every compatible family has exactly one extension. -/
theorem existsUnique_descend {M : Type*} [Monoid M] (g : ∀ P : Cover B, H1 I P.domain n →* M)
    (hg : ∀ P Q h c, g Q (transition I n P Q h c) = g P c) :
    ∃! F : GlobalH1 I B n →* M, ∀ (P : Cover B) (c : H1 I P.domain n), F (ofPoint P c) = g P c := by
  refine ⟨descend g hg, descend_ofPoint g hg, ?_⟩
  intro F hF
  exact hom_ext (fun P c => (hF P c).trans (descend_ofPoint g hg P c).symm)

/-- Every fixed-cover class squares to the identity because its coefficients are physical Clifford signs. -/
theorem square_on_cover {ι : Type*} {U : ι → TopologicalSpace.Opens B} (c : H1 I U n) :
    c * c = 1 := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rw [← classOf_mul, ← classOf_unit I U n]
  apply classOf_eq_of_overlap
  intro i j x _ _
  change z.val.value i j x * z.val.value i j x = 1
  rcases CliffordSpinSignKernel.eq_one_or_generator (z.val.value i j x) with h | h
  · rw [h, one_mul]
  · rw [h, ← pow_two, ← CliffordSpinSignKernel.generator_orderOf, pow_orderOf_eq_one]

/-- Every element of the all-cover degree-one sign group is its own inverse. -/
theorem global_square (c : GlobalH1 I B n) : c * c = 1 := by
  obtain ⟨P, a, rfl⟩ := exists_representative c
  rw [← map_mul, square_on_cover, map_one]

end FoliationQM.SpinHOneUniversal
