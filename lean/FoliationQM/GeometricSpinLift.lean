module
public import FoliationQM.GeometricPrincipalAtlas
public import FoliationQM.CliffordSpinSignKernel

/-!
# Geometric Spin lifts of independently specified principal bundles

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
Both total spaces, projections, and principal atlases are supplied independently
with their original topologies. A geometric lift is a continuous base-preserving
map equivariant for the actual Clifford Spin-to-Lorentz homomorphism. Its
surjectivity, literal two-sign fibers, and exact fiber cardinality are proved,
not supplied as assumptions. This does not assert that any such lift exists,
identify a Lorentz principal bundle with tangent frames, or yet prove the map
is a covering or a local diffeomorphism.
-/

@[expose] public section
noncomputable section
open Function
namespace FoliationQM.GeometricSpinLift
open CliffordSpinMap CliffordSpinLorentz CliffordSpinSignKernel LorentzMatrixGroup

variable {B Q P : Type*} [TopologicalSpace B] [TopologicalSpace Q] [TopologicalSpace P]
  {spinProj : Q → B} {frameProj : P → B} {ι κ : Type*}
  (S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι)
  (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ)

/-- A geometric lift between independent actual principal bundles: continuity, base preservation and equivariance for the genuine Clifford Lorentz homomorphism. -/
structure Map where
  /-- The map of the original total spaces. -/
  toFun : Q → P
  /-- Continuity in the original total-space topologies. -/
  continuous_toFun : Continuous toFun
  /-- Preservation of the original bundle projections. -/
  proj : ∀ q, frameProj (toFun q) = spinProj q
  /-- Equivariance for the original physical Clifford Spin-to-Lorentz homomorphism. -/
  equivariant : ∀ q s, toFun (S.right q s) = L.right (toFun q) (lorentzHom s)

namespace Map

instance : CoeFun (Map S L) (fun _ => Q → P) := ⟨Map.toFun⟩

variable {S L} (F : Map S L)

/-- Every geometric lift is surjective, derived from principal transitivity and surjectivity of the actual Clifford Lorentz homomorphism. -/
theorem surjective : Surjective F := by
  intro p
  obtain ⟨q, hq⟩ := S.proj_surjective (frameProj p)
  obtain ⟨g, hg, _⟩ := L.existsUnique_right (F q) p ((F.proj q).trans hq)
  obtain ⟨s, hs⟩ := lorentzHom_surjective g
  exact ⟨S.right q s, by rw [F.equivariant, hs, hg]⟩

/-- Translating an actual Spin frame preserves its geometric image exactly for elements of the physical central kernel. -/
theorem right_image_eq_iff (q : Q) (s : Spin) :
    F (S.right q s) = F q ↔ lorentzHom s = 1 := by
  rw [F.equivariant]
  constructor
  · intro h
    exact L.right_injective (F q) (h.trans (L.right_one (F q)).symm)
  · intro h
    rw [h, L.right_one]

/-- Two actual Spin frames have the same geometric image exactly when they are equal or differ by the literal negative Clifford unit. -/
theorem image_eq_iff (q r : Q) :
    F r = F q ↔ r = q ∨ r = S.right q CliffordSpinEquivalence.negativeOne := by
  constructor
  · intro he
    have hp : spinProj q = spinProj r :=
      (F.proj q).symm.trans ((congrArg frameProj he.symm).trans (F.proj r))
    obtain ⟨s, hs, _⟩ := S.existsUnique_right q r hp
    have hk : lorentzHom s = 1 := (F.right_image_eq_iff q s).mp (hs ▸ he)
    rcases (lorentzHom_eq_one_iff s).mp hk with h | h
    · exact Or.inl (hs.symm.trans (h ▸ S.right_one q))
    · exact Or.inr (hs.symm.trans (congrArg (S.right q) h))
  · rintro (rfl | rfl)
    · rfl
    · exact (F.right_image_eq_iff q _).mpr ((lorentzHom_eq_one_iff _).mpr (Or.inr rfl))

/-- The actual central sign operation on geometric Spin frames. -/
def sign (q : Q) : Q := S.right q CliffordSpinEquivalence.negativeOne

/-- The literal sign operation preserves the geometric Lorentz frame. -/
theorem image_sign (q : Q) : F (sign (S := S) q) = F q :=
  (F.image_eq_iff q _).mpr (Or.inr rfl)

/-- The literal sign operation has no fixed geometric Spin frame, by principality of the independently supplied Spin atlas. -/
theorem sign_ne (q : Q) : sign (S := S) q ≠ q := by
  intro he
  exact CliffordSpinEquivalence.negativeOne_ne_one
    (S.right_injective q (he.trans (S.right_one q).symm))

/-- Applying the literal Clifford sign twice returns the original geometric Spin frame. -/
theorem sign_sign (q : Q) : sign (S := S) (sign (S := S) q) = q := by
  have hg : generator * generator = 1 := by
    have h := pow_orderOf_eq_one generator
    rw [generator_orderOf, pow_two] at h
    exact h
  have hs : CliffordSpinEquivalence.negativeOne * CliffordSpinEquivalence.negativeOne = 1 :=
    congrArg (fun k : Kernel => k.val) hg
  simp only [sign, S.right_mul, hs, S.right_one]

/-- Kernel translation at a specified geometric Spin frame parametrizes its actual image fiber. -/
def kernelToFiber (q : Q) (k : Kernel) : {r : Q // F r = F q} :=
  ⟨S.right q k.val, (F.right_image_eq_iff q k.val).mpr k.property⟩

/-- The actual physical kernel parametrization of a geometric lift fiber is bijective. -/
theorem kernelToFiber_bijective (q : Q) : Bijective (F.kernelToFiber q) := by
  constructor
  · intro k l he
    exact Subtype.ext (S.right_injective q (congrArg Subtype.val he))
  · intro r
    have hp : spinProj q = spinProj r.val :=
      (F.proj q).symm.trans ((congrArg frameProj r.property.symm).trans (F.proj r.val))
    obtain ⟨s, hs, _⟩ := S.existsUnique_right q r.val hp
    have hk := (F.right_image_eq_iff q s).mp (hs ▸ r.property)
    exact ⟨⟨s, hk⟩, Subtype.ext hs⟩

/-- The genuine physical sign kernel is equivalent to the actual geometric image fiber through a specified Spin frame. -/
def kernelFiberEquiv (q : Q) : Kernel ≃ {r : Q // F r = F q} :=
  Equiv.ofBijective (F.kernelToFiber q) (F.kernelToFiber_bijective q)

/-- Every actual geometric lift fiber has exactly two elements, derived without assuming any fiber cardinality or covering property. -/
theorem fiber_card (p : P) : Nat.card {q : Q // F q = p} = 2 := by
  obtain ⟨q, rfl⟩ := F.surjective p
  exact (Nat.card_congr (F.kernelFiberEquiv q).symm).trans kernel_card

end Map
end FoliationQM.GeometricSpinLift
