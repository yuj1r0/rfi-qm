module
public import FoliationQM.SpinLorentzLocalDiffeomorph
public import FoliationQM.CliffordSpinManifold
public import FoliationQM.CliffordSpinRepresentation
public import FoliationQM.CliffordSpinCovering

/-!
# The genuine smooth Clifford Spin double covering

Source scope: the actual Clifford Spin/Lorentz frame identification in
v13 `prop:takabayasi`. The target is the independently constructed real
Lorentz Cayley manifold on the original proper future matrix group.
The explicit nonsingular Jacobian and local inverse theorem for the
actual special-linear representation, together with the proved genuine
Clifford Spin diffeomorphism, establish smooth local inverses for the
original Clifford Lorentz homomorphism. Its natural covering topology
and exact two-sign fibers are retained.

This is a smooth two-sheeted covering. Simple connectivity and the
universal-cover assertion, arbitrary geometric spacetime Spin structures,
and integrated variational Dirac dynamics remain separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CliffordSpinLorentzSmooth
open CliffordSpinMap CliffordSpinLorentz LorentzMatrixGroup

/-- The actual six-dimensional Clifford Spin manifold model. -/
abbrev spinModel := 𝓘(ℝ, CliffordSpinManifold.Model)

/-- The independently constructed six-dimensional real Lorentz Cayley model. -/
abbrev lorentzModel := LorentzManifold.model

/-- The original Clifford Lorentz homomorphism is smooth into the independent Lorentz manifold, with its actual physical matrix entries. -/
theorem contMDiff_lorentzHom (n : WithTop ℕ∞) :
    ContMDiff spinModel lorentzModel n lorentzHom :=
  LorentzManifold.contMDiff_iff_value.mpr
    (CliffordSpinRepresentation.contMDiff_lorentz_matrix n)

/-- The genuine Clifford Lorentz homomorphism has actual smooth local inverses for the independently fixed source and target atlases. -/
theorem lorentzHom_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph spinModel lorentzModel n lorentzHom := by
  intro s
  have h := ((CliffordSpinManifold.spinDiffeomorph n).isLocalDiffeomorph s).comp
    lorentzModel ProperFutureLorentz
    (SpinLorentzLocalDiffeomorph.properFutureHom_isLocalDiffeomorph n
      (CliffordSpinManifold.spinDiffeomorph n s))
  have he : SpinLorentzOrientation.properFutureHom ∘ CliffordSpinManifold.spinDiffeomorph n =
      lorentzHom := by
    funext x
    rfl
  rw [he] at h
  exact h

/-- The actual Clifford map is simultaneously a natural covering, an all-order local diffeomorphism, and exactly two-to-one over every Lorentz matrix. -/
theorem lorentzHom_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap lorentzHom ∧
      IsLocalDiffeomorph spinModel lorentzModel n lorentzHom ∧
      ∀ L : ProperFutureLorentz, Nat.card (lorentzHom ⁻¹' {L}) = 2 :=
  ⟨CliffordSpinCovering.lorentzHom_isCoveringMap,
    lorentzHom_isLocalDiffeomorph n, CliffordSpinCovering.lorentz_fiber_card⟩

/-- A genuine smooth partial inverse of the Clifford Lorentz map through any prescribed actual Spin lift. -/
def localInverse (n : WithTop ℕ∞) (s : Spin) :
    PartialDiffeomorph lorentzModel spinModel ProperFutureLorentz Spin n :=
  (lorentzHom_isLocalDiffeomorph n s).localInverse

/-- The Lorentz image of a prescribed Spin lift lies in its actual smooth inverse's open source. -/
theorem image_mem_localInverse_source (n : WithTop ℕ∞) (s : Spin) :
    lorentzHom s ∈ (localInverse n s).source :=
  (lorentzHom_isLocalDiffeomorph n s).localInverse_mem_source

/-- The actual smooth local inverse returns exactly its prescribed Clifford Spin anchor. -/
theorem localInverse_image (n : WithTop ℕ∞) (s : Spin) :
    localInverse n s (lorentzHom s) = s :=
  (lorentzHom_isLocalDiffeomorph n s).localInverse_left_inv
    (lorentzHom_isLocalDiffeomorph n s).localInverse_mem_target

/-- Projecting the actual smooth inverse recovers each Lorentz element in its genuine open domain. -/
theorem image_localInverse {n : WithTop ℕ∞} {s : Spin} {L : ProperFutureLorentz}
    (hL : L ∈ (localInverse n s).source) : lorentzHom (localInverse n s L) = L :=
  (lorentzHom_isLocalDiffeomorph n s).localInverse_right_inv hL

/-- The actual anchored Clifford Spin inverse is smooth on its full open source. -/
theorem contMDiffOn_localInverse (n : WithTop ℕ∞) (s : Spin) :
    ContMDiffOn lorentzModel spinModel n (localInverse n s) (localInverse n s).source :=
  (lorentzHom_isLocalDiffeomorph n s).contMDiffOn_localInverse

/-- Every genuine Spin lift extends to a smooth local section of the original Lorentz projection through that exact lift. -/
theorem exists_smooth_local_section (n : WithTop ℕ∞) (s : Spin) :
    ∃ U : Set ProperFutureLorentz, IsOpen U ∧ lorentzHom s ∈ U ∧
      ∃ f : ProperFutureLorentz → Spin, ContMDiffOn lorentzModel spinModel n f U ∧
        f (lorentzHom s) = s ∧ ∀ L ∈ U, lorentzHom (f L) = L := by
  refine ⟨(localInverse n s).source, (localInverse n s).open_source,
    image_mem_localInverse_source n s, localInverse n s,
    contMDiffOn_localInverse n s, localInverse_image n s, ?_⟩
  intro L hL
  exact image_localInverse hL

end FoliationQM.CliffordSpinLorentzSmooth
