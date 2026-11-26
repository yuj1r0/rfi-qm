module
public import FoliationQM.SmoothLorentzGramSchmidt
public import FoliationQM.SmoothFrameExtension
public import FoliationQM.LorentzGramSchmidtBasis

/-!
# Genuine local Lorentz frames from smooth signed normalization

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
Actual local seed sections are normalized by the verified four-step algorithm
on its computed open positive-pivot domain. The metric Gram identity and the
independent seed basis prove that the actual smooth output sections form a
basis. Their pointwise basis is exactly the algebraic Gram--Schmidt basis,
so its original exterior orientation is preserved.

An independently specified eta basis in one fiber has a genuine smooth
eta-normalized local extension through the original bundle trivialization.
The open neighborhood and its anchor membership are derived, and the anchor
basis is retained exactly. No smooth orthonormal tetrad, output basis,
positive-pivot neighborhood, future-cone regularity, or Spin lift is supplied
as an input. All topologies and bundle atlases remain the original ones.
-/

@[expose] public section
noncomputable section
open Bundle Set Module
open scoped Manifold Topology
namespace FoliationQM.SmoothLorentzLocalFrame
open LorentzMatrixGroup

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞}
  (g : ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ)
  {s : Fin 4 → ∀ x : B, V x} {U : Set B}

omit [TopologicalSpace B] in
/-- On the actual computed domain, the normalized sections have the original metric's exact Lorentz Gram matrix. -/
theorem normalized_gram (hSymm : ∀ x ∈ U, LinearMap.BilinForm.IsSymm (g x).toLinearMap₁₂)
    {x : B} (hx : x ∈ SmoothLorentzGramSchmidt.domain g s U) (a b : Fin 4) :
    g x (SmoothLorentzGramSchmidt.normalized g s a x)
      (SmoothLorentzGramSchmidt.normalized g s b x) = eta a b :=
  LorentzGramSchmidt.gram (g x).toLinearMap₁₂ (fun i => s i x) (hSymm x hx.1) hx.2 a b

/-- Smooth signed normalization yields a genuine local frame on its computed domain; neither independence nor spanning of the output is a premise. -/
theorem isLocalFrameOn_normalized (hU : IsOpen U)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x => (⟨x, g x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ))) U)
    (hs : IsLocalFrameOn I F n s U)
    (hSymm : ∀ x ∈ U, LinearMap.BilinForm.IsSymm (g x).toLinearMap₁₂) :
    IsLocalFrameOn I F n (SmoothLorentzGramSchmidt.normalized g s)
      (SmoothLorentzGramSchmidt.domain g s U) where
  linearIndependent := by
    intro x hx
    exact LorentzGramFamily.linearIndependent (g x).toLinearMap₁₂
      (fun i => SmoothLorentzGramSchmidt.normalized g s i x) (normalized_gram g hSymm hx)
  generating := by
    intro x hx
    let b := LorentzGramFamily.basisOfGram (g x).toLinearMap₁₂
      (fun i => SmoothLorentzGramSchmidt.normalized g s i x) (normalized_gram g hSymm hx)
      (hs.toBasisAt hx.1)
    have hb : ⇑b = fun i => SmoothLorentzGramSchmidt.normalized g s i x := by
      funext i
      exact LorentzGramFamily.basisOfGram_apply _ _ _ _ i
    rw [← hb, b.span_eq]
  contMDiffOn := SmoothLorentzGramSchmidt.contMDiffOn_normalized g s hU hg hs.contMDiffOn

/-- The actual local-frame output basis equals the algebraic normalized basis of the original local seed basis, with its literal vector coefficients unchanged. -/
theorem normalized_toBasisAt (hU : IsOpen U)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x => (⟨x, g x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ))) U)
    (hs : IsLocalFrameOn I F n s U)
    (hSymm : ∀ x ∈ U, LinearMap.BilinForm.IsSymm (g x).toLinearMap₁₂)
    {x : B} (hx : x ∈ SmoothLorentzGramSchmidt.domain g s U) :
    (isLocalFrameOn_normalized g hU hg hs hSymm).toBasisAt hx =
      LorentzGramSchmidtBasis.normalizedBasis (g x).toLinearMap₁₂ (hs.toBasisAt hx.1)
        (hSymm x hx.1) (by
          have he : ⇑(hs.toBasisAt hx.1) = fun i => s i x := funext (hs.toBasisAt_coe hx.1)
          rw [he]
          exact hx.2) := by
  apply DFunLike.ext
  intro i
  rw [IsLocalFrameOn.toBasisAt_coe, LorentzGramSchmidtBasis.normalizedBasis_apply]
  have he : ⇑(hs.toBasisAt hx.1) = fun j => s j x := funext (hs.toBasisAt_coe hx.1)
  rw [he]
  rfl

/-- The actual smooth local output basis preserves the original seed basis's exterior-form orientation on the exact computed domain. -/
theorem normalized_orientation (hU : IsOpen U)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x => (⟨x, g x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ))) U)
    (hs : IsLocalFrameOn I F n s U)
    (hSymm : ∀ x ∈ U, LinearMap.BilinForm.IsSymm (g x).toLinearMap₁₂)
    {x : B} (hx : x ∈ SmoothLorentzGramSchmidt.domain g s U) :
    ((isLocalFrameOn_normalized g hU hg hs hSymm).toBasisAt hx).orientation =
      (hs.toBasisAt hx.1).orientation := by
  rw [normalized_toBasisAt g hU hg hs hSymm hx]
  exact LorentzGramSchmidtBasis.orientation _ _ _ _

section Anchor
variable [ContMDiffVectorBundle n F V I]
  (hg : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun x => (⟨x, g x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ))))
  (x : B) (b : Basis (Fin 4) ℝ (V x))

/-- The computed open normalization domain of the original-trivialization extension of an independently supplied anchor basis. -/
def anchorDomain : TopologicalSpace.Opens B :=
  ⟨SmoothLorentzGramSchmidt.domain g (SmoothFrameExtension.frame (F := F) x b)
      (SmoothFrameExtension.domain (F := F) (V := V) x),
    SmoothLorentzGramSchmidt.isOpen_domain g (SmoothFrameExtension.frame (F := F) x b)
      (SmoothFrameExtension.domain (F := F) (V := V) x).isOpen hg.contMDiffOn
      (SmoothFrameExtension.contMDiffOn_frame (I := I) (n := n) x b)⟩

/-- An eta-normalized anchor basis belongs to its genuinely computed open normalization domain. -/
theorem mem_anchorDomain
    (hb : ∀ a c : Fin 4, g x (b a) (b c) = eta a c) :
    x ∈ anchorDomain g hg x b := by
  refine ⟨SmoothFrameExtension.mem_domain (F := F) x, ?_⟩
  apply LorentzGramSchmidt.good_of_gram
  intro a c
  simpa only [SmoothFrameExtension.frame_at, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using hb a c

/-- The actual normalized sections return the independently prescribed eta basis exactly at their anchor. -/
theorem normalized_anchor
    (hb : ∀ a c : Fin 4, g x (b a) (b c) = eta a c) (i : Fin 4) :
    SmoothLorentzGramSchmidt.normalized g (SmoothFrameExtension.frame (F := F) x b) i x = b i := by
  have he : (fun j => SmoothFrameExtension.frame (F := F) x b j x) = ⇑b := by
    funext j
    exact SmoothFrameExtension.frame_at (F := F) x b j
  change LorentzGramSchmidt.frame (g x).toLinearMap₁₂
    (fun j => SmoothFrameExtension.frame (F := F) x b j x) i = b i
  rw [he, LorentzGramSchmidt.frame_eq_of_gram _ _ hb]

/-- The actual normalized extension is a smooth local frame on the computed open neighborhood, derived from original metric and bundle regularity. -/
theorem isLocalFrameOn_anchor (hSymm : ∀ y, LinearMap.BilinForm.IsSymm (g y).toLinearMap₁₂) :
    IsLocalFrameOn I F n
      (SmoothLorentzGramSchmidt.normalized g (SmoothFrameExtension.frame (F := F) x b))
      (anchorDomain g hg x b) :=
  isLocalFrameOn_normalized g (SmoothFrameExtension.domain (F := F) (V := V) x).isOpen
    hg.contMDiffOn (SmoothFrameExtension.isLocalFrameOn_frame (I := I) (n := n) x b)
    (fun y _ => hSymm y)

/-- The full actual normalized local-frame basis at an eta anchor is exactly the independently prescribed original basis. -/
theorem anchor_toBasisAt (hSymm : ∀ y, LinearMap.BilinForm.IsSymm (g y).toLinearMap₁₂)
    (hb : ∀ a c : Fin 4, g x (b a) (b c) = eta a c) :
    (isLocalFrameOn_anchor g hg x b hSymm).toBasisAt (mem_anchorDomain g hg x b hb) = b := by
  apply DFunLike.ext
  intro i
  rw [IsLocalFrameOn.toBasisAt_coe]
  exact normalized_anchor g x b hb i

include hg in
/-- An independently specified eta basis has a genuine smooth eta-normalized local extension with exact anchor values, without assuming an orthonormal tetrad or a positive-pivot neighborhood. -/
theorem exists_normalized_extension (hSymm : ∀ y, LinearMap.BilinForm.IsSymm (g y).toLinearMap₁₂)
    (hb : ∀ a c : Fin 4, g x (b a) (b c) = eta a c) :
    ∃ W : TopologicalSpace.Opens B, x ∈ W ∧
      ∃ t : Fin 4 → ∀ y : B, V y, IsLocalFrameOn I F n t (W : Set B) ∧
        (∀ y ∈ W, ∀ a c : Fin 4, g y (t a y) (t c y) = eta a c) ∧
        ∀ i, t i x = b i := by
  refine ⟨anchorDomain g hg x b, mem_anchorDomain g hg x b hb,
    SmoothLorentzGramSchmidt.normalized g (SmoothFrameExtension.frame (F := F) x b),
    isLocalFrameOn_anchor g hg x b hSymm, ?_, normalized_anchor g x b hb⟩
  intro y hy a c
  exact normalized_gram g (fun z _ => hSymm z) hy a c

end Anchor
end FoliationQM.SmoothLorentzLocalFrame
