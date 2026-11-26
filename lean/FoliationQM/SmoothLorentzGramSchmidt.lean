module
public import FoliationQM.LorentzGramSchmidt
public import FoliationQM.SmoothSignedMetricProjection

/-!
# Smooth actual Lorentz Gram–Schmidt and its open domain

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
The four raw residuals and four normalized vectors are the literal verified
algebraic algorithm, applied to actual dependent sections and an actual smooth
bilinear Hom-bundle graph. Their regularity is proved recursively at every
point where the four computed signed squares are positive.

That pointwise regularity proves the exact positive-pivot domain is open.
No open normalization neighborhood, smooth output, symmetry, independence,
orientation, or future-cone conclusion is assumed. The original vector-bundle
topology and charts are retained, and no regularity is asserted across a zero
normalization denominator.
-/

@[expose] public section
noncomputable section
open Bundle Set
open scoped Manifold Bundle Topology
namespace FoliationQM.SmoothLorentzGramSchmidt

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞}
  (g : ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ)
  (s : Fin 4 → ∀ x : B, V x)

/-- The four actual raw residual sections of the explicit signed algorithm. -/
def raw (i : Fin 4) (x : B) : V x :=
  ![LorentzGramSchmidt.u0 (g x).toLinearMap₁₂ (fun j => s j x),
    LorentzGramSchmidt.u1 (g x).toLinearMap₁₂ (fun j => s j x),
    LorentzGramSchmidt.u2 (g x).toLinearMap₁₂ (fun j => s j x),
    LorentzGramSchmidt.u3 (g x).toLinearMap₁₂ (fun j => s j x)] i

/-- The literal four normalized output sections, in the original time-first order. -/
def normalized (i : Fin 4) (x : B) : V x :=
  LorentzGramSchmidt.frame (g x).toLinearMap₁₂ (fun j => s j x) i

/-- The actual signed metric square used by the corresponding normalization. -/
def signedSquare (i : Fin 4) (x : B) : ℝ :=
  (if i = 0 then 1 else -1) * g x (raw g s i x) (raw g s i x)

/-- The exact pointwise domain of the algebraic four-step algorithm. -/
def goodSet : Set B :=
  {x | LorentzGramSchmidt.Good (g x).toLinearMap₁₂ (fun j => s j x)}

/-- The actual normalization domain restricted to the original seed domain. -/
def domain (U : Set B) : Set B := U ∩ goodSet g s

omit [TopologicalSpace B] in
/-- Membership in the genuine algorithm domain is equivalent to positivity of its four explicitly computed signed squares. -/
theorem mem_goodSet_iff {x : B} :
    x ∈ goodSet g s ↔ ∀ i : Fin 4, 0 < signedSquare g s i x := by
  constructor
  · intro hx i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2
  · intro hx
    exact ⟨hx 0, hx 1, hx 2, hx 3⟩

private theorem contMDiffAt_stages {x : B}
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hs : ∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) x)
    (hx : x ∈ goodSet g s) :
    (∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, raw g s i y⟩ : TotalSpace F V)) x) ∧
    (∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, normalized g s i y⟩ : TotalSpace F V)) x) := by
  have h0 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.u0 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x := hs 0
  have he0 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.e0 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_normalize 1 hg h0 hx.1
  have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.u1 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_residual 1 hg he0 (hs 1)
  have he1 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.e1 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_normalize (-1) hg h1 hx.2.1
  have h2 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.u2 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_residual (-1) hg he1
      (SmoothSignedMetricProjection.contMDiffAt_residual 1 hg he0 (hs 2))
  have he2 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.e2 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_normalize (-1) hg h2 hx.2.2.1
  have h3 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.u3 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_residual (-1) hg he2
      (SmoothSignedMetricProjection.contMDiffAt_residual (-1) hg he1
        (SmoothSignedMetricProjection.contMDiffAt_residual 1 hg he0 (hs 3)))
  have he3 : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, LorentzGramSchmidt.e3 (g y).toLinearMap₁₂
        (fun j => s j y)⟩ : TotalSpace F V)) x :=
    SmoothSignedMetricProjection.contMDiffAt_normalize (-1) hg h3 hx.2.2.2
  constructor
  · intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro i
    fin_cases i
    · exact he0
    · exact he1
    · exact he2
    · exact he3

/-- Every actual raw residual graph is smooth at a point of the computed positive-pivot domain, by recursive evaluation of the original metric and section graphs. -/
theorem contMDiffAt_raw {x : B}
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hs : ∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) x)
    (hx : x ∈ goodSet g s) (i : Fin 4) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, raw g s i y⟩ : TotalSpace F V)) x :=
  (contMDiffAt_stages g s hg hs hx).1 i

/-- Each literal normalized section graph is smooth at every point where its four computed signed squares are positive; no smoothness or openness of the output domain is a premise. -/
theorem contMDiffAt_normalized {x : B}
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hs : ∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) x)
    (hx : x ∈ goodSet g s) (i : Fin 4) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, normalized g s i y⟩ : TotalSpace F V)) x :=
  (contMDiffAt_stages g s hg hs hx).2 i

/-- The actual signed square of every residual is smooth at points of the true algorithm domain, so positivity there persists locally. -/
theorem contMDiffAt_signedSquare {x : B}
    (hg : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) x)
    (hs : ∀ i : Fin 4, ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) x)
    (hx : x ∈ goodSet g s) (i : Fin 4) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (signedSquare g s i) x := by
  have hu := contMDiffAt_raw g s hg hs hx i
  exact (show ContDiff ℝ n (fun t : ℝ => (if i = 0 then 1 else -1) * t) by
    fun_prop).comp_contMDiffAt (SmoothSignedMetricProjection.contMDiffAt_pairing hg hu hu)

/-- Smooth metric and seed graphs on an original open domain make the exact four-positive-pivot normalization domain open; this is derived from pointwise stage regularity rather than assumed. -/
theorem isOpen_domain {U : Set B} (hU : IsOpen U)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) U)
    (hs : ∀ i : Fin 4, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) U) :
    IsOpen (domain g s U) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hgx := (hg x hx.1).contMDiffAt (hU.mem_nhds hx.1)
  have hsx (i : Fin 4) := (hs i x hx.1).contMDiffAt (hU.mem_nhds hx.1)
  have hp (i : Fin 4) : ∀ᶠ y in 𝓝 x, 0 < signedSquare g s i y :=
    continuousAt_const.eventually_lt
      (contMDiffAt_signedSquare g s hgx hsx hx.2 i).continuousAt
      ((mem_goodSet_iff g s).mp hx.2 i)
  filter_upwards [hU.mem_nhds hx.1, hp 0, hp 1, hp 2, hp 3] with y hy h0 h1 h2 h3
  exact ⟨hy, h0, h1, h2, h3⟩

/-- The four literal normalized sections are smooth on the derived open normalization domain inside the original seed domain. -/
theorem contMDiffOn_normalized {U : Set B} (hU : IsOpen U)
    (hg : ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, g y⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y : B => V y →L[ℝ] V y →L[ℝ] ℝ))) U)
    (hs : ∀ i : Fin 4, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, s i y⟩ : TotalSpace F V)) U)
    (i : Fin 4) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y => (⟨y, normalized g s i y⟩ : TotalSpace F V)) (domain g s U) := by
  intro x hx
  exact (contMDiffAt_normalized g s ((hg x hx.1).contMDiffAt (hU.mem_nhds hx.1))
    (fun j => (hs j x hx.1).contMDiffAt (hU.mem_nhds hx.1)) hx.2 i).contMDiffWithinAt

end FoliationQM.SmoothLorentzGramSchmidt
