module

public import FoliationQM.RNCRadialGeodesic
public import FoliationQM.RNCRadialPolarization
public import FoliationQM.RNCHalfDensityJet

/-!
# The cyclic identity for a torsion-free radial normal connection

Polarizing the straight-line geodesic equation gives the vanishing connection
at the origin. Polarizing its first derivative gives the cyclic identity used
in the signed Ricci trace calculation in v13 Lemma 9.1.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCConnectionCyclic

open RNCHalfDensityJet RNCRadialGeodesic Filter
open scoped Topology

abbrev Coefficients := V → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A symmetric coordinate matrix induces a symmetric bilinear form. -/
theorem form_symmetric {A : Matrix (Fin 4) (Fin 4) ℝ} (hs : ∀ b c, A b c = A c b) (v w : V) :
    form A v w = form A w v := by
  rw [form_apply, form_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

/-- The radial equation and torsion symmetry force all Christoffel symbols to vanish at the origin. -/
theorem center_entries {G : Coefficients} (h : radialNormal G)
    (hs : ∀ r b c, G 0 r b c = G 0 r c b) (r b c : Fin 4) : G 0 r b c = 0 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := G 0 r
  have hb := RNCRadialPolarization.bilinear_eq_zero_of_diagonal (form A)
    (form_symmetric (hs r)) (fun z => (form_apply A z z).trans (center_contraction h z r))
  have he := congrArg (fun L : V →L[ℝ] V →L[ℝ] ℝ => L (Pi.single b 1) (Pi.single c 1)) hb
  exact (form_basis A b c).symm.trans he

/-- The first coordinate differential of the connection applied to three independent directions. -/
def derivativeForm (G : Coefficients) (r : Fin 4) (u v w : V) : ℝ :=
  form (fun b c => fderiv ℝ (fun y => G y r b c) 0 u) v w

/-- Evaluation of the connection differential is the double sum in the differentiated geodesic equation. -/
theorem derivativeForm_apply (G : Coefficients) (r : Fin 4) (u v w : V) :
    derivativeForm G r u v w = ∑ b, ∑ c, fderiv ℝ (fun y => G y r b c) 0 u * v b * w c :=
  form_apply (n := 4) _ v w

/-- The basis directions select the corresponding Christoffel coefficient. -/
theorem derivativeForm_basis (G : Coefficients) (r : Fin 4) (u : V) (b c : Fin 4) :
    derivativeForm G r u (Pi.single b 1) (Pi.single c 1) = fderiv ℝ (fun y => G y r b c) 0 u :=
  form_basis (n := 4) _ b c

/-- The directional derivative is additive in its differentiation argument. -/
theorem derivativeForm_add (G : Coefficients) (r : Fin 4) (u z v w : V) :
    derivativeForm G r (u + z) v w = derivativeForm G r u v w + derivativeForm G r z v w := by
  simp only [derivativeForm_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- Symmetry of the two connection slots near the center passes to the first differential. -/
theorem derivativeForm_symmetric {G : Coefficients}
    (hs : ∀ r b c, (fun y => G y r b c) =ᶠ[𝓝 0] (fun y => G y r c b))
    (r : Fin 4) (u v w : V) : derivativeForm G r u v w = derivativeForm G r u w v :=
  form_symmetric (fun b c => congrArg (fun L : V →L[ℝ] ℝ => L u) (hs r b c).fderiv_eq) v w

/-- Polarization of the differentiated radial equation forces the cyclic sum of first connection derivatives to vanish. -/
theorem cyclic_directions {G : Coefficients} (h : radialNormal G)
    (hd : ∀ r b c, DifferentiableAt ℝ (fun y => G y r b c) 0)
    (hs : ∀ r b c, (fun y => G y r b c) =ᶠ[𝓝 0] (fun y => G y r c b))
    (r : Fin 4) (u v w : V) :
    derivativeForm G r u v w + derivativeForm G r v w u + derivativeForm G r w u v = 0 := by
  apply RNCRadialPolarization.cyclic_of_diagonal
  · exact derivativeForm_add G r
  · intros
    simp only [derivativeForm, map_add, add_apply]
  · intros
    simp only [derivativeForm, map_add]
  · exact derivativeForm_symmetric hs r
  · intro z
    exact (derivativeForm_apply G r z z z).trans (derivative_contraction h hd z r)

/-- Evaluating on three coordinate axes yields the cyclic Christoffel derivative identity with the literal index order of the curvature convention. -/
theorem cyclic_entries {G : Coefficients} (h : radialNormal G)
    (hd : ∀ r b c, DifferentiableAt ℝ (fun y => G y r b c) 0)
    (hs : ∀ r b c, (fun y => G y r b c) =ᶠ[𝓝 0] (fun y => G y r c b))
    (r a b c : Fin 4) :
    fderiv ℝ (fun y => G y r b c) 0 (Pi.single a 1) +
    fderiv ℝ (fun y => G y r c a) 0 (Pi.single b 1) +
    fderiv ℝ (fun y => G y r a b) 0 (Pi.single c 1) = 0 := by
  simpa only [derivativeForm_basis] using
    cyclic_directions h hd hs r (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)

end FoliationQM.RNCConnectionCyclic
