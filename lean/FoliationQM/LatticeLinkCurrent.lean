module

public import FoliationQM.LatticePolarStencil

/-!
# Oriented probability current on the replicated lattice

Equation 9 of v13 associates a signed flux with an oriented pair of adjacent
sites. The current has the same value in the signed polar and complex wave
descriptions. At each clamped boundary the missing link is a self-link,
whose flux vanishes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeLinkCurrent

open LatticeConservation LatticeComplexEnergy LatticePolarStencil

/-- Physical link current directed from the first site to the second. -/
def link (p : MassiveParameters) (h Ra Rb φa φb : ℝ) : ℝ :=
  Ra * Rb * (p.ellC*p.c/h) * Real.sin (φb-φa)

/-- Rightward flux from the site to its replicated successor. -/
def plus {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  link p h (R i) (R (nextNode i)) (φ i) (φ (nextNode i))

/-- Rightward flux from the replicated predecessor into the site. -/
def minus {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  link p h (R (prevNode i)) (R i) (φ (prevNode i)) (φ i)

/-- The imaginary part of the ordered complex wave pairing gives the source sine current. -/
theorem link_eq_im (p : MassiveParameters) (h Ra Rb φa φb : ℝ) :
    link p h Ra Rb φa φb = p.ellC*p.c/h *
      (star ((Ra : ℂ) * phase φa) * ((Rb : ℂ) * phase φb)).im := by
  have hc : star ((Ra : ℂ) * phase φa) * ((Rb : ℂ) * phase φb) =
      Complex.ofReal (Ra*Rb) * phase (φb-φa) := by
    rw [star_mul, show star (Ra : ℂ) = (Ra : ℂ) from Complex.conj_ofReal _,
      ← relative_phase, Complex.ofReal_mul]
    ring
  simp only [link, hc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, PolarKahlerLattice.phase_im]
  ring

/-- The wave pairing for the flux on the right of a lattice site. -/
theorem plus_eq_im {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) :
    plus p h R φ i = p.ellC*p.c/h * (star (wave R φ i) * wave R φ (nextNode i)).im :=
  link_eq_im p h _ _ _ _

/-- The wave pairing for the flux on the left of a lattice site. -/
theorem minus_eq_im {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) :
    minus p h R φ i = p.ellC*p.c/h * (star (wave R φ (prevNode i)) * wave R φ i).im :=
  link_eq_im p h _ _ _ _

/-- Reversal of link orientation negates its flux for all real site amplitudes. -/
theorem link_antisymmetric (p : MassiveParameters) (h Ra Rb φa φb : ℝ) :
    link p h Rb Ra φb φa = -link p h Ra Rb φa φb := by
  unfold link
  rw [show φa-φb = -(φb-φa) by ring, Real.sin_neg]
  ring

/-- A link from a site to itself carries zero current. -/
theorem link_self (p : MassiveParameters) (h r θ : ℝ) : link p h r r θ θ = 0 := by
  simp [link]

/-- Flux at the outer face of the last, replicated site. -/
theorem plus_last {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin (n+1) → ℝ) :
    plus p h R φ (Fin.last n) = 0 := by
  have he : nextNode (Fin.last n) = Fin.last n := by simp [nextNode]
  rw [plus, he, link_self]

/-- Flux at the outer face of the first, replicated site. -/
theorem minus_first {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin (n+1) → ℝ) :
    minus p h R φ 0 = 0 := by
  have he : prevNode (0 : Fin (n+1)) = 0 := rfl
  rw [minus, he, link_self]

/-- Changing either signed polar representative preserves the link current
whenever the two endpoint waves are unchanged. -/
theorem link_congr_wave (p : MassiveParameters) (h Ra Rb φa φb Sa Sb θa θb : ℝ)
    (ha : (Ra : ℂ) * phase φa = (Sa : ℂ) * phase θa)
    (hb : (Rb : ℂ) * phase φb = (Sb : ℂ) * phase θb) :
    link p h Ra Rb φa φb = link p h Sa Sb θa θb := by
  rw [link_eq_im, ha, hb, ← link_eq_im]

/-- Both oriented face currents depend only on the reconstructed complex wave. -/
theorem plus_minus_congr_wave {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R φ S θ : Fin n → ℝ) (hw : wave R φ = wave S θ) :
    plus p h R φ = plus p h S θ ∧ minus p h R φ = minus p h S θ := by
  constructor <;> funext i
  · rw [plus_eq_im, hw, ← plus_eq_im]
  · rw [minus_eq_im, hw, ← minus_eq_im]

/-- The source's independent half-turn sign correction and whole-turn lift at
every site preserve both face currents, including on links incident to zeros. -/
theorem canonicalization {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R φ : Fin n → ℝ) (k : Fin n → ℤ) :
    let S := fun i => |R i|
    let θ := fun i => (φ i + Real.pi*(if R i < 0 then 1 else 0)) + (k i : ℝ)*(2*Real.pi)
    plus p h S θ = plus p h R φ ∧ minus p h S θ = minus p h R φ :=
  plus_minus_congr_wave p h _ _ R φ (wave_canonicalization R φ k)

/-- The graph current from the unit-mass continuity law is the physical
flux divided by the mesh width on each genuine neighboring pair. -/
theorem scaled_edgeCurrent_of_adjacent {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ : Fin n → ℝ) (i j : Fin n) (hij : i.val+1 = j.val ∨ j.val+1 = i.val) :
    h * edgeCurrent (pathCoupling (p.ellC*p.c/(2*h^2))) R φ i j =
      link p h (R i) (R j) (φ i) (φ j) := by
  unfold edgeCurrent pathCoupling link
  rcases hij with ha | ha
  · have hb : j.val+1 ≠ i.val := by omega
    simp only [ha, hb, ite_true, ite_false, add_zero]
    field_simp [hh.ne']
  · have hb : i.val+1 ≠ j.val := by omega
    simp only [ha, hb, ite_true, ite_false, zero_add]
    field_simp [hh.ne']

end FoliationQM.LatticeLinkCurrent
