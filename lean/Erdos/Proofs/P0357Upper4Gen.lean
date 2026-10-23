import Mathlib
import Erdos.Proofs.P0357Upper2
/-! Erdos 357, upper bound, round 4: a generic *band* packing lemma.

`Erdos357Upper.pattern_count2` (P0357Upper2) hard-wires two families of equal-sum run pairs.  Here
a *design* is a list of bands `(l, α, β)`: family `l` of patterns `Hit l w` (`[l w, l w + l]` and
`[(l+1) w + 1, (l+1) w + l]`, equal sums) for `w ∈ (α, β]`.  If every integer lies in at most `D`
of the chosen patterns, then `#patterns ≤ D * #holes`.  The per-integer degree bound is proved
band by band from three elementary facts (`cnt_zero`, `cnt_X1`, `cnt_Y2`) about where a band can
touch an integer; the concrete designs live in P0357Upper4.lean (generated). -/
namespace Erdos357Upper
open Finset

/-- Number of patterns `w ∈ (α, β]` of family `l` that contain `z`. -/
def cnt (l α β z : ℕ) : ℕ := ((Ioc α β).filter (fun w => Hit l w z)).card

/-- Weakening of the size bound. -/
theorem Adm.mono_n {a : ℕ → ℕ} {k n n' : ℕ} (H : Adm a k n) (h : n ≤ n') : Adm a k n' :=
  { pos := H.pos, mono := H.mono, le := fun i hi => (H.le i hi).trans h, inj := H.inj }

/-- One band: each of its patterns contains a hole, so `#patterns ≤ Σ_{holes} cnt`. -/
theorem band_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ l α β : ℕ} (hl : 1 ≤ l)
    (h1 : t < l * (α + 1)) (h2 : (l + 1) * β + l ≤ θ) :
    β - α ≤ ∑ z ∈ holes a k t θ, cnt l α β z := by
  classical
  have hex : ∀ w ∈ Ioc α β, 1 ≤ ((holes a k t θ).filter (fun z => Hit l w z)).card := by
    intro w hw
    have hw' := mem_Ioc.mp hw
    have e1 : l * (α + 1) ≤ l * w := Nat.mul_le_mul_left l hw'.1
    have e2 : (l + 1) * w ≤ (l + 1) * β := Nat.mul_le_mul_left (l + 1) hw'.2
    obtain ⟨z, hz, hzw⟩ := pattern_hit H hl (t := t) (θ := θ) (l := l) (w := w)
      (by omega) (by omega)
    exact card_pos.mpr ⟨z, mem_filter.mpr ⟨hz, hzw⟩⟩
  calc β - α = (Ioc α β).card := by simp
    _ = ∑ w ∈ Ioc α β, 1 := by simp
    _ ≤ ∑ w ∈ Ioc α β, ((holes a k t θ).filter (fun z => Hit l w z)).card := sum_le_sum hex
    _ = ∑ z ∈ holes a k t θ, cnt l α β z := by
        unfold cnt
        exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun w z => Hit l w z)

/-- A list of bands: total number of patterns `≤ Σ_{holes} (total degree)`. -/
theorem list_key {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ t < p.1 * (p.2.1 + 1) ∧ (p.1 + 1) * p.2.2 + p.1 ≤ θ) :
    (L.map (fun p => p.2.2 - p.2.1)).sum ≤
      ∑ z ∈ holes a k t θ, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hL p (List.mem_cons_self)
    have ih' := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    have hb := band_count H hp.1 hp.2.1 hp.2.2
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    exact Nat.add_le_add hb ih'

/-- **Packing count for a design.**  If every integer has total degree `≤ D`, then
`#patterns ≤ D * #holes`. -/
theorem list_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ D : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ t < p.1 * (p.2.1 + 1) ∧ (p.1 + 1) * p.2.2 + p.1 ≤ θ)
    (hfib : ∀ z, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum ≤ D) :
    (L.map (fun p => p.2.2 - p.2.1)).sum ≤ D * (holes a k t θ).card := by
  refine (list_key H L hL).trans ?_
  calc ∑ z ∈ holes a k t θ, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum
      ≤ ∑ z ∈ holes a k t θ, D := sum_le_sum (fun z _ => hfib z)
    _ = D * (holes a k t θ).card := by simp [mul_comm]

/-! ### Where can a band touch an integer? -/

/-- Y-hits of a band at `z`: `z ∈ [l w, l w + l]`. -/
def cY (l α β z : ℕ) : ℕ := ((Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l)).card

/-- X-hits of a band at `z`: `z ∈ [(l+1) w + 1, (l+1) w + l]`. -/
def cX (l α β z : ℕ) : ℕ :=
  ((Ioc α β).filter (fun w => (l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l)).card

theorem cnt_le_add (l α β z : ℕ) : cnt l α β z ≤ cY l α β z + cX l α β z := by
  classical
  unfold cnt cY cX
  have : (Ioc α β).filter (fun w => Hit l w z) =
      (Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l) ∪
        (Ioc α β).filter (fun w => (l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l) := by
    rw [← filter_or]
    rfl
  rw [this]
  exact card_union_le _ _

theorem cX_le_one (l α β z : ℕ) : cX l α β z ≤ 1 := by
  classical
  unfold cX
  apply card_le_one.mpr
  intro w1 h1 w2 h2
  rw [mem_filter] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left (l + 1) (Nat.succ_le_of_lt h)
    nlinarith [h1.2.1, h1.2.2, h2.2.1, h2.2.2]
  · have := Nat.mul_le_mul_left (l + 1) (Nat.succ_le_of_lt h)
    nlinarith [h1.2.1, h1.2.2, h2.2.1, h2.2.2]

theorem cY_le_two (l α β z : ℕ) (hl : 1 ≤ l) : cY l α β z ≤ 2 := by
  classical
  unfold cY
  have hsub : (Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l) ⊆ {z / l, z / l - 1} := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨_, h1, h2⟩ := hw
    have a1 : w ≤ z / l := (Nat.le_div_iff_mul_le hl).2 (by linarith)
    have a2 : z / l < w + 2 := (Nat.div_lt_iff_lt_mul hl).2 (by nlinarith)
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hsub).trans card_le_two

theorem cY_zero (l α β z : ℕ) (h : z < l * (α + 1) ∨ l * β + l < z) : cY l α β z = 0 := by
  classical
  unfold cY
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w hw
  have hw' := mem_Ioc.mp hw
  have e1 : l * (α + 1) ≤ l * w := Nat.mul_le_mul_left l hw'.1
  have e2 : l * w ≤ l * β := Nat.mul_le_mul_left l hw'.2
  rintro ⟨h1, h2⟩
  omega

theorem cX_zero (l α β z : ℕ) (h : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) :
    cX l α β z = 0 := by
  classical
  unfold cX
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w hw
  have hw' := mem_Ioc.mp hw
  have e1 : (l + 1) * (α + 1) ≤ (l + 1) * w := Nat.mul_le_mul_left (l + 1) hw'.1
  have e2 : (l + 1) * w ≤ (l + 1) * β := Nat.mul_le_mul_left (l + 1) hw'.2
  rintro ⟨h1, h2⟩
  omega

/-- Neither the Y-runs nor the X-runs of the band reach `z`. -/
theorem cnt_zero (l α β z : ℕ) (hY : z < l * (α + 1) ∨ l * β + l < z)
    (hX : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) : cnt l α β z = 0 := by
  have := cnt_le_add l α β z
  rw [cY_zero l α β z hY, cX_zero l α β z hX] at this
  omega

/-- Only the X-runs can reach `z`: degree `≤ 1`. -/
theorem cnt_X1 (l α β z : ℕ) (hY : z < l * (α + 1) ∨ l * β + l < z) : cnt l α β z ≤ 1 := by
  have := cnt_le_add l α β z
  have := cX_le_one l α β z
  rw [cY_zero l α β z hY] at *
  omega

/-- Only the Y-runs can reach `z`: degree `≤ 2`. -/
theorem cnt_Y2 (l α β z : ℕ) (hl : 1 ≤ l)
    (hX : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) : cnt l α β z ≤ 2 := by
  have := cnt_le_add l α β z
  have := cY_le_two l α β z hl
  rw [cX_zero l α β z hX] at *
  omega

/-- Both kinds can reach `z`: degree `≤ 3`. -/
theorem cnt_YX3 (l α β z : ℕ) (hl : 1 ≤ l) : cnt l α β z ≤ 3 := by
  have := cnt_le_add l α β z
  have := cX_le_one l α β z
  have := cY_le_two l α β z hl
  omega

end Erdos357Upper
