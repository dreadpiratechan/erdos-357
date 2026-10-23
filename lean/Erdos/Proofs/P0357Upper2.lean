import Mathlib
import Erdos.Proofs.P0357Upper
/-! Erdos 357, upper bound, round 2: a better hole count in `(t, θ]`.

`Erdos357Upper.main_count` (P0357Upper) gives `k + #holes ≤ (n - t) + sqrt (2 θ)`, where
`holes = (t, θ] \ A`, `t = n/2`, `θ = (2n+4)/3`.  The first round bounded `#holes` below by the
degree-3 count of the family `[6w, 6w+6]` / `[7w+1, 7w+6]`.  Here we use the whole family
`[l w, l w + l]` / `[(l+1) w + 1, (l+1) w + l]` (both runs have the same sum, lengths `l+1 ≠ l`) and
a **fractional-packing / disjoint-pattern** counting: every pattern contains a hole, and a
carefully chosen set of patterns (families `l = 5` and `l = 9` on adjacent ranges of `w`) has the
property that no integer lies in three of them.  Hence `#patterns ≤ 2 #holes`. -/
namespace Erdos357Upper
open Finset

/-- `z` lies in the `(l+1)`-run `[l w, l w + l]` or in the `l`-run `[(l+1) w + 1, (l+1) w + l]`. -/
def Hit (l w z : ℕ) : Prop :=
  (l * w ≤ z ∧ z ≤ l * w + l) ∨ ((l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l)

instance (l w z : ℕ) : Decidable (Hit l w z) := by unfold Hit; infer_instance

/-- Equal-sum runs of lengths `l+1` and `l`: they cannot both lie in the set. -/
theorem pattern_false_gen {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (l w : ℕ) (hl : 1 ≤ l)
    (hY : ∀ j < l + 1, ∃ i, i < k ∧ a i = l * w + j)
    (hX : ∀ j < l, ∃ i, i < k ∧ a i = (l + 1) * w + 1 + j) : False := by
  obtain ⟨iY, hiY, haY⟩ := consecutive_run H (l * w) (l + 1) (by omega) hY
  obtain ⟨iX, hiX, haX⟩ := consecutive_run H ((l + 1) * w + 1) l hl hX
  have e1 := blk_run a iY (l * w) (l + 1) haY
  have e2 := blk_run a iX ((l + 1) * w + 1) l haX
  have hb : blk a iY (iY + (l + 1)) = blk a iX (iX + l) := by nlinarith [e1, e2]
  have := H.inj iY (iY + (l + 1)) iX (iX + l) (by omega) (by omega) hiY hiX hb
  omega

/-- Every pattern whose points lie in `(t, θ]` contains a hole. -/
theorem pattern_hit {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ l w : ℕ} (hl : 1 ≤ l)
    (h1 : t < l * w) (h2 : (l + 1) * w + l ≤ θ) :
    ∃ z, z ∈ holes a k t θ ∧ Hit l w z := by
  by_contra hcon
  push_neg at hcon
  have h3 : l * w ≤ (l + 1) * w := Nat.mul_le_mul_right w (Nat.le_succ l)
  have hall : ∀ z, Hit l w z → ∃ i, i < k ∧ a i = z := by
    intro z hz
    by_contra hnot
    apply hcon z _ hz
    rw [mem_holes]
    refine ⟨⟨?_, ?_⟩, hnot⟩
    · rcases hz with h | h <;> omega
    · rcases hz with h | h <;> omega
  exact pattern_false_gen H l w hl (fun j hj => hall _ (Or.inl ⟨by omega, by omega⟩))
    (fun j hj => hall _ (Or.inr ⟨by omega, by omega⟩))

/-- No integer is in more than two of the chosen patterns (families `5` and `9`). -/
theorem fiber_bound {α5 β5 α9 β9 : ℕ}
    (hi : 5 * β5 + 5 < 9 * (α9 + 1)) (hii : 9 * β9 + 9 < 6 * (α5 + 1) + 1)
    (hiii : 9 * β9 + 9 < 10 * (α9 + 1) + 1) (hiv : 5 * β5 + 5 < 6 * (α5 + 1) + 1) (z : ℕ) :
    ((Ioc α5 β5).filter (fun w => Hit 5 w z)).card +
      ((Ioc α9 β9).filter (fun w => Hit 9 w z)).card ≤ 2 := by
  by_cases h1 : z ≤ 5 * β5 + 5
  · have hF9 : (Ioc α9 β9).filter (fun w => Hit 9 w z) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w hw
      have := mem_Ioc.mp hw
      unfold Hit
      omega
    have hF5 : (Ioc α5 β5).filter (fun w => Hit 5 w z) ⊆ {z / 5, z / 5 - 1} := by
      intro w hw
      rw [mem_filter, mem_Ioc] at hw
      obtain ⟨hw1, hw2⟩ := hw
      unfold Hit at hw2
      simp only [mem_insert, mem_singleton]
      omega
    have := card_le_card hF5
    rw [hF9]
    simpa using this.trans card_le_two
  · by_cases h2 : z ≤ 9 * β9 + 9
    · have hF5 : (Ioc α5 β5).filter (fun w => Hit 5 w z) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hw
        have := mem_Ioc.mp hw
        unfold Hit
        omega
      have hF9 : (Ioc α9 β9).filter (fun w => Hit 9 w z) ⊆ {z / 9, z / 9 - 1} := by
        intro w hw
        rw [mem_filter, mem_Ioc] at hw
        obtain ⟨hw1, hw2⟩ := hw
        unfold Hit at hw2
        simp only [mem_insert, mem_singleton]
        omega
      have := card_le_card hF9
      rw [hF5]
      simpa using this.trans card_le_two
    · have hF5 : (Ioc α5 β5).filter (fun w => Hit 5 w z) ⊆ {(z - 1) / 6} := by
        intro w hw
        rw [mem_filter, mem_Ioc] at hw
        obtain ⟨hw1, hw2⟩ := hw
        unfold Hit at hw2
        simp only [mem_singleton]
        omega
      have hF9 : (Ioc α9 β9).filter (fun w => Hit 9 w z) ⊆ {(z - 1) / 10} := by
        intro w hw
        rw [mem_filter, mem_Ioc] at hw
        obtain ⟨hw1, hw2⟩ := hw
        unfold Hit at hw2
        simp only [mem_singleton]
        omega
      have c5 := card_le_card hF5
      have c9 := card_le_card hF9
      simp only [card_singleton] at c5 c9
      omega

/-- **Packing count.**  Two families of equal-sum run pairs on adjacent `w`-ranges, no integer in
three of them: `#patterns ≤ 2 #holes`. -/
theorem pattern_count2 {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ α5 β5 α9 β9 : ℕ}
    (h5a : t < 5 * (α5 + 1)) (h5b : 6 * β5 + 5 ≤ θ)
    (h9a : t < 9 * (α9 + 1)) (h9b : 10 * β9 + 9 ≤ θ)
    (hi : 5 * β5 + 5 < 9 * (α9 + 1)) (hii : 9 * β9 + 9 < 6 * (α5 + 1) + 1)
    (hiii : 9 * β9 + 9 < 10 * (α9 + 1) + 1) (hiv : 5 * β5 + 5 < 6 * (α5 + 1) + 1) :
    (β5 - α5) + (β9 - α9) ≤ 2 * (holes a k t θ).card := by
  classical
  have hex5 : ∀ w ∈ Ioc α5 β5, ∃ z, z ∈ holes a k t θ ∧ Hit 5 w z := by
    intro w hw
    have := mem_Ioc.mp hw
    exact pattern_hit H (by norm_num) (by omega) (by omega)
  have hex9 : ∀ w ∈ Ioc α9 β9, ∃ z, z ∈ holes a k t θ ∧ Hit 9 w z := by
    intro w hw
    have := mem_Ioc.mp hw
    exact pattern_hit H (by norm_num) (by omega) (by omega)
  choose! g5 hg5 using hex5
  choose! g9 hg9 using hex9
  have e5 : (Ioc α5 β5).card =
      ∑ z ∈ holes a k t θ, ((Ioc α5 β5).filter (fun w => g5 w = z)).card :=
    card_eq_sum_card_fiberwise (fun w hw => (hg5 w hw).1)
  have e9 : (Ioc α9 β9).card =
      ∑ z ∈ holes a k t θ, ((Ioc α9 β9).filter (fun w => g9 w = z)).card :=
    card_eq_sum_card_fiberwise (fun w hw => (hg9 w hw).1)
  have key : ∀ z ∈ holes a k t θ,
      ((Ioc α5 β5).filter (fun w => g5 w = z)).card +
        ((Ioc α9 β9).filter (fun w => g9 w = z)).card ≤ 2 := by
    intro z _
    have s5 : (Ioc α5 β5).filter (fun w => g5 w = z) ⊆ (Ioc α5 β5).filter (fun w => Hit 5 w z) := by
      intro w hw
      rw [mem_filter] at hw ⊢
      exact ⟨hw.1, by rw [← hw.2]; exact (hg5 w hw.1).2⟩
    have s9 : (Ioc α9 β9).filter (fun w => g9 w = z) ⊆ (Ioc α9 β9).filter (fun w => Hit 9 w z) := by
      intro w hw
      rw [mem_filter] at hw ⊢
      exact ⟨hw.1, by rw [← hw.2]; exact (hg9 w hw.1).2⟩
    have := fiber_bound hi hii hiii hiv z
    have c5 := card_le_card s5
    have c9 := card_le_card s9
    omega
  calc (β5 - α5) + (β9 - α9) = (Ioc α5 β5).card + (Ioc α9 β9).card := by simp
    _ = ∑ z ∈ holes a k t θ, (((Ioc α5 β5).filter (fun w => g5 w = z)).card +
          ((Ioc α9 β9).filter (fun w => g9 w = z)).card) := by
        rw [e5, e9, sum_add_distrib]
    _ ≤ ∑ z ∈ holes a k t θ, 2 := sum_le_sum key
    _ = 2 * (holes a k t θ).card := by simp [mul_comm]

/-- The eight side conditions of `pattern_count2` for the concrete design
`α5 = ⌊n/2⌋/5`, `β5 = (θ-5)/6`, `α9 = (5β5+5)/9`, `β9 = (θ-9)/10`, `θ = ⌊(2n+4)/3⌋`.
For `n ≥ 400` there is room to spare (omega); `12 ≤ n < 400` is a finite check. -/
theorem design_ok (n : ℕ) (hn : 12 ≤ n) :
    (n / 2 < 5 * (n / 2 / 5 + 1)) ∧ (6 * (((2 * n + 4) / 3 - 5) / 6) + 5 ≤ (2 * n + 4) / 3) ∧
    (n / 2 < 9 * ((5 * (((2 * n + 4) / 3 - 5) / 6) + 5) / 9 + 1)) ∧
    (10 * (((2 * n + 4) / 3 - 9) / 10) + 9 ≤ (2 * n + 4) / 3) ∧
    (5 * (((2 * n + 4) / 3 - 5) / 6) + 5 <
      9 * ((5 * (((2 * n + 4) / 3 - 5) / 6) + 5) / 9 + 1)) ∧
    (9 * (((2 * n + 4) / 3 - 9) / 10) + 9 < 6 * (n / 2 / 5 + 1) + 1) ∧
    (9 * (((2 * n + 4) / 3 - 9) / 10) + 9 <
      10 * ((5 * (((2 * n + 4) / 3 - 5) / 6) + 5) / 9 + 1) + 1) ∧
    (5 * (((2 * n + 4) / 3 - 5) / 6) + 5 < 6 * (n / 2 / 5 + 1) + 1) := by
  by_cases h : 400 ≤ n
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · have h' : n < 400 := by omega
    interval_cases n <;> decide

/-- The closing arithmetic: the pattern bound `P ≤ 2·holes` and the crossing bound
`k + holes ≤ (n - n/2) + s` combine to `1620 k ≤ 797 n + 1620 s + C`. -/
theorem arith_close (n : ℕ) (hn : 12 ≤ n) :
    1620 * (n - n / 2) ≤ 797 * n +
      810 * ((((2 * n + 4) / 3 - 5) / 6 - n / 2 / 5) +
        (((2 * n + 4) / 3 - 9) / 10 - (5 * (((2 * n + 4) / 3 - 5) / 6) + 5) / 9)) + 8000 := by
  by_cases h : 400 ≤ n
  · omega
  · have h' : n < 400 := by omega
    interval_cases n <;> decide

/-- Admissible data of the right size give the final inequality (needs `12 <= n`). -/
theorem adm_bound2 {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (hn : 12 ≤ n) :
    1620 * k ≤ 797 * n + 1620 * Nat.sqrt (2 * ((2 * n + 4) / 3)) + 8000 := by
  have h1 := main_count H (t := n / 2) (θ := (2 * n + 4) / 3)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := design_ok n hn
  have h2 := pattern_count2 H (t := n / 2) (θ := (2 * n + 4) / 3)
    (α5 := n / 2 / 5) (β5 := ((2 * n + 4) / 3 - 5) / 6)
    (α9 := (5 * (((2 * n + 4) / 3 - 5) / 6) + 5) / 9) (β9 := ((2 * n + 4) / 3 - 9) / 10)
    c1 c2 c3 c4 c5 c6 c7 c8
  have h3 := arith_close n hn
  omega

/-- **Upper bound, round 2.**  `1620 f(n) ≤ 797 n + 1620 sqrt(2 ⌊(2n+4)/3⌋) + 8000` for the
literal upstream `f`; i.e. `f(n) ≤ (797/1620) n + O(sqrt n)`, `797/1620 = 1/2 - 13/1620`. -/
theorem f_le_upper2 (n : ℕ) :
    1620 * Erdos357.f n ≤ 797 * n + 1620 * Nat.sqrt (2 * ((2 * n + 4) / 3)) + 8000 := by
  have hbound : ∀ k, k ∈ {k : ℕ | ∃ a : Fin k → ℤ,
      Set.range a ⊆ Set.Icc 1 (n : ℤ) ∧ StrictMono a ∧ Erdos357.HasDistinctSums a} →
      1620 * k ≤ 797 * n + 1620 * Nat.sqrt (2 * ((2 * n + 4) / 3)) + 8000 := by
    rintro k ⟨a, hr, hm, ha⟩
    by_cases hn : 12 ≤ n
    · obtain ⟨b, hb⟩ := adm_of_int a hr hm ha
      have := adm_bound2 hb hn
      omega
    · have h1 := Erdos357.finite_int_length_le_half_add_sqrt a hr hm ha
      have h2 : Nat.sqrt n ≤ Nat.sqrt (2 * ((2 * n + 4) / 3)) :=
        Nat.sqrt_le_sqrt (by omega)
      omega
  have hf : Erdos357.f n ≤ (797 * n + 1620 * Nat.sqrt (2 * ((2 * n + 4) / 3)) + 8000) / 1620 := by
    unfold Erdos357.f
    apply csSup_le'
    intro k hk
    have := hbound k hk
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have := (Nat.le_div_iff_mul_le (show 0 < 1620 by norm_num)).mp hf
  omega

/-- Real-valued form: `f(n) ≤ (797/1620) n + 2 sqrt n + 7`, `797/1620 = 1/2 - 13/1620`. -/
theorem f_le_real2 (n : ℕ) :
    (Erdos357.f n : ℝ) ≤ (797 / 1620) * n + 2 * Real.sqrt n + 7 := by
  have h := f_le_upper2 n
  have hs : Nat.sqrt (2 * ((2 * n + 4) / 3)) ≤ 2 * Nat.sqrt n + 2 := by
    have h1 := Nat.sqrt_le' (2 * ((2 * n + 4) / 3))
    have h2 := Nat.lt_succ_sqrt' n
    by_contra hcon
    push_neg at hcon
    set s := Nat.sqrt (2 * ((2 * n + 4) / 3))
    set m := Nat.sqrt n
    have h3 : 3 * s ^ 2 ≤ 4 * n + 8 := by omega
    have h4 : (2 * m + 3) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [Nat.succ_eq_add_one] at h2
    nlinarith
  have hm : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have h5 : (1620 : ℝ) * (Erdos357.f n : ℝ) ≤ 797 * n +
      1620 * ((2 * Nat.sqrt n + 2 : ℕ) : ℝ) + 8000 := by
    have := h.trans (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_left 1620 hs) _) 8000)
    exact_mod_cast this
  push_cast at h5
  nlinarith

end Erdos357Upper

/-- Pin: `Erdos357.f` is verbatim the upstream extremal function (Formal Conjectures
`ErdosProblems/357.lean`, commit c83a94d): integer-valued `Fin k → ℤ`, range in `Icc 1 n`,
`StrictMono`, and `HasDistinctSums` over all order-connected index sets. -/
example (n : ℕ) : Erdos357.f n = sSup {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ Erdos357.HasDistinctSums a} := rfl
