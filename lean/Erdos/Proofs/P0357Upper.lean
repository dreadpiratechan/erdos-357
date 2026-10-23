import Mathlib
import Erdos.Proofs.P0357
/-! Erdos 357, upper bound: a left-hole refinement of the crossing argument.

Zero-based formulation.  `a : ℕ → ℕ` lists the set (indices `< k`), `blk a x y` is the sum of
`a x, ..., a (y-1)`.  Crossing argument: with `t = n/2`, every endpoint `y` whose prefix sum
exceeds `t` has a canonical block `[canon y, y)` with sum in `(t, n]`; these sums are distinct.
Refinement (this file): let `θ = (2n+4)/3`.  A non-singleton block with sum `≤ θ` and
start `≥ 1` extends one step to the left with sum `≤ n` (`chain`).  Hence every "hole"
`z ∈ (t, θ]`, `z ∉ A`, costs one slot of `(t, n]`: `k + #holes ≤ (n - t) + sqrt (2θ)`.
Arithmetic (equal-sum runs `[6w, 6w+6]` / `[7w+1, 7w+6]`) forces many holes.
The statement is for the literal upstream `f` (bridge at the end of the file). -/
namespace Erdos357Upper
open Finset

/-- Sum of `a x, ..., a (y-1)`. -/
def blk (a : ℕ → ℕ) (x y : ℕ) : ℕ := ∑ i ∈ Ico x y, a i

/-- Hypotheses on the first `k` terms. -/
structure Adm (a : ℕ → ℕ) (k n : ℕ) : Prop where
  pos : ∀ i, i < k → 0 < a i
  mono : ∀ i j, i < j → j < k → a i < a j
  le : ∀ i, i < k → a i ≤ n
  inj : ∀ x y x' y', x < y → x' < y' → y ≤ k → y' ≤ k →
    blk a x y = blk a x' y' → x = x' ∧ y = y'

theorem blk_split (a : ℕ → ℕ) {x m y : ℕ} (h1 : x ≤ m) (h2 : m ≤ y) :
    blk a x y = blk a x m + blk a m y :=
  (Finset.sum_Ico_consecutive a h1 h2).symm

theorem blk_succ (a : ℕ → ℕ) (x : ℕ) : blk a x (x + 1) = a x := by
  simp [blk]

theorem blk_run (a : ℕ → ℕ) (i c : ℕ) :
    ∀ l, (∀ j < l, a (i + j) = c + j) → 2 * blk a i (i + l) + l = l * (2 * c + l) := by
  intro l
  induction l with
  | zero => intro _; simp [blk]
  | succ l ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 : blk a i (i + (l + 1)) = blk a i (i + l) + a (i + l) := by
      rw [← add_assoc, blk_split a (show i ≤ i + l by omega) (show i + l ≤ i + l + 1 by omega),
        blk_succ]
    have h3 := h l (by omega)
    rw [h2, h3]
    nlinarith

theorem Adm.ge_idx {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) :
    ∀ i, i < k → i + 1 ≤ a i := by
  intro i
  induction i with
  | zero => intro h; exact H.pos 0 h
  | succ i ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := H.mono i (i + 1) (by omega) h
    omega

theorem Adm.tri {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) :
    ∀ y, y ≤ k → y * (y + 1) ≤ 2 * blk a 0 y := by
  intro y
  induction y with
  | zero => intro _; simp [blk]
  | succ y ih =>
    intro hy
    have h1 := ih (by omega)
    have h2 := H.ge_idx y (by omega)
    have h3 : blk a 0 (y + 1) = blk a 0 y + a y := by
      rw [blk_split a (Nat.zero_le y) (Nat.le_succ y), blk_succ]
    rw [h3]
    nlinarith

/-- The canonical start: the last start whose block ending at `y` has sum `> t`. -/
def canon (a : ℕ → ℕ) (t y : ℕ) : ℕ :=
  Nat.findGreatest (fun x => t < blk a x y) (y - 1)

theorem canon_lt (a : ℕ → ℕ) (t : ℕ) {y : ℕ} (hy : 1 ≤ y) : canon a t y < y := by
  have := Nat.findGreatest_le (P := fun x => t < blk a x y) (y - 1)
  unfold canon
  omega

theorem canon_spec (a : ℕ → ℕ) (t : ℕ) {y : ℕ} (h0 : t < blk a 0 y) :
    t < blk a (canon a t y) y :=
  Nat.findGreatest_spec (P := fun x => t < blk a x y) (Nat.zero_le (y - 1)) h0

theorem canon_max (a : ℕ → ℕ) (t : ℕ) {y x : ℕ} (hx : canon a t y < x) (hxy : x < y) :
    blk a x y ≤ t := by
  have := Nat.findGreatest_is_greatest (P := fun x => t < blk a x y) hx (by omega)
  exact not_lt.mp this

theorem canon_le_n {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t y : ℕ}
    (ht : 2 * t ≤ n) (hy : 1 ≤ y) (hyk : y ≤ k) :
    blk a (canon a t y) y ≤ n := by
  have hc := canon_lt a t hy
  by_cases h1 : canon a t y + 1 = y
  · have : blk a (canon a t y) y = a (canon a t y) := by
      have h2 := blk_succ a (canon a t y)
      rwa [h1] at h2
    rw [this]
    exact H.le _ (by omega)
  · have hc1 : canon a t y + 1 < y := by omega
    have hle : blk a (canon a t y + 1) y ≤ t := canon_max a t (by omega) hc1
    have hsplit : blk a (canon a t y) y = a (canon a t y) + blk a (canon a t y + 1) y := by
      rw [blk_split a (show canon a t y ≤ canon a t y + 1 by omega) (by omega), blk_succ]
    have hlast : a (y - 1) ≤ blk a (canon a t y + 1) y := by
      have hmem : y - 1 ∈ Ico (canon a t y + 1) y := mem_Ico.mpr ⟨by omega, by omega⟩
      exact Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hmem
    have hlt := H.mono (canon a t y) (y - 1) (by omega) (by omega)
    omega

/-- One step to the left of a non-singleton block of sum `≤ θ` stays `≤ n`. -/
theorem chain {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {θ : ℕ} (hθ : 3 * θ ≤ 2 * n + 4)
    {x y : ℕ} (hxy : x + 2 ≤ y) (hyk : y ≤ k) (hx1 : 1 ≤ x) (hs : blk a x y ≤ θ) :
    blk a (x - 1) y ≤ n := by
  have hsplit : blk a (x - 1) y = a (x - 1) + blk a x y := by
    have := blk_split a (show x - 1 ≤ x by omega) (show x ≤ y by omega)
    rw [this]
    have h2 : x = (x - 1) + 1 := by omega
    have := blk_succ a (x - 1)
    rw [← h2] at this
    rw [this]
  have hpair : a x + a (x + 1) ≤ blk a x y := by
    have hsub : ({x, x + 1} : Finset ℕ) ⊆ Ico x y := by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp only [mem_Ico] <;> omega
    have := Finset.sum_le_sum_of_subset (f := a) hsub
    rwa [Finset.sum_pair (by omega)] at this
  have h1 := H.mono (x - 1) x (by omega) (by omega)
  have h2 := H.mono x (x + 1) (by omega) (by omega)
  omega

/-- Existence of the extension beyond `θ` used for the hole accounting. -/
theorem exists_beyond {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {θ : ℕ} (hθ : 3 * θ ≤ 2 * n + 4)
    {y c : ℕ} (hyk : y ≤ k) (hc : c + 2 ≤ y) (hcθ : blk a c y ≤ θ) (h0 : θ < blk a 0 y) :
    ∃ x', x' < c ∧ θ < blk a x' y ∧ blk a x' y ≤ n := by
  let s : Set ℕ := {x | blk a x y ≤ θ}
  have hne : s.Nonempty := ⟨c, hcθ⟩
  have hmem : sInf s ∈ s := Nat.sInf_mem hne
  have hle : sInf s ≤ c := Nat.sInf_le hcθ
  have hne0 : sInf s ≠ 0 := by
    intro h0'
    have : blk a 0 y ≤ θ := by
      have := hmem
      rw [h0'] at this
      exact this
    omega
  have hmin : sInf s - 1 ∉ s := Nat.notMem_of_lt_sInf (by omega)
  refine ⟨sInf s - 1, by omega, ?_, ?_⟩
  · simp only [s, Set.mem_setOf_eq, not_le] at hmin
    exact hmin
  · exact chain H hθ (by omega) hyk (by omega) hmem

/-- A run of consecutive integers inside the set is a run of consecutive terms. -/
theorem consecutive_run {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (c : ℕ) :
    ∀ l, 1 ≤ l → (∀ j < l, ∃ i, i < k ∧ a i = c + j) →
      ∃ i, i + l ≤ k ∧ ∀ j < l, a (i + j) = c + j := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    intro hmem
    obtain ⟨i, hi, hai⟩ := hmem 0 (by omega)
    refine ⟨i, by omega, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simpa using hai
  | succ l hl ih =>
    intro hmem
    obtain ⟨i, hil, hai⟩ := ih (fun j hj => hmem j (by omega))
    obtain ⟨i2, hi2, hai2⟩ := hmem l (by omega)
    have h1 : a (i + (l - 1)) = c + (l - 1) := hai (l - 1) (by omega)
    have hlt : i + l ≤ i2 := by
      by_contra hn
      have h3 : i2 ≤ i + (l - 1) := by omega
      rcases h3.eq_or_lt with h | h
      · rw [h] at hai2; omega
      · have := H.mono i2 (i + (l - 1)) h (by omega); omega
    have hlk : i + l < k := by omega
    have hge : a (i + (l - 1)) < a (i + l) := H.mono _ _ (by omega) hlk
    have hle : a (i + l) ≤ a i2 := by
      rcases hlt.eq_or_lt with h | h
      · rw [h]
      · exact (H.mono _ _ h hi2).le
    refine ⟨i, by omega, fun j hj => ?_⟩
    by_cases hjl : j < l
    · exact hai j hjl
    · have : j = l := by omega
      subst this
      omega

/-- Equal-sum runs: seven consecutive integers `6w..6w+6` and six consecutive integers
`7w+1..7w+6` have the same sum `42w+21`; they cannot both lie in the set. -/
theorem pattern_false {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (w : ℕ)
    (hY : ∀ j < 7, ∃ i, i < k ∧ a i = 6 * w + j)
    (hX : ∀ j < 6, ∃ i, i < k ∧ a i = 7 * w + 1 + j) : False := by
  obtain ⟨iY, hiY, haY⟩ := consecutive_run H (6 * w) 7 (by omega) hY
  obtain ⟨iX, hiX, haX⟩ := consecutive_run H (7 * w + 1) 6 (by omega) hX
  have e1 := blk_run a iY (6 * w) 7 haY
  have e2 := blk_run a iX (7 * w + 1) 6 haX
  have := H.inj iY (iY + 7) iX (iX + 6) (by omega) (by omega) hiY hiX (by omega)
  omega

/-- Integers of `(t, θ]` that are not terms. -/
def holes (a : ℕ → ℕ) (k t θ : ℕ) : Finset ℕ :=
  (Ioc t θ).filter (fun z => z ∉ (range k).image a)

theorem mem_holes {a : ℕ → ℕ} {k t θ z : ℕ} :
    z ∈ holes a k t θ ↔ (t < z ∧ z ≤ θ) ∧ ¬ ∃ i, i < k ∧ a i = z := by
  simp [holes, mem_Ioc]

theorem pattern_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (t θ : ℕ) :
    (θ - 6) / 7 - t / 6 ≤ 3 * (holes a k t θ).card := by
  classical
  have hex' : ∀ w ∈ Ioc (t / 6) ((θ - 6) / 7), ∃ z, z ∈ holes a k t θ ∧
      ((6 * w ≤ z ∧ z ≤ 6 * w + 6) ∨ (7 * w + 1 ≤ z ∧ z ≤ 7 * w + 6)) := by
    intro w hw
    have hw' := mem_Ioc.mp hw
    by_contra hcon
    have hall : ∀ z, ((6 * w ≤ z ∧ z ≤ 6 * w + 6) ∨ (7 * w + 1 ≤ z ∧ z ≤ 7 * w + 6)) →
        ∃ i, i < k ∧ a i = z := by
      intro z hz
      by_contra hnot
      apply hcon
      refine ⟨z, ?_, hz⟩
      rw [mem_holes]
      refine ⟨⟨?_, ?_⟩, hnot⟩ <;> omega
    exact pattern_false H w (fun j hj => hall _ (Or.inl ⟨by omega, by omega⟩))
      (fun j hj => hall _ (Or.inr ⟨by omega, by omega⟩))
  choose! g hg using hex'
  have hmaps : ∀ w ∈ Ioc (t / 6) ((θ - 6) / 7), g w ∈ holes a k t θ :=
    fun w hw => (hg w hw).1
  have hfib : ∀ z ∈ holes a k t θ,
      ((Ioc (t / 6) ((θ - 6) / 7)).filter (fun w => g w = z)).card ≤ 3 := by
    intro z _
    have hsub : (Ioc (t / 6) ((θ - 6) / 7)).filter (fun w => g w = z) ⊆
        {z / 6, z / 6 - 1, (z - 1) / 7} := by
      intro w hw
      rw [mem_filter] at hw
      obtain ⟨hwW, hwz⟩ := hw
      have h2 := (hg w hwW).2
      rw [hwz] at h2
      simp only [mem_insert, mem_singleton]
      omega
    exact (card_le_card hsub).trans card_le_three
  have := Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfib
  simpa using this

/-- Main accounting: each hole in `(t, θ]` costs one slot of `(t, n]`. -/
theorem main_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ : ℕ}
    (ht : 2 * t ≤ n) (htθ : t ≤ θ) (hθ : 3 * θ ≤ 2 * n + 4) (hθn : θ ≤ n) :
    k + (holes a k t θ).card ≤ (n - t) + Nat.sqrt (2 * θ) := by
  classical
  let A : Finset ℕ := (range k).image a
  let S : ℕ → ℕ := fun y => blk a 0 y
  let σ : ℕ → ℕ := fun y => blk a (canon a t y) y
  let Yall : Finset ℕ := Icc 1 k
  let I : Finset ℕ := Yall.filter (fun y => t < S y)
  let Lot : Finset ℕ := Yall.filter (fun y => ¬ t < S y)
  let Lo : Finset ℕ := Yall.filter (fun y => S y ≤ θ)
  let Y1 : Finset ℕ := I.filter (fun y => σ y ≤ θ ∧ σ y ∉ A)
  let Y2 : Finset ℕ := Y1.filter (fun y => θ < S y)
  let Y1lo : Finset ℕ := Y1.filter (fun y => ¬ θ < S y)
  have memI : ∀ y, y ∈ I ↔ (1 ≤ y ∧ y ≤ k) ∧ t < S y := by
    intro y; simp only [I, Yall, mem_filter, mem_Icc]
  have memY1 : ∀ y, y ∈ Y1 ↔ ((1 ≤ y ∧ y ≤ k) ∧ t < S y) ∧ (σ y ≤ θ ∧ σ y ∉ A) := by
    intro y; simp only [Y1, I, Yall, mem_filter, mem_Icc]
  have memY2 : ∀ y, y ∈ Y2 ↔ (((1 ≤ y ∧ y ≤ k) ∧ t < S y) ∧ (σ y ≤ θ ∧ σ y ∉ A)) ∧ θ < S y := by
    intro y; simp only [Y2, Y1, I, Yall, mem_filter, mem_Icc]
  have memA : ∀ z, z ∈ A ↔ ∃ i, i < k ∧ a i = z := by
    intro z; simp [A]
  -- basic facts for y ∈ I
  have hI1 : ∀ y ∈ I, canon a t y < y := by
    intro y hy
    have := (memI y).mp hy
    exact canon_lt a t this.1.1
  have hI2 : ∀ y ∈ I, t < σ y ∧ σ y ≤ n := by
    intro y hy
    have h := (memI y).mp hy
    exact ⟨canon_spec a t h.2, canon_le_n H ht h.1.1 h.1.2⟩
  have σinj : Set.InjOn σ (I : Set ℕ) := by
    intro y hy y2 hy2 he
    have hy' := (memI y).mp hy
    have hy2' := (memI y2).mp hy2
    exact (H.inj _ _ _ _ (hI1 y hy) (hI1 y2 hy2) hy'.1.2 hy2'.1.2 he).2
  -- extension beyond θ for y ∈ Y2
  have hex : ∀ y ∈ Y2, ∃ x', x' < canon a t y ∧ θ < blk a x' y ∧ blk a x' y ≤ n := by
    intro y hy
    have h := (memY2 y).mp hy
    have hyI : y ∈ I := (memI y).mpr h.1.1
    have hc := hI1 y hyI
    have hc1 : canon a t y + 1 < y := by
      by_contra hn
      have heq : canon a t y + 1 = y := by omega
      have h2 : σ y = a (canon a t y) := by
        have h3 := blk_succ a (canon a t y)
        simp only [σ]
        rw [heq] at h3
        exact h3
      apply h.1.2.2
      rw [memA]
      exact ⟨canon a t y, by omega, h2.symm⟩
    exact exists_beyond H hθ h.1.1.1.2 (by omega) h.1.2.1 h.2
  choose! xp hxp using hex
  let Ψ : ℕ → ℕ := fun y => blk a (xp y) y
  have hY2k : ∀ y ∈ Y2, y ≤ k := fun y hy => ((memY2 y).mp hy).1.1.1.2
  have hΨlt : ∀ y ∈ Y2, xp y < y := fun y hy => by
    have := hI1 y ((memI y).mpr ((memY2 y).mp hy).1.1)
    have := (hxp y hy).1
    omega
  have Ψinj : Set.InjOn Ψ (Y2 : Set ℕ) := by
    intro y hy y2 hy2 he
    exact (H.inj _ _ _ _ (hΨlt y hy) (hΨlt y2 hy2) (hY2k y hy) (hY2k y2 hy2) he).2
  let Sg : Finset ℕ := I.image σ
  let Hs : Finset ℕ := holes a k t θ
  let Hb : Finset ℕ := Hs.filter (fun z => z ∉ Sg)
  let Ha : Finset ℕ := Hs.filter (fun z => ¬ z ∉ Sg)
  let Ps : Finset ℕ := Y2.image Ψ
  have cSg : Sg.card = I.card := card_image_of_injOn σinj
  have cPs : Ps.card = Y2.card := card_image_of_injOn Ψinj
  have cH : Hb.card + Ha.card = Hs.card := card_filter_add_card_filter_not _
  -- Ha is covered by Y1
  have hHa : Ha.card ≤ Y1.card := by
    have hsub : Ha ⊆ Y1.image σ := by
      intro z hz
      simp only [Ha, mem_filter, not_not] at hz
      obtain ⟨hzH, hzS⟩ := hz
      obtain ⟨y, hyI, rfl⟩ := mem_image.mp hzS
      have hzh := mem_holes.mp hzH
      rw [mem_image]
      refine ⟨y, (memY1 y).mpr ⟨(memI y).mp hyI, hzh.1.2, ?_⟩, rfl⟩
      rw [memA]
      exact hzh.2
    exact (card_le_card hsub).trans card_image_le
  -- Y1 splits at θ < S
  have cY1 : Y2.card + Y1lo.card = Y1.card := card_filter_add_card_filter_not _
  -- I and Lot split Yall
  have cI : I.card + Lot.card = k := by
    have h := card_filter_add_card_filter_not (s := Yall) (fun y => t < S y)
    have hk : Yall.card = k := by simp [Yall]
    rw [hk] at h
    exact h
  -- small prefix sums
  have hLo : Lo.card ≤ Nat.sqrt (2 * θ) := by
    have hsub : Lo ⊆ Icc 1 (Nat.sqrt (2 * θ)) := by
      intro y hy
      simp only [Lo, Yall, mem_filter, mem_Icc] at hy
      rw [mem_Icc]
      refine ⟨hy.1.1, Nat.le_sqrt.mpr ?_⟩
      have := H.tri y hy.1.2
      nlinarith [hy.2]
    have := card_le_card hsub
    simpa using this
  have hdisj : Disjoint Lot Y1lo := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Lot, Y1lo, Y1, I, Yall, mem_filter, mem_Icc] at hy1 hy2
    exact hy1.2 hy2.1.1.2
  have hLoSub : Lot ∪ Y1lo ⊆ Lo := by
    intro y hy
    rcases mem_union.mp hy with h | h
    · simp only [Lot, Lo, Yall, mem_filter, mem_Icc] at h ⊢
      exact ⟨h.1, by omega⟩
    · simp only [Y1lo, Lo, Y1, I, Yall, mem_filter, mem_Icc] at h ⊢
      exact ⟨h.1.1.1, by omega⟩
  have hLo2 : Lot.card + Y1lo.card ≤ Nat.sqrt (2 * θ) := by
    have := card_le_card hLoSub
    rw [card_union_of_disjoint hdisj] at this
    omega
  -- the target interval
  have hd1 : Disjoint Sg Hb := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Hb, mem_filter] at hz2
    exact hz2.2 hz1
  have hd2 : Disjoint Sg Ps := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y2, hy2, rfl⟩ := mem_image.mp hz2
    obtain ⟨y, hy, he⟩ := mem_image.mp hz1
    have hyI : y ∈ I := hy
    have hy2Y := (memY2 y2).mp hy2
    have hy2I : y2 ∈ I := (memI y2).mpr hy2Y.1.1
    have hyk := ((memI y).mp hyI).1.2
    have := H.inj (canon a t y) y (xp y2) y2 (hI1 y hyI) (hΨlt y2 hy2) hyk
      (hY2k y2 hy2) he
    have h1 := (hxp y2 hy2).1
    have h2 : y = y2 := this.2
    subst h2
    omega
  have hd3 : Disjoint Hb Ps := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y2, hy2, rfl⟩ := mem_image.mp hz2
    simp only [Hb, Hs, mem_filter] at hz1
    have h1 := (mem_holes.mp hz1.1).1.2
    have h2 := (hxp y2 hy2).2.1
    simp only [Ψ] at h1
    omega
  have hsubI : Sg ∪ Hb ∪ Ps ⊆ Ioc t n := by
    intro z hz
    rw [mem_Ioc]
    rcases mem_union.mp hz with h | h
    · rcases mem_union.mp h with h | h
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
        exact hI2 y hy
      · simp only [Hb, Hs, mem_filter] at h
        have := (mem_holes.mp h.1).1
        omega
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      have h1 := (hxp y hy).2
      simp only [Ψ]
      omega
  have hcard : Sg.card + Hb.card + Ps.card ≤ n - t := by
    have h1 := card_le_card hsubI
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd2, hd3⟩),
      card_union_of_disjoint hd1] at h1
    simpa using h1
  have hHs : Hs.card = (holes a k t θ).card := rfl
  omega

/-! ### Bridge to the literal upstream `f` -/

/-- Admissible integer sequences give `Adm` (zero-based natural encoding). -/
theorem adm_of_int {k n : ℕ} (a : Fin k → ℤ) (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ))
    (hm : StrictMono a) (ha : Erdos357.HasDistinctSums a) :
    ∃ b : ℕ → ℕ, Adm b k n := by
  classical
  have hab : ∀ i : Fin k, 1 ≤ a i ∧ a i ≤ n := fun i => hr ⟨i, rfl⟩
  let c : Fin k → ℕ := fun i => (a i).toNat
  have hc : ∀ i, (c i : ℤ) = a i := fun i => Int.toNat_of_nonneg (by have := (hab i).1; omega)
  have hcm : StrictMono c := by
    intro i j hij
    have h := hm hij
    rw [← hc i, ← hc j] at h
    exact_mod_cast h
  have hcd : Erdos357.HasDistinctSums c := by
    intro J hJ K hK hs
    apply ha hJ hK
    have h2 := congrArg (fun z : ℕ => (z : ℤ)) hs
    simpa only [Nat.cast_sum, hc] using h2
  let b : ℕ → ℕ := fun i => if h : i < k then c ⟨i, h⟩ else 0
  have hbc : ∀ i (h : i < k), b i = c ⟨i, h⟩ := fun i h => by simp [b, h]
  have hbd : Erdos357.HasDistinctSums (fun i : Fin k => b i.val) := by
    have : (fun i : Fin k => b i.val) = c := by
      funext i; rw [hbc i.val i.isLt]
    rw [this]; exact hcd
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hbc i hi]
    have := (hab ⟨i, hi⟩).1
    have := hc ⟨i, hi⟩
    omega
  · intro i j hij hj
    rw [hbc i (by omega), hbc j hj]
    exact hcm (show (⟨i, by omega⟩ : Fin k) < ⟨j, hj⟩ from hij)
  · intro i hi
    rw [hbc i hi]
    have := (hab ⟨i, hi⟩).2
    have := hc ⟨i, hi⟩
    omega
  · intro x y x' y' hxy hxy' hyk hyk' he
    have e1 : blk b x y = ∑ t ∈ range (y - x), b (x + t) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have e2 : blk b x' y' = ∑ t ∈ range (y' - x'), b (x' + t) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have := Erdos357.block_inj_of_hasDistinctSums b k hbd (i := x) (l := y - x) (j := x')
      (r := y' - x') (by omega) (by omega) (by omega) (by omega) (by rw [← e1, ← e2]; exact he)
    omega

/-- **Upper bound.**  `252 f(n) ≤ 125 n + 252 sqrt(2 ⌊(2n+4)/3⌋) + 258` for the literal
upstream `f`; i.e. `f(n) ≤ (125/252) n + O(sqrt n)`. -/
theorem f_le_upper (n : ℕ) :
    252 * Erdos357.f n ≤ 125 * n + 252 * Nat.sqrt (2 * ((2 * n + 4) / 3)) + 258 := by
  have hbound : Erdos357.f n ≤ (n - n / 2) + Nat.sqrt (2 * ((2 * n + 4) / 3)) -
      ((((2 * n + 4) / 3 - 6) / 7 - n / 2 / 6) + 2) / 3 := by
    unfold Erdos357.f
    apply csSup_le'
    rintro k ⟨a, hr, hm, ha⟩
    obtain ⟨b, hb⟩ := adm_of_int a hr hm ha
    by_cases hn : 2 ≤ n
    · have h1 := main_count hb (t := n / 2) (θ := (2 * n + 4) / 3)
        (by omega) (by omega) (by omega) (by omega)
      have h2 := pattern_count hb (n / 2) ((2 * n + 4) / 3)
      omega
    · have h1 := Erdos357.finite_int_length_le_half_add_sqrt a hr hm ha
      have h2 : Nat.sqrt n ≤ Nat.sqrt (2 * ((2 * n + 4) / 3)) :=
        Nat.sqrt_le_sqrt (by omega)
      omega
  omega

/-- Real-valued form of the same bound. -/
theorem f_le_real (n : ℕ) :
    (Erdos357.f n : ℝ) ≤ (125 / 252) * n + 2 * Real.sqrt n + 4 := by
  have h := f_le_upper n
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
  have h5 : (252 : ℝ) * (Erdos357.f n : ℝ) ≤ 125 * n +
      252 * ((2 * Nat.sqrt n + 2 : ℕ) : ℝ) + 258 := by
    have := h.trans (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_left 252 hs) _) 258)
    exact_mod_cast this
  push_cast at h5
  nlinarith

end Erdos357Upper


/-- Pin: `Erdos357.f` is verbatim the upstream extremal function (Formal Conjectures
`ErdosProblems/357.lean`, commit c83a94d): integer-valued `Fin k → ℤ`, range in `Icc 1 n`,
`StrictMono`, and `HasDistinctSums` over all order-connected index sets. -/
example (n : ℕ) : Erdos357.f n = sSup {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ Erdos357.HasDistinctSums a} := rfl
