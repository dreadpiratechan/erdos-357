import Mathlib
/-! Erdos 357: the known lower-density theorem and a finite half-plus-square-root bound.
HasDistinctSums and f are restated from upstream 357.lean (Formal Conjectures Authors,
Apache-2.0). The finite crossing argument is audited from the July 24, 2026 report at
https://erdosproblemaday.com/day/357-half-the-runs. No novelty is claimed.
The open finite little-o conjecture is not proved here. -/
namespace Erdos357
open Finset

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

example (a : ℕ → ℕ) : HasDistinctSums a ↔
    {J : Finset ℕ | (J : Set ℕ).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x) := Iff.rfl

/-- Pigeonhole bound for a finite family of intervals with sums in [0,B]. -/
theorem interval_family_card_le (a : ℕ → ℕ) (ha : HasDistinctSums a)
    (S : Finset (Finset ℕ)) (B : ℕ)
    (hc : ∀ J ∈ S, (J : Set ℕ).OrdConnected)
    (hb : ∀ J ∈ S, ∑ x ∈ J, a x ≤ B) : S.card ≤ B + 1 := by
  classical
  have hi : Set.InjOn (fun J : Finset ℕ ↦ ∑ x ∈ J, a x) (S : Set (Finset ℕ)) := by
    intro J hJ K hK he
    exact ha (hc J hJ) (hc K hK) he
  calc
    S.card = (S.image (fun J ↦ ∑ x ∈ J, a x)).card := (card_image_of_injOn hi).symm
    _ ≤ (range (B + 1)).card := card_le_card (by
      intro v hv
      obtain ⟨J, hJ, rfl⟩ := mem_image.mp hv
      exact mem_range.mpr (Nat.lt_succ_of_le (hb J hJ)))
    _ = B + 1 := card_range _

/-- A positive-length interval determines its start and length. -/
theorem block_injective : Set.InjOn
    (fun p : ℕ × ℕ ↦ Ico p.1 (p.1 + p.2)) {p | 0 < p.2} := by
  intro p hp q hq he
  change 0 < p.2 at hp
  change 0 < q.2 at hq
  change Ico p.1 (p.1 + p.2) = Ico q.1 (q.1 + q.2) at he
  have hp0 : p.1 ∈ Ico p.1 (p.1 + p.2) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hq0 : q.1 ∈ Ico q.1 (q.1 + q.2) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hpq := (mem_Ico.mp (he ▸ hp0)).1
  have hqp := (mem_Ico.mp (he.symm ▸ hq0)).1
  have hstart : p.1 = q.1 := by omega
  have hlen : p.2 = q.2 := by
    have hh := congrArg Finset.card he
    simpa using hh
  exact Prod.ext hstart hlen

/-- Explicit block-sum bound under a linear envelope on the sequence. -/
theorem block_sum_le_of_linear (a : ℕ → ℕ) (C : ℕ)
    (ha : ∀ t, a t ≤ C * (t + 1)) (i l : ℕ) :
    ∑ t ∈ Ico i (i + l), a t ≤ C * l * (i + l) := by
  calc
    ∑ t ∈ Ico i (i + l), a t ≤ ∑ _t ∈ Ico i (i + l), C * (i + l) := by
      apply sum_le_sum
      intro t ht
      exact (ha t).trans (Nat.mul_le_mul_left C (by have := (mem_Ico.mp ht).2; omega))
    _ = C * l * (i + l) := by simp; ring

/-- Counting bound for blocks encoded by start and positive length. -/
theorem block_family_card_le (a : ℕ → ℕ) (ha : HasDistinctSums a)
    (F : Finset (ℕ × ℕ)) (B : ℕ)
    (hp : ∀ p ∈ F, 0 < p.2)
    (hb : ∀ p ∈ F, ∑ t ∈ Ico p.1 (p.1 + p.2), a t ≤ B) : F.card ≤ B + 1 := by
  classical
  let S := F.image (fun p ↦ Ico p.1 (p.1 + p.2))
  have hi : Set.InjOn (fun p : ℕ × ℕ ↦ Ico p.1 (p.1 + p.2)) (F : Set (ℕ × ℕ)) :=
    block_injective.mono (by intro p h; exact hp p h)
  have he : S.card = F.card := card_image_of_injOn hi
  rw [← he]
  apply interval_family_card_le a ha S B
  · intro J hJ
    obtain ⟨p, _, rfl⟩ := mem_image.mp hJ
    simpa only [coe_Ico] using (Set.ordConnected_Ico : (Set.Ico p.1 (p.1 + p.2)).OrdConnected)
  · intro J hJ
    obtain ⟨p, hpF, rfl⟩ := mem_image.mp hJ
    exact hb p hpF

def shortBlocks (N L : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 L).biUnion (fun l ↦ (range (N / l)).image (fun i ↦ (i,l)))

@[simp] theorem mem_shortBlocks {N L i l : ℕ} :
    (i,l) ∈ shortBlocks N L ↔ 1 ≤ l ∧ l ≤ L ∧ i < N / l := by
  simp only [shortBlocks, mem_biUnion, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, x, hx, hxi, hjl⟩
    subst j; subst x
    exact ⟨hj.1, hj.2, hx⟩
  · rintro ⟨hl, hL, hi⟩
    exact ⟨l, ⟨hl,hL⟩, i, hi, rfl, rfl⟩

theorem card_shortBlocks (N L : ℕ) :
    (shortBlocks N L).card = ∑ l ∈ Icc 1 L, N / l := by
  unfold shortBlocks
  rw [card_biUnion]
  · apply sum_congr rfl
    intro l hl
    rw [card_image_of_injective]
    · exact card_range _
    · intro i j h; exact (Prod.mk.inj h).1
  · intro l hl m hm hne
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨j, hj, he⟩ := mem_image.mp hq
    exact hne (Prod.mk.inj he).2.symm

theorem floor_sum_le_of_linear (a : ℕ → ℕ) (ha : HasDistinctSums a)
    (C : ℕ) (hC : ∀ t, a t ≤ C * (t + 1)) (N L : ℕ) :
    ∑ l ∈ Icc 1 L, N / l ≤ C * (N + L^2) + 1 := by
  rw [← card_shortBlocks]
  apply block_family_card_le a ha (shortBlocks N L)
  · intro p hp
    have hh := mem_shortBlocks.mp hp
    omega
  · intro p hp
    have hh := mem_shortBlocks.mp hp
    have hn : p.2 * p.1 ≤ N := by
      calc
        p.2 * p.1 ≤ p.2 * (N / p.2) := Nat.mul_le_mul_left _ (Nat.le_of_lt hh.2.2)
        _ ≤ N := Nat.mul_div_le N p.2
    have hl : p.2 * p.2 ≤ L * L := Nat.mul_self_le_mul_self hh.2.1
    calc
      _ ≤ C * p.2 * (p.1 + p.2) := block_sum_le_of_linear a C hC _ _
      _ ≤ C * (N + L^2) := by nlinarith



/-- The floor sum retains the divergent harmonic main term. -/
theorem harmonic_mul_le_floor_sum (N L : ℕ) :
    (N : ℝ) * (harmonic L : ℝ) ≤ (∑ l ∈ Icc 1 L, N / l : ℕ) + L := by
  have hterm (l : ℕ) (hl : l ∈ Icc 1 L) :
      (N : ℝ) / l ≤ (N / l : ℕ) + 1 := by
    have hl0 : 0 < l := by have := (mem_Icc.mp hl).1; omega
    apply (div_le_iff₀ (by exact_mod_cast hl0)).mpr
    have hr := Nat.mod_lt N hl0
    have he := Nat.div_add_mod N l
    have hr' : ((N % l : ℕ) : ℝ) ≤ l := by exact_mod_cast (Nat.le_of_lt hr)
    have he' : (l : ℝ) * (N / l : ℕ) + (N % l : ℕ) = N := by exact_mod_cast he
    nlinarith
  calc
    (N : ℝ) * (harmonic L : ℝ) = ∑ l ∈ Icc 1 L, (N : ℝ) / l := by
      simp [harmonic_eq_sum_Icc, mul_sum, div_eq_mul_inv]
    _ ≤ ∑ l ∈ Icc 1 L, (((N / l : ℕ) : ℝ) + 1) := sum_le_sum hterm
    _ = (∑ l ∈ Icc 1 L, N / l : ℕ) + L := by
      simp [sum_add_distrib, ← Nat.cast_sum]

/-- Distinct consecutive sums forbid even a global linear envelope. -/
theorem no_linear_envelope (a : ℕ → ℕ) (ha : HasDistinctSums a) (C : ℕ) :
    ¬ (∀ t, a t ≤ C * (t + 1)) := by
  intro hC
  let L := Nat.floor (Real.exp ((C : ℝ) + 2))
  have hL : (C : ℝ) + 1 < (harmonic L : ℝ) := by
    have h := log_le_harmonic_floor (Real.exp ((C : ℝ) + 2)) (le_of_lt (Real.exp_pos _))
    rw [Real.log_exp] at h
    dsimp [L]
    linarith
  let N := C * L^2 + L + 2
  have hf : ((∑ l ∈ Icc 1 L, N / l : ℕ) : ℝ) ≤ (C : ℝ) * (N + (L : ℝ)^2) + 1 := by
    exact_mod_cast floor_sum_le_of_linear a ha C hC N L
  have hh := harmonic_mul_le_floor_sum N L
  have hN : (N : ℝ) = (C : ℝ) * (L : ℝ)^2 + L + 2 := by
    simp [N]
  have hNpos : (0 : ℝ) < N := by positivity
  have hm := mul_lt_mul_of_pos_left hL hNpos
  nlinarith



/-- An eventual linear envelope can absorb its finite prefix, so is impossible too. -/
theorem superlinear_late (a : ℕ → ℕ) (ha : HasDistinctSums a)
    (hm : StrictMono a) (C N : ℕ) :
    ∃ n, N ≤ n ∧ C * (n + 1) < a n := by
  by_contra h
  push_neg at h
  apply no_linear_envelope a ha (C + a N)
  intro t
  by_cases ht : N ≤ t
  · have := h t ht
    nlinarith
  · have := hm.monotone (show t ≤ N by omega)
    nlinarith

@[simp] theorem nat_ncard_Iio (n : ℕ) : (Set.Iio n).ncard = n := by
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

theorem range_ncard_below (a : ℕ → ℕ) (hm : StrictMono a) (n : ℕ) :
    (Set.range a ∩ Set.Iio (a n)).ncard = n := by
  have he : Set.range a ∩ Set.Iio (a n) = a '' Set.Iio n := by
    ext x
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hm.lt_iff_lt.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hm hi⟩
  rw [he, Set.ncard_image_of_injective _ hm.injective]
  exact nat_ncard_Iio n

/-- The known lower-density conclusion, stated directly as a liminf. -/
theorem range_liminf_density_zero (a : ℕ → ℕ) (ha : HasDistinctSums a)
    (hm : StrictMono a) :
    Filter.liminf (fun b : ℕ ↦ ((Set.range a ∩ Set.Iio b).ncard : ℝ) / b)
      Filter.atTop = 0 := by
  let d := fun b : ℕ ↦ ((Set.range a ∩ Set.Iio b).ncard : ℝ) / b
  have hz : ∀ᶠ b in Filter.atTop, (0 : ℝ) ≤ d b :=
    Filter.Eventually.of_forall (fun b ↦ by dsimp [d]; positivity)
  have hu : ∀ r : ℝ, (∀ᶠ b in Filter.atTop, r ≤ d b) → r ≤ 0 := by
    intro r hr
    by_contra hn
    have hrpos : 0 < r := by linarith
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hrpos
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hr
    obtain ⟨n, hnB, hn⟩ := superlinear_late a ha hm (k + 1) B
    have han : 0 < a n := by omega
    have hcross : (n : ℝ) * (k + 1) < a n := by
      exact_mod_cast (show n * (k + 1) < a n by nlinarith)
    have hsmall : (n : ℝ) / a n < 1 / ((k : ℝ) + 1) := by
      apply (div_lt_div_iff₀ (by exact_mod_cast han) (by positivity)).mpr
      simpa using hcross
    have hlarge := hB (a n) (le_trans hnB (hm.id_le n))
    dsimp [d] at hlarge
    rw [range_ncard_below a hm n] at hlarge
    linarith
  rw [Filter.liminf_eq]
  change sSup {r : ℝ | ∀ᶠ b in Filter.atTop, r ≤ d b} = 0
  apply le_antisymm
  · exact csSup_le ⟨0, hz⟩ hu
  · exact le_csSup ⟨0, hu⟩ hz

/-- Exact expansion of upstream Set.lowerDensity at the default ambient set univ.
The local project lacks the FormalConjecturesForMathlib density import. -/
theorem infinite_set_lower_density (a : ℕ → ℕ) (hm : StrictMono a)
    (ha : HasDistinctSums a) :
    Filter.liminf (fun b : ℕ ↦
      ((((Set.range a ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
        (Set.univ ∩ Set.Iio b).ncard)) Filter.atTop = 0 := by
  simpa using range_liminf_density_zero a ha hm

/-- A suffix crossing t has sum at most max(a_i,2t). -/
theorem crossing_interval {k : ℕ} (a : Fin k → ℕ) (hm : Monotone a)
    (i : Fin k) (t : ℕ) (hi : t < ∑ j ∈ Iic i, a j) :
    ∃ j ≤ i, t < ∑ x ∈ Icc j i, a x ∧
      ∑ x ∈ Icc j i, a x ≤ max (a i) (2 * t) := by
  classical
  let S := (Iic i).filter (fun j ↦ t < ∑ x ∈ Icc j i, a x)
  have hS : S.Nonempty := by
    let z : Fin k := ⟨0, by have := i.isLt; omega⟩
    refine ⟨z, mem_filter.mpr ⟨mem_Iic.mpr (by exact Nat.zero_le _), ?_⟩⟩
    have he : Icc z i = Iic i := by
      ext x
      simp only [mem_Icc, mem_Iic]
      exact and_iff_right (show z ≤ x from Nat.zero_le _)
    simpa [he] using hi
  let j := S.max' hS
  have hj := mem_filter.mp (S.max'_mem hS)
  have hji : j ≤ i := mem_Iic.mp hj.1
  refine ⟨j, hji, hj.2, ?_⟩
  by_cases heq : j = i
  · simp [heq]
  · have hjlt : j < i := lt_of_le_of_ne hji heq
    let u : Fin k := ⟨j.val + 1, by have := i.isLt; exact lt_of_le_of_lt hjlt i.isLt⟩
    have hu : u ≤ i := hjlt
    have htail : ∑ x ∈ Icc u i, a x ≤ t := by
      by_contra hn
      have huS : u ∈ S := mem_filter.mpr ⟨mem_Iic.mpr hu, by omega⟩
      have hle := S.le_max' u huS
      change u ≤ j at hle
      have : u.val ≤ j.val := hle
      dsimp [u] at this
      omega
    have hai : a i ≤ t := by
      have hmem : i ∈ Icc u i := mem_Icc.mpr ⟨hu, le_rfl⟩
      exact (single_le_sum (fun x _ ↦ Nat.zero_le (a x)) hmem).trans htail
    have haj : a j ≤ t := (hm hji).trans hai
    have he : Icc j i = insert j (Icc u i) := by
      ext x
      simp only [mem_Icc, mem_insert]
      change (j.val ≤ x.val ∧ x.val ≤ i.val) ↔
        x = j ∨ (j.val + 1 ≤ x.val ∧ x.val ≤ i.val)
      constructor
      · rintro ⟨hx, hxi⟩
        by_cases h : x.val = j.val
        · exact Or.inl (Fin.ext h)
        · exact Or.inr ⟨by omega, hxi⟩
      · rintro (rfl | ⟨hx, hxi⟩)
        · exact ⟨le_rfl, hji⟩
        · exact ⟨by omega, hxi⟩
    have hnot : j ∉ Icc u i := by
      simp only [mem_Icc, not_and]
      intro h
      have : j.val + 1 ≤ j.val := h
      omega
    rw [he, sum_insert hnot]
    exact (Nat.add_le_add haj htail).trans (by omega)

/-- Positive strict increase supplies the triangular prefix lower bound. -/
theorem prefix_twice_lower {k : ℕ} (a : Fin k → ℕ) (hm : StrictMono a)
    (hp : ∀ i, 0 < a i) (i : Fin k) :
    (i.val + 1) * (i.val + 2) ≤ 2 * ∑ j ∈ Iic i, a j := by
  have hlower : ∀ v (hv : v < k), v + 1 ≤ a ⟨v, hv⟩ := by
    intro v
    induction v with
    | zero => intro hv; exact hp _
    | succ v ih =>
      intro hv
      have hv' : v < k := by omega
      have h := ih hv'
      have h' := hm (show (⟨v, hv'⟩ : Fin k) < ⟨v + 1, hv⟩ from Nat.lt_succ_self v)
      omega
  have hsum : ∑ j ∈ Iic i, (j.val + 1) ≤ ∑ j ∈ Iic i, a j :=
    sum_le_sum (fun j _ ↦ hlower j.val j.isLt)
  have he : (Iic i).map Fin.valEmbedding = range (i.val + 1) := by
    rw [Fin.map_valEmbedding_Iic]
    ext x
    simp only [mem_Iic, mem_range]
    omega
  have hs : ∑ j ∈ Iic i, (j.val + 1) = ∑ j ∈ range (i.val + 1), (j + 1) := by
    rw [← he, sum_map]
    rfl
  rw [hs, sum_add_distrib] at hsum
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hsum
  have hgauss := sum_range_id_mul_two (i.val + 1)
  simp only [Nat.add_sub_cancel] at hgauss
  nlinarith

/-- Every sufficiently long prefix crosses floor(n/2). -/
theorem prefix_crosses_half {k : ℕ} (a : Fin k → ℕ) (hm : StrictMono a)
    (hp : ∀ i, 0 < a i) (n : ℕ) (i : Fin k) (hi : Nat.sqrt n ≤ i.val) :
    n / 2 < ∑ j ∈ Iic i, a j := by
  have hprefix := prefix_twice_lower a hm hp i
  have hsqrt := Nat.lt_succ_sqrt n
  have hsq : (Nat.sqrt n + 1)^2 ≤ (i.val + 1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hdiv := Nat.div_mul_le_self n 2
  nlinarith
/-- The audited finite crossing bound; it applies to finite sequences directly. -/
theorem finite_length_le_half_add_sqrt {k n : ℕ} (a : Fin k → ℕ)
    (hm : StrictMono a) (hp : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ n)
    (ha : HasDistinctSums a) : k ≤ n - n / 2 + Nat.sqrt n := by
  classical
  by_cases hk : k ≤ Nat.sqrt n
  · omega
  let m : Fin k := ⟨Nat.sqrt n, by omega⟩
  let S := Ici m
  have hc : ∀ i : S, ∃ j ≤ (i : Fin k),
      n / 2 < ∑ x ∈ Icc j (i : Fin k), a x ∧
      ∑ x ∈ Icc j (i : Fin k), a x ≤ max (a i) (2 * (n / 2)) := by
    intro i
    apply crossing_interval a hm.monotone
    apply prefix_crosses_half a hm hp
    have hle : m ≤ (i : Fin k) := mem_Ici.mp i.property
    exact hle
  choose start hstart using hc
  let v : S → ℕ := fun i ↦ ∑ x ∈ Icc (start i) (i : Fin k), a x
  have hv (i : S) : v i ∈ Ioc (n / 2) n := by
    apply mem_Ioc.mpr
    refine ⟨(hstart i).2.1, (hstart i).2.2.trans ?_⟩
    apply max_le (hb i)
    omega
  have hinj : Function.Injective v := by
    intro i j he
    have hI : Icc (start i) (i : Fin k) = Icc (start j) (j : Fin k) := by
      apply ha
      · simpa only [Set.mem_setOf_eq, coe_Icc] using
          (Set.ordConnected_Icc : (Set.Icc (start i) (i : Fin k)).OrdConnected)
      · simpa only [Set.mem_setOf_eq, coe_Icc] using
          (Set.ordConnected_Icc : (Set.Icc (start j) (j : Fin k)).OrdConnected)
      · exact he
    have hi : (i : Fin k) ∈ Icc (start i) (i : Fin k) :=
      mem_Icc.mpr ⟨(hstart i).1, le_rfl⟩
    have hj : (j : Fin k) ∈ Icc (start j) (j : Fin k) :=
      mem_Icc.mpr ⟨(hstart j).1, le_rfl⟩
    have hij := (mem_Icc.mp (hI ▸ hi)).2
    have hji := (mem_Icc.mp (hI.symm ▸ hj)).2
    exact Subtype.ext (le_antisymm hij hji)
  have hcount : S.card ≤ n - n / 2 := by
    calc
      S.card = (univ.image v).card := by rw [card_image_of_injective _ hinj]; simp
      _ ≤ (Ioc (n / 2) n).card := card_le_card (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        exact hv i)
      _ = n - n / 2 := Nat.card_Ioc _ _
  have hcard : S.card = k - Nat.sqrt n := by simp [S, m, Fin.card_Ici]
  rw [hcard] at hcount
  omega

/-- Integer-valued version, with exactly the finite admissibility assumptions upstream. -/
theorem finite_int_length_le_half_add_sqrt {k n : ℕ} (a : Fin k → ℤ)
    (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ)) (hm : StrictMono a)
    (ha : HasDistinctSums a) : k ≤ n - n / 2 + Nat.sqrt n := by
  let b := fun i ↦ (a i).toNat
  have hab (i : Fin k) : 1 ≤ a i ∧ a i ≤ n := hr ⟨i, rfl⟩
  have he (i : Fin k) : (b i : ℤ) = a i := Int.toNat_of_nonneg (by have := (hab i).1; omega)
  have hm' : StrictMono b := by
    intro i j hij
    have hh := hm hij
    rw [← he i, ← he j] at hh
    exact_mod_cast hh
  have hp : ∀ i, 0 < b i := by
    intro i
    have hh := (hab i).1
    rw [← he i] at hh
    omega
  have hb : ∀ i, b i ≤ n := by
    intro i
    have hh := (hab i).2
    rw [← he i] at hh
    exact_mod_cast hh
  have hdistinct : HasDistinctSums b := by
    intro J hJ K hK hs
    apply ha hJ hK
    have hc := congrArg (fun z : ℕ ↦ (z : ℤ)) hs
    simpa only [Nat.cast_sum, he] using hc
  exact finite_length_le_half_add_sqrt b hm' hp hb hdistinct

/-- Verbatim upstream extremal function (Formal Conjectures Authors, Apache-2.0). -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

example (n : ℕ) : f n = sSup {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a} := rfl

/-- A finite upper bound from the crossing-sum argument; not the open little-o claim. -/
theorem f_le_half_add_sqrt (n : ℕ) : f n ≤ (n + 1) / 2 + Nat.sqrt n := by
  unfold f
  apply csSup_le'
  intro k hk
  obtain ⟨a, hr, hm, ha⟩ := hk
  have h := finite_int_length_le_half_add_sqrt a hr hm ha
  omega

/-- A division-free form of the same bound. -/
theorem two_mul_f_le (n : ℕ) : 2 * f n ≤ n + 2 * Nat.sqrt n + 1 := by
  have h := f_le_half_add_sqrt n
  omega

/-! Modulus-22 construction discovered by the local periodic-residue search.
The generic lifting proof is independent of the finite numerical checks.
No claim of literature priority is made. -/
namespace Mod22

def residue : Fin 6 → ℕ := ![2, 6, 9, 12, 18, 19]
def pref : Fin 6 → ZMod 22 := ![0, 2, 8, 17, 7, 3]
def phase (i : ℕ) : Fin 6 := ⟨i % 6, Nat.mod_lt _ (by decide)⟩
def a (m i : ℕ) : ℕ := 22 * (m + 1)^2 + 22 * (i / 6) + residue (phase i)

theorem phase_succ (i : ℕ) : phase (i+1) = phase i + 1 := by
  apply Fin.ext
  simp [phase, Fin.val_add, Nat.add_mod]

theorem a_cast (m i : ℕ) : (a m i : ZMod 22) = residue (phase i) := by
  have h22 : (22 : ZMod 22) = 0 := by decide
  simp [a, h22]

-- Finite certificates generated with erdos.witness.finite_check below.
theorem pref_step : (∀ i : Fin 6, pref (i + 1) = pref i + residue i) := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem length_certificate : (∀ i j u v : Fin 6, pref j - pref i = pref v - pref u → (j.val + 6 - i.val) % 6 = (v.val + 6 - u.val) % 6) := by decide

theorem prefix_cast (m n : ℕ) :
    ((∑ t ∈ range n, a m t : ℕ) : ZMod 22) = pref (phase n) := by
  induction n with
  | zero => norm_num [phase, pref]
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_add, ih, a_cast, phase_succ, pref_step]

theorem block_cast (m i l : ℕ) :
    ((∑ t ∈ range l, a m (i+t) : ℕ) : ZMod 22) = pref (phase (i+l)) - pref (phase i) := by
  have h := congrArg (fun x : ℕ ↦ (x : ZMod 22)) (sum_range_add (a m) i l)
  dsimp only at h
  rw [Nat.cast_add, prefix_cast, prefix_cast] at h
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h.symm)

theorem block_lengths_mod (m i l j r : ℕ)
    (h : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : l % 6 = r % 6 := by
  have hc := congrArg (fun x : ℕ ↦ (x : ZMod 22)) h
  dsimp only at hc
  rw [block_cast, block_cast] at hc
  have he := length_certificate (phase i) (phase (i+l)) (phase j) (phase (j+r)) hc
  dsimp [phase] at he
  have hi := Nat.add_mod i l 6
  have hj := Nat.add_mod j r 6
  omega

theorem residue_bounds (i : Fin 6) :
    22 * i.val + 4 ≤ 6 * residue i ∧ 6 * residue i ≤ 22 * i.val + 20 := by
  fin_cases i <;> decide

theorem a_bounds (m i : ℕ) :
    132 * (m+1)^2 + 22*i + 4 ≤ 6*a m i ∧
    6*a m i ≤ 132 * (m+1)^2 + 22*i + 20 := by
  have h := residue_bounds (phase i)
  have hd := Nat.mod_add_div i 6
  dsimp [a, phase] at *
  constructor <;> nlinarith

theorem a_pos (m i : ℕ) : 0 < a m i := by
  have := (a_bounds m i).1
  omega

theorem a_mono (m : ℕ) : StrictMono (a m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h1 := (a_bounds m i).2
  have h2 := (a_bounds m (i+1)).1
  omega

theorem a_shift (m i t : ℕ) : 6*a m (i+t) ≤ 6*a m t + 22*i + 16 := by
  have h1 := (a_bounds m (i+t)).2
  have h2 := (a_bounds m t).1
  omega


theorem block_shift (m i l : ℕ) :
    6 * ∑ t ∈ range l, a m (i+t) ≤
      6 * ∑ t ∈ range l, a m t + l * (22*i+16) := by
  have h := sum_le_sum (s := range l) (fun t _ ↦ a_shift m i t)
  simpa [sum_add_distrib, ← mul_sum, mul_add, add_assoc] using h

theorem block_start_le (m i l : ℕ) :
    ∑ t ∈ range l, a m t ≤ ∑ t ∈ range l, a m (i+t) := by
  apply sum_le_sum
  intro t ht
  exact (a_mono m).monotone (by omega)

theorem block_length_growth (m l r : ℕ) (hlr : l ≤ r) :
    (∑ t ∈ range l, a m t) + (r-l) * (22*(m+1)^2) ≤ ∑ t ∈ range r, a m t := by
  have he : r = l + (r-l) := by omega
  rw [he, sum_range_add]
  have h : (r-l)*(22*(m+1)^2) ≤ ∑ t ∈ range (r-l), a m (l+t) := by
    calc
      _ = ∑ _t ∈ range (r-l), 22*(m+1)^2 := by simp
      _ ≤ _ := sum_le_sum (fun t _ ↦ by simp only [a]; omega)
  simpa only [Nat.add_sub_cancel_left] using Nat.add_le_add_left h _

theorem block_length_eq (m i l j r : ℕ) (hi : i+l ≤ 12*m) (hj : j+r ≤ 12*m)
    (he : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : l = r := by
  suffices hone : ∀ i l j r : ℕ, i+l ≤ 12*m → j+r ≤ 12*m → l ≤ r →
      (∑ t ∈ range l, a m (i+t)) = (∑ t ∈ range r, a m (j+t)) → l = r by
    rcases le_total l r with hlr | hrl
    · exact hone i l j r hi hj hlr he
    · exact (hone j r i l hj hi hrl he.symm).symm
  intro i l j r hi hj hlr he
  by_contra hne
  have hmod := block_lengths_mod m i l j r he
  have hgap : 6 ≤ r-l := by omega
  have hg := block_length_growth m l r hlr
  have hs := block_start_le m j r
  have ht := block_shift m i l
  rw [he] at ht
  have hbase := Nat.mul_le_mul_right (22*(m+1)^2) hgap
  have hib : l*(22*i+16) ≤ l*(22*(12*m-l)+16) := Nat.mul_le_mul_left _ (by omega)
  have hsq : 0 ≤ (2*(l : ℤ)-12*m)^2 := sq_nonneg _
  have hln : l ≤ 12*m := by omega
  have hsub : (12*m-l : ℕ) + l = 12*m := by omega
  nlinarith


theorem block_inj (m i l j r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (hi : i+l ≤ 12*m) (hj : j+r ≤ 12*m)
    (he : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : i = j ∧ l = r := by
  have hlen := block_length_eq m i l j r hi hj he
  subst r
  have hf : StrictMono (fun i ↦ ∑ t ∈ range l, a m (i+t)) := by
    intro x y hxy
    apply sum_lt_sum
    · intro t ht
      exact le_of_lt (a_mono m (by omega))
    · exact ⟨0, mem_range.mpr hl, a_mono m (by omega)⟩
  exact ⟨hf.injective he, rfl⟩

end Mod22

/-- A nonempty connected finite index set is a natural block after taking values. -/
theorem fin_interval_encoding {k : ℕ} (J : Finset (Fin k))
    (hc : (J : Set (Fin k)).OrdConnected) (hJ : J.Nonempty) :
    ∃ i l : ℕ, 0 < l ∧ i+l ≤ k ∧ J.map Fin.valEmbedding = Ico i (i+l) := by
  classical
  let u := J.min' hJ
  let v := J.max' hJ
  have hu : u ∈ J := J.min'_mem hJ
  have hv : v ∈ J := J.max'_mem hJ
  have huv : u ≤ v := J.min'_le _ hv
  have hEq : J = Icc u v := by
    ext x
    constructor
    · intro hx
      exact mem_Icc.mpr ⟨J.min'_le _ hx, J.le_max' _ hx⟩
    · intro hx
      exact hc.out hu hv (mem_Icc.mp hx)
  refine ⟨u.val, v.val+1-u.val, by omega, by have := v.isLt; omega, ?_⟩
  rw [hEq, Fin.map_valEmbedding_Icc]
  ext x
  simp only [mem_Icc, mem_Ico]
  have h := huv
  change u.val ≤ v.val at h
  omega

/-- Bridge a natural block-injectivity argument to the literal finite predicate. -/
theorem hasDistinctSums_of_block_inj (a : ℕ → ℕ) (k : ℕ) (hp : ∀ i, 0 < a i)
    (hb : ∀ i l j r : ℕ, 0 < l → 0 < r → i+l ≤ k → j+r ≤ k →
      (∑ t ∈ range l, a (i+t)) = (∑ t ∈ range r, a (j+t)) → i = j ∧ l = r) :
    HasDistinctSums (fun i : Fin k ↦ a i.val) := by
  classical
  intro J hJ K hK he
  have hzero (S : Finset (Fin k)) : (∑ x ∈ S, a x.val) = 0 ↔ S = ∅ := by
    constructor
    · intro hz
      by_contra hn
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      have ht := single_le_sum (fun y _ ↦ Nat.zero_le (a y.val)) hx
      have hh := hp x.val
      omega
    · rintro rfl; simp
  by_cases hj : J = ∅
  · subst J
    have hk : K = ∅ := (hzero K).mp (by simpa using he.symm)
    exact hk.symm
  by_cases hk : K = ∅
  · subst K
    exact (hzero J).mp (by simpa using he)
  obtain ⟨i,l,hl,hil,hmapJ⟩ := fin_interval_encoding J hJ (nonempty_iff_ne_empty.mpr hj)
  obtain ⟨j,r,hr,hjr,hmapK⟩ := fin_interval_encoding K hK (nonempty_iff_ne_empty.mpr hk)
  have hsum (S : Finset (Fin k)) (i l : ℕ)
      (hs : S.map Fin.valEmbedding = Ico i (i+l)) :
      ∑ x ∈ S, a x.val = ∑ t ∈ range l, a (i+t) := by
    have hh : ∑ x ∈ S, a x.val = ∑ x ∈ S.map Fin.valEmbedding, a x := by simp
    rw [hh, hs, sum_Ico_eq_sum_range]
    simp
  dsimp only at he
  rw [hsum J i l hmapJ, hsum K j r hmapK] at he
  obtain ⟨rfl, rfl⟩ := hb i l j r hl hr hil hjr he
  have hm : J.map Fin.valEmbedding = K.map Fin.valEmbedding := hmapJ.trans hmapK.symm
  exact Finset.map_injective _ hm

namespace Mod22

theorem a_distinct (m : ℕ) : HasDistinctSums (fun i : Fin (12*m) ↦ a m i.val) :=
  hasDistinctSums_of_block_inj (a m) (12*m) (a_pos m) (block_inj m)


theorem a_upper (m i : ℕ) (hi : i < 12*m) : a m i ≤ 22*(m+2)^2 := by
  have h := (a_bounds m i).2
  nlinarith

theorem int_admissible (m : ℕ) :
    ∃ b : Fin (12*m) → ℤ, Set.range b ⊆ Set.Icc 1 (22*(m+2)^2 : ℕ) ∧
      StrictMono b ∧ HasDistinctSums b := by
  let b : Fin (12*m) → ℤ := fun i ↦ (a m i.val : ℤ)
  refine ⟨b, ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    have hp := a_pos m i.val
    have hu := a_upper m i.val i.isLt
    constructor
    · dsimp [b]; exact_mod_cast (show 1 ≤ a m i.val by omega)
    · dsimp [b]; exact_mod_cast hu
  · intro i j hij
    have h := a_mono m hij
    change (a m i.val : ℤ) < (a m j.val : ℤ)
    exact_mod_cast h
  · intro J hJ K hK he
    apply a_distinct m hJ hK
    dsimp [b] at he
    exact_mod_cast he

end Mod22

/-- Every admissible length lies below the literal upstream supremum. -/
theorem admissible_length_le_f {k n : ℕ} (a : Fin k → ℤ)
    (hr : Set.range a ⊆ Set.Icc 1 n) (hm : StrictMono a) (ha : HasDistinctSums a) :
    k ≤ f n := by
  unfold f
  apply le_csSup
  · refine ⟨n - n/2 + Nat.sqrt n, ?_⟩
    rintro l ⟨b, hbr, hbm, hba⟩
    exact finite_int_length_le_half_add_sqrt b hbr hbm hba
  · exact ⟨a, hr, hm, ha⟩

/-- Explicit modulus-22 construction for every natural parameter m. -/
theorem mod22_lower (m : ℕ) : 12*m ≤ f (22*(m+2)^2) := by
  obtain ⟨a, hr, hm, ha⟩ := Mod22.int_admissible m
  exact admissible_length_le_f a hr hm ha

/-- Floor-form lower bound, valid for every n. -/
theorem mod22_lower_all (n : ℕ) : 12*(Nat.sqrt (n/22)-2) ≤ f n := by
  let q := Nat.sqrt (n/22)
  by_cases hq : q < 2
  · have hzero : Nat.sqrt (n/22)-2 = 0 := by omega
    simp [hzero]
  have hsq := Nat.sqrt_le (n/22)
  have hd := Nat.div_mul_le_self n 22
  have hqn : 22*((q-2)+2)^2 ≤ n := by
    have he : q-2+2 = q := by omega
    rw [he]
    dsimp [q]
    nlinarith
  obtain ⟨a, hr, hm, ha⟩ := Mod22.int_admissible (q-2)
  apply admissible_length_le_f a ?_ hm ha
  intro x hx
  have hh := hr hx
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact_mod_cast hqn

/-- Quantitative real form; the asymptotic square-root coefficient is 12/sqrt(22). -/
theorem mod22_lower_real (n : ℕ) :
    (12 / Real.sqrt 22) * Real.sqrt n - 36 ≤ (f n : ℝ) := by
  let q := Nat.sqrt (n/22)
  have hf := mod22_lower_all n
  have hq : 12*(q+1) ≤ f n + 36 := by dsimp [q]; omega
  have hn : n < 22*(q+1)^2 := by
    have hs := Nat.lt_succ_sqrt (n/22)
    have hd := Nat.mod_lt n (by decide : 0 < 22)
    have he := Nat.div_add_mod n 22
    dsimp [q]
    nlinarith
  have h22 : 0 < Real.sqrt 22 := Real.sqrt_pos.mpr (by norm_num)
  have hs22 : (Real.sqrt 22)^2 = 22 := Real.sq_sqrt (by norm_num)
  have hroot : Real.sqrt n ≤ Real.sqrt 22 * ((q : ℝ)+1) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hn' : (n : ℝ) ≤ 22*((q : ℝ)+1)^2 := by exact_mod_cast (Nat.le_of_lt hn)
      nlinarith
  have hq' : (12 : ℝ)*((q : ℝ)+1) ≤ (f n : ℝ)+36 := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left hq' (le_of_lt h22)
  have hh' := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 12)
  have hfinal : (12 * Real.sqrt n) / Real.sqrt 22 ≤ (f n : ℝ)+36 := by
    apply (div_le_iff₀ h22).mpr
    nlinarith
  calc
    (12 / Real.sqrt 22) * Real.sqrt n - 36 =
        (12 * Real.sqrt n) / Real.sqrt 22 - 36 := by ring
    _ ≤ (f n : ℝ) := by linarith
/-! Modulus-42 construction (residues 2,7,11,25,26,34; consecutive-sum residue spectra of
lengths 0..11 partition Z/42, so equal sums force equal lengths modulo 12; score 12/7).
It was found by the exact residue-set search problems/0357/modular_dfs.py and is
proved with the same scheme as Mod22, using a 12-periodic prefix table because the
residue total 105 is 21 mod 42, not 0. No literature priority is claimed. -/

namespace Mod42

def residue : Fin 12 → ℕ := ![2, 7, 11, 25, 26, 34, 2, 7, 11, 25, 26, 34]
def pref : Fin 12 → ZMod 42 := ![0, 2, 9, 20, 3, 29, 21, 23, 30, 41, 24, 8]
def phase (i : ℕ) : Fin 12 := ⟨i % 12, Nat.mod_lt _ (by decide)⟩
def tri (m : ℕ) : ℕ := m * (m + 1) / 2 + 1
def base (m : ℕ) : ℕ := 42 * tri m
def a (m i : ℕ) : ℕ := base m + 42 * (i / 6) + residue (phase i)

theorem two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) + 2 := by
  have h : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  unfold tri
  have := Nat.mul_div_cancel' h
  omega

theorem tri_pos (m : ℕ) : 1 ≤ tri m := Nat.le_add_left _ _

theorem phase_succ (i : ℕ) : phase (i+1) = phase i + 1 := by
  apply Fin.ext
  simp [phase, Fin.val_add, Nat.add_mod]

theorem a_cast (m i : ℕ) : (a m i : ZMod 42) = residue (phase i) := by
  have h42 : (42 : ZMod 42) = 0 := by decide
  simp [a, base, h42]

theorem pref_step : (∀ i : Fin 12, pref (i + 1) = pref i + residue i) := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem length_certificate : (∀ i j u v : Fin 12, pref j - pref i = pref v - pref u →
    (j.val + 12 - i.val) % 12 = (v.val + 12 - u.val) % 12) := by decide

theorem prefix_cast (m n : ℕ) :
    ((∑ t ∈ range n, a m t : ℕ) : ZMod 42) = pref (phase n) := by
  induction n with
  | zero => norm_num [phase, pref]
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_add, ih, a_cast, phase_succ, pref_step]

theorem block_cast (m i l : ℕ) :
    ((∑ t ∈ range l, a m (i+t) : ℕ) : ZMod 42) = pref (phase (i+l)) - pref (phase i) := by
  have h := congrArg (fun x : ℕ ↦ (x : ZMod 42)) (sum_range_add (a m) i l)
  dsimp only at h
  rw [Nat.cast_add, prefix_cast, prefix_cast] at h
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h.symm)

theorem block_lengths_mod (m i l j r : ℕ)
    (h : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : l % 12 = r % 12 := by
  have hc := congrArg (fun x : ℕ ↦ (x : ZMod 42)) h
  dsimp only at hc
  rw [block_cast, block_cast] at hc
  have he := length_certificate (phase i) (phase (i+l)) (phase j) (phase (j+r)) hc
  dsimp [phase] at he
  omega

theorem residue_bounds (i : Fin 12) :
    7 * (i.val % 6) ≤ residue i + 3 ∧ residue i ≤ 7 * (i.val % 6) + 4 := by
  fin_cases i <;> decide

theorem residue_step (i : Fin 12) :
    residue i < residue (i + 1) + 42 * (if i.val % 6 = 5 then 1 else 0) := by
  fin_cases i <;> decide

theorem a_bounds (m i : ℕ) :
    base m + 7 * i ≤ a m i + 3 ∧ a m i ≤ base m + 7 * i + 4 := by
  have h := residue_bounds (phase i)
  dsimp [a, phase] at *
  omega

theorem base_ge (m : ℕ) : 42 ≤ base m := by
  have := tri_pos m
  unfold base
  omega

theorem a_pos (m i : ℕ) : 0 < a m i := by
  have := base_ge m
  unfold a
  omega

theorem a_mono (m : ℕ) : StrictMono (a m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h := residue_step (phase i)
  have hp : phase (i+1) = phase i + 1 := phase_succ i
  unfold a
  rw [hp]
  have hv : (phase i).val = i % 12 := rfl
  rw [hv] at h
  by_cases h5 : (i % 12) % 6 = 5
  · have h5' : i % 6 = 5 := by omega
    have hd : (i+1)/6 = i/6 + 1 := by omega
    simp only [h5, if_true] at h
    omega
  · have h5' : ¬ i % 6 = 5 := by omega
    have hd : (i+1)/6 = i/6 := by omega
    simp only [h5, if_false] at h
    omega

theorem a_shift (m i t : ℕ) : a m (i+t) ≤ a m t + 7*i + 7 := by
  have h1 := (a_bounds m (i+t)).2
  have h2 := (a_bounds m t).1
  omega

theorem block_shift (m i l : ℕ) :
    ∑ t ∈ range l, a m (i+t) ≤ ∑ t ∈ range l, a m t + l * (7*i+7) := by
  have h := sum_le_sum (s := range l) (fun t _ ↦ a_shift m i t)
  simpa [sum_add_distrib, mul_add, add_assoc] using h

theorem block_start_le (m i l : ℕ) :
    ∑ t ∈ range l, a m t ≤ ∑ t ∈ range l, a m (i+t) := by
  apply sum_le_sum
  intro t ht
  exact (a_mono m).monotone (by omega)

theorem block_length_growth (m l r : ℕ) (hlr : l ≤ r) :
    (∑ t ∈ range l, a m t) + (r-l) * base m ≤ ∑ t ∈ range r, a m t := by
  have he : r = l + (r-l) := by omega
  rw [he, sum_range_add]
  have h : (r-l)*base m ≤ ∑ t ∈ range (r-l), a m (l+t) := by
    calc
      _ = ∑ _t ∈ range (r-l), base m := by simp
      _ ≤ _ := sum_le_sum (fun t _ ↦ by simp only [a]; omega)
  simpa only [Nat.add_sub_cancel_left] using Nat.add_le_add_left h _

theorem block_length_eq (m i l j r : ℕ) (hi : i+l ≤ 12*m) (hj : j+r ≤ 12*m)
    (he : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : l = r := by
  suffices hone : ∀ i l j r : ℕ, i+l ≤ 12*m → j+r ≤ 12*m → l ≤ r →
      (∑ t ∈ range l, a m (i+t)) = (∑ t ∈ range r, a m (j+t)) → l = r by
    rcases le_total l r with hlr | hrl
    · exact hone i l j r hi hj hlr he
    · exact (hone j r i l hj hi hrl he.symm).symm
  intro i l j r hi hj hlr he
  by_contra hne
  have hmod := block_lengths_mod m i l j r he
  have hgap : 12 ≤ r-l := by omega
  have hg := block_length_growth m l r hlr
  have hs := block_start_le m j r
  have ht := block_shift m i l
  rw [he] at ht
  have hbase := Nat.mul_le_mul_right (base m) hgap
  have hib : l*(7*i+7) ≤ l*(7*(12*m-l)+7) := Nat.mul_le_mul_left _ (by omega)
  have h2 := two_mul_tri m
  have hb : base m = 42 * tri m := rfl
  obtain ⟨x, hx⟩ : ∃ x, 12*m - l = x := ⟨_, rfl⟩
  rw [hx] at hib
  have hlx : l + x = 12*m := by omega
  have key : 12 * base m ≤ l * (7*x+7) := by linarith
  have hm12 : ((l:ℤ) + x) = 12 * m := by exact_mod_cast hlx
  have hm2 : (144:ℤ) * (m*(m+1)) = (l+x)^2 + 12*(l+x) := by rw [hm12]; ring
  have h2' : (2:ℤ) * tri m = m*(m+1)+2 := by exact_mod_cast h2
  have key' : (12:ℤ) * (42 * tri m) ≤ l * (7*x+7) := by
    rw [hb] at key; exact_mod_cast key
  have hsq : 0 ≤ ((l : ℤ) - x - 1)^2 := sq_nonneg _
  have hl0 : (0:ℤ) ≤ l := by positivity
  have hx0 : (0:ℤ) ≤ x := by positivity
  nlinarith

theorem block_inj (m i l j r : ℕ) (hl : 0 < l) (hr : 0 < r)
    (hi : i+l ≤ 12*m) (hj : j+r ≤ 12*m)
    (he : ∑ t ∈ range l, a m (i+t) = ∑ t ∈ range r, a m (j+t)) : i = j ∧ l = r := by
  have hlen := block_length_eq m i l j r hi hj he
  subst r
  have hf : StrictMono (fun i ↦ ∑ t ∈ range l, a m (i+t)) := by
    intro x y hxy
    apply sum_lt_sum
    · intro t ht
      exact le_of_lt (a_mono m (by omega))
    · exact ⟨0, mem_range.mpr hl, a_mono m (by omega)⟩
  exact ⟨hf.injective he, rfl⟩

theorem a_distinct (m : ℕ) : HasDistinctSums (fun i : Fin (12*m) ↦ a m i.val) :=
  hasDistinctSums_of_block_inj (a m) (12*m) (a_pos m) (block_inj m)

theorem base_eq (m : ℕ) : base m = 21 * m^2 + 21 * m + 42 := by
  have h := two_mul_tri m
  unfold base
  nlinarith

theorem a_upper (m i : ℕ) (hi : i < 12*m) : a m i ≤ 21 * m^2 + 105 * m + 46 := by
  have h := (a_bounds m i).2
  have hb := base_eq m
  nlinarith

theorem int_admissible (m : ℕ) :
    ∃ b : Fin (12*m) → ℤ, Set.range b ⊆ Set.Icc 1 (21 * m^2 + 105 * m + 46 : ℕ) ∧
      StrictMono b ∧ HasDistinctSums b := by
  let b : Fin (12*m) → ℤ := fun i ↦ (a m i.val : ℤ)
  refine ⟨b, ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    have hp := a_pos m i.val
    have hu := a_upper m i.val i.isLt
    constructor
    · dsimp [b]; exact_mod_cast (show 1 ≤ a m i.val by omega)
    · dsimp [b]; exact_mod_cast hu
  · intro i j hij
    have h := a_mono m hij
    change (a m i.val : ℤ) < (a m j.val : ℤ)
    exact_mod_cast h
  · intro J hJ K hK he
    apply a_distinct m hJ hK
    dsimp [b] at he
    exact_mod_cast he

end Mod42

/-- Explicit modulus-42 construction for every natural parameter m. -/
theorem mod42_lower (m : ℕ) : 12*m ≤ f (21*m^2 + 105*m + 46) := by
  obtain ⟨a, hr, hm, ha⟩ := Mod42.int_admissible m
  exact admissible_length_le_f a hr hm ha

/-- Floor-form lower bound for the modulus-42 construction, valid for every n. -/
theorem mod42_lower_all (n : ℕ) : 12*(Nat.sqrt (n/21)-3) ≤ f n := by
  let q := Nat.sqrt (n/21)
  by_cases hq : q < 3
  · have hzero : Nat.sqrt (n/21)-3 = 0 := by omega
    simp [hzero]
  have hsq := Nat.sqrt_le (n/21)
  have hd := Nat.div_mul_le_self n 21
  have hqn : 21*(q-3)^2 + 105*(q-3) + 46 ≤ n := by
    obtain ⟨m, hm⟩ : ∃ m, q = m + 3 := ⟨q-3, by omega⟩
    have he : q - 3 = m := by omega
    rw [he]
    have h1 : q * q ≤ n / 21 := hsq
    rw [hm] at h1
    nlinarith
  obtain ⟨a, hr, hm, ha⟩ := Mod42.int_admissible (q-3)
  apply admissible_length_le_f a ?_ hm ha
  intro x hx
  have hh := hr hx
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact_mod_cast hqn

/-- Quantitative real form; the asymptotic square-root coefficient is 12/sqrt(21),
about 2.6186, above the modulus-22 coefficient 12/sqrt(22), about 2.5584. -/
theorem mod42_lower_real (n : ℕ) :
    (12 / Real.sqrt 21) * Real.sqrt n - 48 ≤ (f n : ℝ) := by
  let q := Nat.sqrt (n/21)
  have hf := mod42_lower_all n
  have hq : 12*(q+1) ≤ f n + 48 := by dsimp [q]; omega
  have hn : n < 21*(q+1)^2 := by
    have hs := Nat.lt_succ_sqrt (n/21)
    have hd := Nat.mod_lt n (by decide : 0 < 21)
    have he := Nat.div_add_mod n 21
    dsimp [q]
    nlinarith
  have h21 : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  have hs21 : (Real.sqrt 21)^2 = 21 := Real.sq_sqrt (by norm_num)
  have hroot : Real.sqrt n ≤ Real.sqrt 21 * ((q : ℝ)+1) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hn' : (n : ℝ) ≤ 21*((q : ℝ)+1)^2 := by exact_mod_cast (Nat.le_of_lt hn)
      nlinarith
  have hq' : (12 : ℝ)*((q : ℝ)+1) ≤ (f n : ℝ)+48 := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left hq' (le_of_lt h21)
  have hh' := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 12)
  have hfinal : (12 * Real.sqrt n) / Real.sqrt 21 ≤ (f n : ℝ)+48 := by
    apply (div_le_iff₀ h21).mpr
    nlinarith
  calc
    (12 / Real.sqrt 21) * Real.sqrt n - 48 =
        (12 * Real.sqrt n) / Real.sqrt 21 - 48 := by ring
    _ ≤ (f n : ℝ) := by linarith

/-! Exact reduction to ordered disjoint collisions. The cancellation idea is
standard; see Beker, arXiv:2311.10087, Section 2. No new upper bound is claimed. -/

/-- To rule out repeated positive differences, disjoint index intervals suffice. -/
theorem difference_inj_of_disjoint (p : ℕ → ℕ) (hp : StrictMono p) (k : ℕ)
    (hd : ∀ i j u v : ℕ, i < j → j ≤ u → u < v → v ≤ k →
      p j + p u ≠ p v + p i)
    {i j u v : ℕ} (hij : i < j) (huv : u < v) (hjk : j ≤ k) (hvk : v ≤ k)
    (he : p j + p u = p v + p i) : i = u ∧ j = v := by
  have aux (i j u v : ℕ) (hij : i < j) (huv : u < v)
      (hvk : v ≤ k) (hiu : i < u) (he : p j + p u = p v + p i) : False := by
    have hpiu := hp hiu
    have hjv : j < v := by
      apply hp.lt_iff_lt.mp
      omega
    by_cases hju : j ≤ u
    · exact hd i j u v hij hju huv hvk he
    · exact hd i u j v hiu (by omega) hjv hvk (by omega)
  rcases lt_trichotomy i u with hiu | hiu | hui
  · exact (aux i j u v hij huv hvk hiu he).elim
  · subst u
    exact ⟨rfl, hp.injective (by omega)⟩
  · exact (aux u v i j huv hij hjk hui (by omega)).elim

/-- Sums over disjoint nonempty blocks detect every violation of the finite predicate. -/
theorem hasDistinctSums_of_no_disjoint_collision (a : ℕ → ℕ) (k : ℕ)
    (hp : ∀ i, 0 < a i)
    (hd : ∀ i l j r : ℕ, 0 < l → 0 < r → i+l ≤ j → j+r ≤ k →
      (∑ t ∈ range l, a (i+t)) ≠ (∑ t ∈ range r, a (j+t))) :
    HasDistinctSums (fun i : Fin k ↦ a i.val) := by
  let p : ℕ → ℕ := fun n ↦ ∑ t ∈ range n, a t
  have hps : StrictMono p := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [p]
    rw [sum_range_succ]
    exact Nat.lt_add_of_pos_right (hp n)
  have hsplit (i l : ℕ) : p (i+l) = p i + ∑ t ∈ range l, a (i+t) := by
    dsimp [p]
    rw [sum_range_add]

  have hdis : ∀ i j u v : ℕ, i < j → j ≤ u → u < v → v ≤ k →
      p j + p u ≠ p v + p i := by
    intro i j u v hij hju huv hvk he
    have hj : i + (j-i) = j := by omega
    have hv : u + (v-u) = v := by omega
    have hs1 := hsplit i (j-i)
    have hs2 := hsplit u (v-u)
    rw [hj] at hs1
    rw [hv] at hs2
    exact hd i (j-i) u (v-u) (by omega) (by omega) (by omega) (by omega) (by omega)
  apply hasDistinctSums_of_block_inj a k hp
  intro i l j r hl hr hil hjr he
  have hi := hsplit i l
  have hj := hsplit j r
  obtain ⟨heq, hend⟩ := difference_inj_of_disjoint p hps k hdis
    (by omega : i < i+l) (by omega : j < j+r) hil hjr (by omega)
  exact ⟨heq, by omega⟩
/-- In a strictly increasing positive sequence, a later equal-sum block is shorter. -/
theorem later_equal_block_shorter (a : ℕ → ℕ) (hm : StrictMono a)
    {i l j r : ℕ} (hl : 0 < l) (hij : i < j)
    (he : (∑ t ∈ range l, a (i+t)) = (∑ t ∈ range r, a (j+t))) : r < l := by
  by_contra hn
  have hlr : l ≤ r := by omega
  have hlt : (∑ t ∈ range l, a (i+t)) < ∑ t ∈ range l, a (j+t) := by
    apply sum_lt_sum
    · intro t ht
      exact (hm (by omega : i+t < j+t)).le
    · exact ⟨0, mem_range.mpr hl, hm (by omega)⟩
  have hle : (∑ t ∈ range l, a (j+t)) ≤ ∑ t ∈ range r, a (j+t) := by
    exact sum_le_sum_of_subset (range_mono hlr)
  omega

/-- Only earlier-longer versus later-shorter disjoint blocks need be excluded. -/
theorem hasDistinctSums_of_no_ordered_collision (a : ℕ → ℕ) (k : ℕ)
    (hp : ∀ i, 0 < a i) (hm : StrictMono a)
    (hd : ∀ i l j r : ℕ, 0 < r → r < l → i+l ≤ j → j+r ≤ k →
      (∑ t ∈ range l, a (i+t)) ≠ (∑ t ∈ range r, a (j+t))) :
    HasDistinctSums (fun i : Fin k ↦ a i.val) := by
  apply hasDistinctSums_of_no_disjoint_collision a k hp
  intro i l j r hl hr hij hjr he
  have hrl := later_equal_block_shorter a hm hl (by omega : i < j) he
  exact hd i l j r hr hrl hij hjr he

/-- The literal finite predicate forces injectivity for natural block encodings. -/
theorem block_inj_of_hasDistinctSums (a : ℕ → ℕ) (k : ℕ)
    (ha : HasDistinctSums (fun i : Fin k ↦ a i.val))
    {i l j r : ℕ} (hl : 0 < l) (hr : 0 < r) (hil : i+l ≤ k) (hjr : j+r ≤ k)
    (he : (∑ t ∈ range l, a (i+t)) = (∑ t ∈ range r, a (j+t))) : i = j ∧ l = r := by
  classical
  let J : Finset (Fin k) := Icc ⟨i, by omega⟩ ⟨i+l-1, by omega⟩
  let K : Finset (Fin k) := Icc ⟨j, by omega⟩ ⟨j+r-1, by omega⟩
  have hJ : J.map Fin.valEmbedding = Ico i (i+l) := by
    dsimp [J]
    rw [Fin.map_valEmbedding_Icc]
    ext t
    simp only [mem_Icc, mem_Ico]
    omega
  have hK : K.map Fin.valEmbedding = Ico j (j+r) := by
    dsimp [K]
    rw [Fin.map_valEmbedding_Icc]
    ext t
    simp only [mem_Icc, mem_Ico]
    omega
  have hs (S : Finset (Fin k)) (x len : ℕ)
      (hS : S.map Fin.valEmbedding = Ico x (x+len)) :
      (∑ t ∈ S, a t.val) = ∑ t ∈ range len, a (x+t) := by
    have hh : (∑ t ∈ S, a t.val) = ∑ t ∈ S.map Fin.valEmbedding, a t := by simp
    rw [hh, hS, sum_Ico_eq_sum_range]
    simp
  have hJK : J = K := ha
    (by simpa only [Set.mem_setOf_eq, J, coe_Icc] using (Set.ordConnected_Icc :
      (Set.Icc (⟨i, by omega⟩ : Fin k) ⟨i+l-1, by omega⟩).OrdConnected))
    (by simpa only [Set.mem_setOf_eq, K, coe_Icc] using (Set.ordConnected_Icc :
      (Set.Icc (⟨j, by omega⟩ : Fin k) ⟨j+r-1, by omega⟩).OrdConnected))
    (by change (∑ t ∈ J, a t.val) = ∑ t ∈ K, a t.val
        rw [hs J i l hJ, hs K j r hK]
        exact he)
  have hmap : Ico i (i+l) = Ico j (j+r) := by rw [← hJ, ← hK, hJK]
  have hh : (i,l) = (j,r) := block_injective hl hr hmap
  exact Prod.mk.inj hh

/-- Exact finite equivalence; the natural sequence outside Fin k is not assumed admissible. -/
theorem hasDistinctSums_iff_no_ordered_collision (a : ℕ → ℕ) (k : ℕ)
    (hp : ∀ i, 0 < a i) (hm : StrictMono a) :
    HasDistinctSums (fun i : Fin k ↦ a i.val) ↔
      ∀ i l j r : ℕ, 0 < r → r < l → i+l ≤ j → j+r ≤ k →
        (∑ t ∈ range l, a (i+t)) ≠ (∑ t ∈ range r, a (j+t)) := by
  constructor
  · intro ha i l j r hr hrl hij hjr he
    obtain ⟨heq, _⟩ := block_inj_of_hasDistinctSums a k ha
      (by omega : 0 < l) hr (by omega : i+l ≤ k) hjr he
    omega
  · exact hasDistinctSums_of_no_ordered_collision a k hp hm


/-! Standard additive energy and the exact finite conjecture.
The energy count is standard; see the source audit in problems/0357/NOTES.md.
The final equivalence does not establish its energy-excess side or solve 357. -/

/-- Positive differences, represented by ordered pairs of values. -/
def positivePairs (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter (fun x ↦ x.1 < x.2)

/-- Multiplicity of an integer difference in a finite set. -/
def differenceMultiplicity (S : Finset ℤ) (d : ℤ) : ℕ :=
  ((S ×ˢ S).filter (fun x ↦ x.2-x.1=d)).card

/-- The number of unordered pairs of distinct positive-difference representations. -/
def collisionCount (S : Finset ℤ) : ℕ :=
  ∑ d ∈ (positivePairs S).image (fun x ↦ x.2-x.1),
    (differenceMultiplicity S d).choose 2

/-- Partition a symmetric sum on pairs into its diagonal and positive half. -/
theorem sum_pairs_symmetric (S : Finset ℤ) (w : ℤ × ℤ → ℕ)
    (hw : ∀ x y, w (x,y) = w (y,x)) :
    (∑ x ∈ S ×ˢ S, w x) = (∑ x ∈ S, w (x,x)) +
      2 * ∑ x ∈ positivePairs S, w x := by
  have hpart : (∑ x ∈ S ×ˢ S, w x) =
      (∑ x ∈ (S ×ˢ S).filter (fun x ↦ x.1=x.2), w x) +
      (∑ x ∈ (S ×ˢ S).filter (fun x ↦ x.1<x.2), w x) +
      (∑ x ∈ (S ×ˢ S).filter (fun x ↦ x.2<x.1), w x) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    split_ifs <;> omega
  have hn : (∑ x ∈ (S ×ˢ S).filter (fun x ↦ x.2<x.1), w x) =
      ∑ x ∈ positivePairs S, w x := by
    apply sum_bij (fun x _ ↦ x.swap)
    · intro x hx
      simpa [positivePairs, mem_filter, mem_product, and_comm, and_left_comm] using hx
    · intro x hx y hy he
      exact Prod.swap_injective he
    · intro y hy
      refine ⟨y.swap, ?_, by simp⟩
      simpa [positivePairs, mem_filter, mem_product, and_comm, and_left_comm] using hy
    · intro x hx
      exact hw x.1 x.2
  rw [hn, ← diag_eq_filter, sum_diag] at hpart
  dsimp only [positivePairs] at hpart ⊢
  omega

theorem twice_positivePairs_card (S : Finset ℤ) :
    S.card^2 = S.card + 2*(positivePairs S).card := by
  simpa [card_product, sq] using sum_pairs_symmetric S (fun _ ↦ 1) (by intros; rfl)

theorem differenceMultiplicity_zero (S : Finset ℤ) : differenceMultiplicity S 0 = S.card := by
  unfold differenceMultiplicity
  have he : (S ×ˢ S).filter (fun x ↦ x.2-x.1=0) = S.diag := by
    ext x
    simp only [mem_filter, mem_product, mem_diag]
    constructor
    · rintro ⟨⟨hx,hy⟩,he⟩; exact ⟨hx, by omega⟩
    · rintro ⟨hx,he⟩; exact ⟨⟨hx, he ▸ hx⟩, by omega⟩
  rw [he, diag_card]

theorem differenceMultiplicity_neg (S : Finset ℤ) (d : ℤ) :
    differenceMultiplicity S (-d) = differenceMultiplicity S d := by
  unfold differenceMultiplicity
  apply card_bij (fun x _ ↦ x.swap)
  · intro x hx
    simp only [mem_filter, mem_product] at hx ⊢
    exact ⟨⟨hx.1.2,hx.1.1⟩, by dsimp; omega⟩
  · intro x hx y hy he; exact Prod.swap_injective he
  · intro y hy
    refine ⟨y.swap, ?_, by simp⟩
    simp only [mem_filter, mem_product] at hy ⊢
    exact ⟨⟨hy.1.2,hy.1.1⟩, by dsimp; omega⟩

/-- This is Mathlib's additive energy, not a surrogate energy definition. -/
theorem addEnergy_eq_sum_multiplicity (S : Finset ℤ) :
    S.addEnergy S = ∑ x ∈ S ×ˢ S, differenceMultiplicity S (x.2-x.1) := by
  unfold addEnergy differenceMultiplicity
  simp only [card_eq_sum_ones, sum_filter, sum_product]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  congr 1
  apply propext
  omega

theorem positivePairs_fiber (S : Finset ℤ) {d : ℤ} (hd : 0 < d) :
    (positivePairs S).filter (fun x ↦ x.2-x.1=d) =
      (S ×ˢ S).filter (fun x ↦ x.2-x.1=d) := by
  ext x
  simp only [positivePairs, mem_filter]
  constructor
  · exact fun h ↦ ⟨h.1.1,h.2⟩
  · intro h; exact ⟨⟨h.1,by omega⟩,h.2⟩

theorem positive_diff_of_mem_image (S : Finset ℤ) {d : ℤ}
    (hd : d ∈ (positivePairs S).image (fun x ↦ x.2-x.1)) : 0 < d := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hd
  have h := (mem_filter.mp hx).2
  omega

theorem positive_weight_eq_sum_sq (S : Finset ℤ) :
    (∑ x ∈ positivePairs S, differenceMultiplicity S (x.2-x.1)) =
      ∑ d ∈ (positivePairs S).image (fun x ↦ x.2-x.1),
        (differenceMultiplicity S d)^2 := by
  have hf := sum_fiberwise_of_maps_to' (s := positivePairs S)
    (fun x hx ↦ mem_image_of_mem (fun x : ℤ × ℤ ↦ x.2-x.1) hx)
    (differenceMultiplicity S)
  rw [← hf]
  apply sum_congr rfl
  intro d hd
  rw [sum_const, nsmul_eq_mul, positivePairs_fiber S (positive_diff_of_mem_image S hd)]
  simp [differenceMultiplicity, sq]

theorem sum_positive_multiplicities (S : Finset ℤ) :
    (∑ d ∈ (positivePairs S).image (fun x ↦ x.2-x.1),
      differenceMultiplicity S d) = (positivePairs S).card := by
  rw [card_eq_sum_card_image (fun x : ℤ × ℤ ↦ x.2-x.1) (positivePairs S)]
  apply sum_congr rfl
  intro d hd
  rw [positivePairs_fiber S (positive_diff_of_mem_image S hd)]
  rfl

theorem square_eq_self_add_twice_choose (n : ℕ) : n^2 = n+2*n.choose 2 := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  cases n with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one]; ring

theorem addEnergy_positive_decomposition (S : Finset ℤ) :
    S.addEnergy S = S.card^2 + 2 *
      ∑ d ∈ (positivePairs S).image (fun x ↦ x.2-x.1),
        (differenceMultiplicity S d)^2 := by
  rw [addEnergy_eq_sum_multiplicity]
  have hw : ∀ x y : ℤ, differenceMultiplicity S (y-x) = differenceMultiplicity S (x-y) := by
    intro x y
    have he : y-x = -(x-y) := by ring
    rw [he, differenceMultiplicity_neg]
  rw [sum_pairs_symmetric S _ hw]
  simp only [sub_self, differenceMultiplicity_zero, sum_const, nsmul_eq_mul]
  rw [positive_weight_eq_sum_sq]
  simp [sq]

/-- Exact standard energy: baseline plus four times the unordered collision count. -/
theorem addEnergy_excess (S : Finset ℤ) :
    S.addEnergy S = 2*S.card^2-S.card+4*collisionCount S := by
  have hs : (∑ d ∈ (positivePairs S).image (fun x ↦ x.2-x.1),
      (differenceMultiplicity S d)^2) = (positivePairs S).card+2*collisionCount S := by
    simp_rw [square_eq_self_add_twice_choose]
    rw [sum_add_distrib, sum_positive_multiplicities, ← mul_sum]
    rfl
  have he := addEnergy_positive_decomposition S
  rw [hs] at he
  have hc := twice_positivePairs_card S
  omega

/-- No positive difference is repeated precisely when the excess vanishes. -/
theorem collisionCount_eq_zero_iff (S : Finset ℤ) : collisionCount S = 0 ↔
    Set.InjOn (fun x : ℤ × ℤ ↦ x.2-x.1) (positivePairs S : Set (ℤ × ℤ)) := by
  constructor
  · intro hz x hx y hy he
    have hmem := mem_image_of_mem (fun x : ℤ × ℤ ↦ x.2-x.1) hx
    have hle := single_le_sum (fun d _ ↦ Nat.zero_le ((differenceMultiplicity S d).choose 2)) hmem
    change _ ≤ collisionCount S at hle
    rw [hz] at hle
    have hzero : (differenceMultiplicity S (x.2-x.1)).choose 2 = 0 := Nat.eq_zero_of_le_zero hle
    have hcard : ((S ×ˢ S).filter (fun z ↦ z.2-z.1=x.2-x.1)).card ≤ 1 := by
      have := Nat.choose_eq_zero_iff.mp hzero
      change differenceMultiplicity S (x.2-x.1) ≤ 1
      omega
    apply card_le_one.mp hcard x _ y _
    · exact mem_filter.mpr ⟨(mem_filter.mp hx).1,rfl⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp hy).1,he.symm⟩
  · intro hinj
    apply sum_eq_zero
    intro d hd
    apply Nat.choose_eq_zero_iff.mpr
    have hcard : ((S ×ˢ S).filter (fun z ↦ z.2-z.1=d)).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      have hpos := positive_diff_of_mem_image S hd
      apply hinj
      · exact mem_filter.mpr ⟨(mem_filter.mp hx).1,by have := (mem_filter.mp hx).2; omega⟩
      · exact mem_filter.mpr ⟨(mem_filter.mp hy).1,by have := (mem_filter.mp hy).2; omega⟩
      · exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    change differenceMultiplicity S d ≤ 1 at hcard
    omega

/-- Prefix sums with the exact finite integer-valued term type from the problem. -/
def finitePrefix {k : ℕ} (a : Fin k → ℤ) (j : Fin (k+1)) : ℤ :=
  ∑ i : Fin k with i.val < j.val, a i

def prefixSet {k : ℕ} (a : Fin k → ℤ) : Finset ℤ := univ.image (finitePrefix a)

def indexInterval (k i j : ℕ) : Finset (Fin k) :=
  univ.filter (fun x ↦ i ≤ x.val ∧ x.val < j)

theorem finitePrefix_strictMono {k : ℕ} (a : Fin k → ℤ) (hp : ∀ i, 0 < a i) :
    StrictMono (finitePrefix a) := by
  intro i j hij
  have hv : i.val < j.val := hij
  have hik : i.val < k := by have := j.isLt; omega
  unfold finitePrefix
  apply sum_lt_sum_of_subset (i := (⟨i.val,hik⟩ : Fin k))
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    omega
  · simp only [mem_filter, mem_univ, true_and]; exact hv
  · simp
  · exact hp _
  · intro x hx hn; exact (hp x).le

theorem prefixSet_card {k : ℕ} (a : Fin k → ℤ) (hp : ∀ i, 0 < a i) :
    (prefixSet a).card = k+1 := by
  rw [prefixSet, card_image_of_injective _ (finitePrefix_strictMono a hp).injective]
  simp

theorem finitePrefix_sub {k : ℕ} (a : Fin k → ℤ) (i j : Fin (k+1)) (hij : i ≤ j) :
    finitePrefix a j-finitePrefix a i = ∑ x ∈ indexInterval k i.val j.val, a x := by
  unfold finitePrefix indexInterval
  simp only [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro x hx
  have hv : i.val ≤ j.val := hij
  split_ifs <;> omega

theorem indexInterval_connected (k i j : ℕ) :
    (indexInterval k i j : Set (Fin k)).OrdConnected := by
  constructor
  intro x hx y hy z hz
  simp only [mem_coe, indexInterval, mem_filter, mem_univ, true_and] at hx hy ⊢
  change x.val ≤ z.val ∧ z.val ≤ y.val at hz
  omega

theorem map_indexInterval (k i j : ℕ) (hj : j ≤ k) :
    (indexInterval k i j).map Fin.valEmbedding = Ico i j := by
  ext x
  simp only [mem_map, indexInterval, mem_filter, mem_univ, true_and, mem_Ico]
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx
    refine ⟨⟨x,by omega⟩,hx,rfl⟩

theorem indexInterval_injective (k : ℕ) {i j u v : ℕ}
    (hij : i < j) (huv : u < v) (hj : j ≤ k) (hv : v ≤ k)
    (he : indexInterval k i j = indexInterval k u v) : i=u ∧ j=v := by
  have hmap := congrArg (fun S : Finset (Fin k) ↦ S.map Fin.valEmbedding) he
  dsimp only at hmap
  rw [map_indexInterval k i j hj, map_indexInterval k u v hv] at hmap
  have h1 : i+(j-i)=j := by omega
  have h2 : u+(v-u)=v := by omega
  have hh : (i,j-i)=(u,v-u) := block_injective (by change 0 < j-i; omega) (by change 0 < v-u; omega) (by simpa [h1,h2] using hmap)
  have h := Prod.mk.inj hh
  omega

/-- Exact bridge from the finite integer predicate to uniqueness of positive prefix differences. -/
theorem hasDistinctSums_iff_prefix_differences {k : ℕ} (a : Fin k → ℤ)
    (hp : ∀ i, 0 < a i) : HasDistinctSums a ↔
      Set.InjOn (fun x : ℤ × ℤ ↦ x.2-x.1)
        (positivePairs (prefixSet a) : Set (ℤ × ℤ)) := by
  have hm := finitePrefix_strictMono a hp
  constructor
  · intro ha x hx y hy he
    obtain ⟨hxx,hxlt⟩ := mem_filter.mp hx
    obtain ⟨hxi,hxj⟩ := mem_product.mp hxx
    obtain ⟨hyy,hylt⟩ := mem_filter.mp hy
    obtain ⟨hyi,hyj⟩ := mem_product.mp hyy
    obtain ⟨i,_,hi⟩ := mem_image.mp hxi
    obtain ⟨j,_,hj⟩ := mem_image.mp hxj
    obtain ⟨u,_,hu⟩ := mem_image.mp hyi
    obtain ⟨v,_,hv⟩ := mem_image.mp hyj
    have hij : i < j := hm.lt_iff_lt.mp (by omega)
    have huv : u < v := hm.lt_iff_lt.mp (by omega)
    have he' : (∑ t ∈ indexInterval k i.val j.val, a t) =
        ∑ t ∈ indexInterval k u.val v.val, a t := by
      rw [← finitePrefix_sub a i j hij.le, ← finitePrefix_sub a u v huv.le]
      rw [hi,hj,hu,hv]
      exact he
    have hsets := ha (indexInterval_connected k i.val j.val)
      (indexInterval_connected k u.val v.val) he'
    obtain ⟨hiu,hjv⟩ := indexInterval_injective k hij huv
      (by have := j.isLt; omega) (by have := v.isLt; omega) hsets
    have hieq : i=u := Fin.ext hiu
    have hjeq : j=v := Fin.ext hjv
    apply Prod.ext <;> simp_all
  · intro hinj J hJ K hK he
    have hzero (S : Finset (Fin k)) : (∑ t ∈ S, a t)=0 ↔ S=∅ := by
      constructor
      · intro hz
        by_contra hn
        have hh : 0 < ∑ t ∈ S, a t :=
          sum_pos (fun t _ ↦ hp t) (nonempty_iff_ne_empty.mpr hn)
        omega
      · rintro rfl; simp
    by_cases hj : J=∅
    · subst J
      exact ((hzero K).mp (by simpa using he.symm)).symm
    by_cases hk : K=∅
    · subst K
      exact (hzero J).mp (by simpa using he)
    obtain ⟨i,l,hl,hil,hmapJ⟩ := fin_interval_encoding J hJ (nonempty_iff_ne_empty.mpr hj)
    obtain ⟨j,r,hr,hjr,hmapK⟩ := fin_interval_encoding K hK (nonempty_iff_ne_empty.mpr hk)
    have hJI : J=indexInterval k i (i+l) := by
      apply Finset.map_injective Fin.valEmbedding
      rw [hmapJ, map_indexInterval k i (i+l) hil]
    have hKI : K=indexInterval k j (j+r) := by
      apply Finset.map_injective Fin.valEmbedding
      rw [hmapK, map_indexInterval k j (j+r) hjr]
    let fi : Fin (k+1) := ⟨i,by omega⟩
    let fj : Fin (k+1) := ⟨i+l,by omega⟩
    let fu : Fin (k+1) := ⟨j,by omega⟩
    let fv : Fin (k+1) := ⟨j+r,by omega⟩
    have hifj : fi<fj := by change i < i+l; omega
    have hufv : fu<fv := by change j < j+r; omega
    have hmem (x y : Fin (k+1)) (hxy : x<y) :
        (finitePrefix a x,finitePrefix a y) ∈ positivePairs (prefixSet a) := by
      apply mem_filter.mpr
      exact ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_univ x),
        mem_image_of_mem _ (mem_univ y)⟩,hm hxy⟩
    have he' : finitePrefix a fj-finitePrefix a fi = finitePrefix a fv-finitePrefix a fu := by
      rw [finitePrefix_sub a fi fj hifj.le, finitePrefix_sub a fu fv hufv.le]
      change (∑ t ∈ indexInterval k i (i+l), a t) = ∑ t ∈ indexInterval k j (j+r), a t
      rw [← hJI,← hKI]
      exact he
    have hpairs := hinj (hmem fi fj hifj) (hmem fu fv hufv) he'
    have hpair := Prod.mk.inj hpairs
    have hstart : i=j := congrArg Fin.val (hm.injective hpair.1)
    have hend : i+l=j+r := congrArg Fin.val (hm.injective hpair.2)
    have hlen : l=r := by omega
    simp only [hJI,hKI,hstart,hlen]

/-- Exact energy identity for a finite positive integer sequence of length k. -/
theorem prefix_energy_excess {k : ℕ} (a : Fin k → ℤ) (hp : ∀ i, 0 < a i) :
    (prefixSet a).addEnergy (prefixSet a) =
      2*(k+1)^2-(k+1)+4*collisionCount (prefixSet a) := by
  rw [addEnergy_excess, prefixSet_card a hp]

/-- The upstream finite condition is exactly zero excess above the Sidon baseline. -/
theorem hasDistinctSums_iff_prefix_energy_minimal {k : ℕ} (a : Fin k → ℤ)
    (hp : ∀ i, 0 < a i) : HasDistinctSums a ↔
      (prefixSet a).addEnergy (prefixSet a) = 2*(k+1)^2-(k+1) := by
  rw [hasDistinctSums_iff_prefix_differences a hp, ← collisionCount_eq_zero_iff,
    prefix_energy_excess a hp]
  omega

/-- Any violation has at least four units of excess, with the exact integer hypotheses. -/
theorem prefix_energy_gap_of_not_distinct {k : ℕ} (a : Fin k → ℤ)
    (hp : ∀ i, 0 < a i) (hn : ¬ HasDistinctSums a) :
    2*(k+1)^2-(k+1)+4 ≤ (prefixSet a).addEnergy (prefixSet a) := by
  have he := prefix_energy_excess a hp
  have hh := (hasDistinctSums_iff_prefix_energy_minimal a hp).not.mp hn
  omega

/-- The natural supremum in upstream f is attained, including n=0. -/
theorem f_admissible (n : ℕ) : ∃ a : Fin (f n) → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a := by
  unfold f
  apply Nat.sSup_mem (s := {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a})
  · refine ⟨0, (fun _ ↦ 0), ?_, ?_, ?_⟩
    · rintro x ⟨i,hi⟩; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro J hJ K hK he; exact Subsingleton.elim _ _
  · refine ⟨n-n/2+Nat.sqrt n, ?_⟩
    rintro k ⟨a,hr,hm,ha⟩
    exact finite_int_length_le_half_add_sqrt a hr hm ha

/-- A reformulation of the OPEN conjecture, not a proof of either side. -/
theorem finite_conjecture_iff_energy_excess :
    Asymptotics.IsLittleO Filter.atTop (fun n : ℕ ↦ (f n : ℝ)) (fun n : ℕ ↦ (n : ℝ)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (k : ℕ) (a : Fin k → ℤ), Set.range a ⊆ Set.Icc 1 n → StrictMono a →
          ε*(n : ℝ) ≤ (k : ℝ) →
          2*(k+1)^2-(k+1) < (prefixSet a).addEnergy (prefixSet a) := by
  constructor
  · intro ho ε hε
    filter_upwards [ho.bound (show 0 < ε/2 by linarith),
      Filter.eventually_gt_atTop (0 : ℕ)] with n hb hn
    have hb' : (f n : ℝ) ≤ ε/2*(n : ℝ) := by simpa using hb
    intro k a hr hm hk
    have hp : ∀ i, 0 < a i := by
      intro i; have h := (hr ⟨i,rfl⟩).1; omega
    have hnd : ¬ HasDistinctSums a := by
      intro ha
      have hle : (k : ℝ) ≤ (f n : ℝ) := by exact_mod_cast admissible_length_le_f a hr hm ha
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      nlinarith
    have hg := prefix_energy_gap_of_not_distinct a hp hnd
    omega
  · intro he
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [he ε hε] with n hn
    obtain ⟨a,hr,hm,ha⟩ := f_admissible n
    have hp : ∀ i, 0 < a i := by
      intro i; have h := (hr ⟨i,rfl⟩).1; omega
    have hlt : (f n : ℝ) < ε*(n : ℝ) := by
      by_contra hh
      have hd := hn (f n) a hr hm (by linarith)
      have hz := (hasDistinctSums_iff_prefix_energy_minimal a hp).mp ha
      omega
    simpa using hlt.le


/-! Explicit collisions in APs and finite periodic patterns.
These are restricted-family bounds, not a proof of the open conjecture. -/

/-- Doubled AP sum with no truncated subtraction in the identity. -/
theorem ap_sum_twice (A d x s : ℕ) :
    2 * (∑ u ∈ range s, (A + d*(x+u))) + d*s =
      2*s*A + 2*d*s*x + d*s*s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ]
    nlinarith only [ih]

/-- The residue choice makes the quotient in the AP collision witness exact. -/
theorem ap_collision_divisible (d t c : ℕ) :
    2*d*t+1 ∣ 2*d*((t*c) % (2*d*t+1))+c := by
  have h := ((Nat.mod_modEq (t*c) (2*d*t+1)).mul_left (2*d)).add_right c
  have he : 2*d*(t*c)+c = (2*d*t+1)*c := by ring
  rw [he] at h
  exact (h.dvd_iff (dvd_refl _)).mpr (dvd_mul_right _ _)

/-- Explicit unequal-length AP blocks with equal sums and a finite endpoint bound. -/
theorem ap_collision (A d t : ℕ) (hd : 0 < d) :
    let r := 2*d*t+1
    let l := r+2*d
    let c := 2*A+d*(2*d-1)
    let i := (t*c) % r
    let j := i+2*d+(2*d*i+c)/r
    let K := 2*r+4*d-1+c/r
    0 < r ∧ r < l ∧ i+l ≤ K ∧ j+r ≤ K ∧
      (∑ u ∈ range l, (A+d*(i+u))) = (∑ u ∈ range r, (A+d*(j+u))) := by
  dsimp only
  let r := 2*d*t+1
  let c := 2*A+d*(2*d-1)
  let i := (t*c) % r
  let q := (2*d*i+c)/r
  have hr : 0 < r := by dsimp [r]; omega
  have hi : i < r := Nat.mod_lt _ hr
  have he : r*q = 2*d*i+c := Nat.mul_div_cancel' (ap_collision_divisible d t c)
  have hq : q ≤ 2*d+c/r := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    have hc := Nat.mod_add_div c r
    have hc' := Nat.mod_lt c hr
    nlinarith
  change 0 < r ∧ r < r+2*d ∧ i+(r+2*d) ≤ 2*r+4*d-1+c/r ∧
    i+2*d+q+r ≤ 2*r+4*d-1+c/r ∧
    (∑ u ∈ range (r+2*d), (A+d*(i+u))) =
      (∑ u ∈ range r, (A+d*(i+2*d+q+u)))
  have hk0 : 0 ≤ c/r := Nat.zero_le _
  refine ⟨hr, by omega, by omega, by omega, ?_⟩
  have h1 := ap_sum_twice A d i (r+2*d)
  have h2 := ap_sum_twice A d (i+2*d+q) r
  have hdm : 2*d-1+1 = 2*d := by omega
  have hc : c+d = 2*A+2*d*d := by
    dsimp [c]
    nlinarith only [congrArg (fun x => d*x) hdm]
  nlinarith only [h1, h2, congrArg (fun x => 2*d*x) hc,
    congrArg (fun x => 2*d*x) he]

/-- A rounded choice of the witness parameter gives a square-root cutoff. -/
theorem ap_cutoff_sqrt (d c : ℕ) (hd : 0 < d) :
    let r := 2*d*(Nat.sqrt c/(2*d)+1)+1
    2*r+4*d-1+c/r ≤ 3*Nat.sqrt c+8*d+1 := by
  dsimp only
  let s := Nat.sqrt c
  let r := 2*d*(s/(2*d)+1)+1
  have hd' : 0 < 2*d := by omega
  have hs := Nat.mod_add_div s (2*d)
  have hmod := Nat.mod_lt s hd'
  have hrlo : s < r := by dsimp [r]; nlinarith
  have hrhi : r ≤ s+2*d+1 := by
    dsimp [r]
    nlinarith only [hs, Nat.zero_le (s % (2*d))]
  have hr : 0 < r := by omega
  have hc : c/r ≤ s := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    have hsq := Nat.lt_succ_sqrt c
    change c < (s+1)*r
    change c < (s+1)*(s+1) at hsq
    nlinarith
  change 2*r+4*d-1+c/r ≤ 3*s+8*d+1
  omega

/-- Every positive-step AP has a collision within the displayed number of terms. -/
theorem ap_sqrt_collision (A d : ℕ) (hd : 0 < d) :
    ∃ i l j r : ℕ, 0 < r ∧ r < l ∧
      i+l ≤ 3*Nat.sqrt (2*A+d*(2*d-1))+8*d+1 ∧
      j+r ≤ 3*Nat.sqrt (2*A+d*(2*d-1))+8*d+1 ∧
      (∑ u ∈ range l, (A+d*(i+u))) = (∑ u ∈ range r, (A+d*(j+u))) := by
  let c := 2*A+d*(2*d-1)
  let t := Nat.sqrt c/(2*d)+1
  have h := ap_collision A d t hd
  have hk := ap_cutoff_sqrt d c hd
  refine ⟨(t*c)%(2*d*t+1), 2*d*t+1+2*d,
    (t*c)%(2*d*t+1)+2*d+(2*d*((t*c)%(2*d*t+1))+c)/(2*d*t+1),
    2*d*t+1, h.1, h.2.1, ?_, ?_, h.2.2.2.2⟩
  · exact le_trans h.2.2.1 hk
  · exact le_trans h.2.2.2.1 hk

/-- Finite natural-valued AP specialization of the full distinct-sums predicate. -/
theorem ap_not_hasDistinctSums (A d k : ℕ) (hd : 0 < d)
    (hk : 3*Nat.sqrt (2*A+d*(2*d-1))+8*d+1 ≤ k) :
    ¬ HasDistinctSums (fun i : Fin k ↦ A+d*i.val) := by
  intro ha
  obtain ⟨i,l,j,r,hr,hl,hi,hj,he⟩ := ap_sqrt_collision A d hd
  have h := block_inj_of_hasDistinctSums (fun i ↦ A+d*i) k ha
    (by omega : 0 < l) hr (hi.trans hk) (hj.trans hk) he
  omega

/-- Grouping consecutive terms preserves actual interval sums. -/
theorem sum_grouped_blocks (a : ℕ → ℕ) (p i l : ℕ) :
    (∑ u ∈ range (p*l), a (p*i+u)) =
      ∑ v ∈ range l, ∑ s ∈ range p, a (p*(i+v)+s) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    apply sum_congr rfl
    intro s hs
    congr 1
    ring

/-- One full period has an affine sum as a function of its index. -/
theorem periodic_block_sum (B p q t : ℕ) (R : ℕ → ℕ) (hp : 0 < p) :
    (∑ s ∈ range p, (B+q*((p*t+s)/p)+R ((p*t+s)%p))) =
      (p*B+∑ s ∈ range p, R s)+(p*q)*t := by
  have h : ∀ s ∈ range p, (p*t+s)/p = t ∧ (p*t+s)%p = s := by
    intro s hs
    have hs' : s < p := mem_range.mp hs
    constructor
    · rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hs', Nat.add_zero]
    · simp [Nat.mod_eq_of_lt hs']
  calc
    _ = ∑ s ∈ range p, (B+q*t+R s) := by
      apply sum_congr rfl
      intro s hs
      rw [(h s hs).1, (h s hs).2]
    _ = _ := by simp [sum_add_distrib]; ring

/-- A finite AP of group sums forces a collision; no hypothesis beyond k is used. -/
theorem grouped_ap_not_hasDistinctSums (a : ℕ → ℕ) (A d p k : ℕ)
    (hp : 0 < p) (hd : 0 < d)
    (hk : p*(3*Nat.sqrt (2*A+d*(2*d-1))+8*d+1) ≤ k)
    (hb : ∀ t, p*(t+1) ≤ k → (∑ s ∈ range p, a (p*t+s)) = A+d*t) :
    ¬ HasDistinctSums (fun i : Fin k ↦ a i.val) := by
  intro ha
  obtain ⟨i,l,j,r,hr,hl,hi,hj,he⟩ := ap_sqrt_collision A d hd
  have hi' : p*i+p*l ≤ k := by
    have := (Nat.mul_le_mul_left p hi).trans hk
    nlinarith only [this]
  have hj' : p*j+p*r ≤ k := by
    have := (Nat.mul_le_mul_left p hj).trans hk
    nlinarith only [this]
  have hs : ∀ x z, p*x+p*z ≤ k →
      (∑ u ∈ range (p*z), a (p*x+u)) = ∑ v ∈ range z, (A+d*(x+v)) := by
    intro x z hxz
    rw [sum_grouped_blocks]
    apply sum_congr rfl
    intro v hv
    apply hb
    have hv' : v+1 ≤ z := mem_range.mp hv
    have hvp := Nat.mul_le_mul_left p hv'
    nlinarith only [hvp, hxz]
  have he' : (∑ u ∈ range (p*l), a (p*i+u)) =
      ∑ u ∈ range (p*r), a (p*j+u) := by
    rw [hs i l hi', hs j r hj', he]
  have h := block_inj_of_hasDistinctSums a k ha
    (Nat.mul_pos hp (by omega : 0 < l)) (Nat.mul_pos hp hr) hi' hj' he'
  have hlt := Nat.mul_lt_mul_of_pos_left hl hp
  omega

/-- Explicit finite collision cutoff for an arbitrary natural-valued periodic pattern. -/
theorem periodic_not_hasDistinctSums (B p q k : ℕ) (R : ℕ → ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hk : p*(3*Nat.sqrt (2*(p*B+∑ s ∈ range p, R s)+(p*q)*(2*(p*q)-1))+
      8*(p*q)+1) ≤ k) :
    ¬ HasDistinctSums (fun i : Fin k ↦ B+q*(i.val/p)+R (i.val%p)) := by
  apply grouped_ap_not_hasDistinctSums (fun i ↦ B+q*(i/p)+R (i%p))
    (p*B+∑ s ∈ range p, R s) (p*q) p k hp (Nat.mul_pos hp hq) hk
  intro t ht
  exact periodic_block_sum B p q t R hp

/-- The literal distinct-sums predicate is preserved by the natural-to-integer embedding. -/
theorem hasDistinctSums_natCast_iff {ι : Type*} [Preorder ι] (a : ι → ℕ) :
    HasDistinctSums (fun i ↦ (a i : ℤ)) ↔ HasDistinctSums a := by
  constructor
  · intro h J hJ K hK he
    apply h hJ hK
    dsimp only at he ⊢
    exact_mod_cast he
  · intro h J hJ K hK he
    apply h hJ hK
    dsimp only at he ⊢
    exact_mod_cast he

/-- Periodic collision cutoff for the integer-valued predicate used by f. -/
theorem periodic_int_not_hasDistinctSums (B p q k : ℕ) (R : ℕ → ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hk : p*(3*Nat.sqrt (2*(p*B+∑ s ∈ range p, R s)+(p*q)*(2*(p*q)-1))+
      8*(p*q)+1) ≤ k) :
    ¬ HasDistinctSums (fun i : Fin k ↦ ((B+q*(i.val/p)+R (i.val%p) : ℕ) : ℤ)) := by
  intro ha
  apply periodic_not_hasDistinctSums B p q k R hp hq hk
  exact (hasDistinctSums_natCast_iff _).mp ha

/-- A bound in terms of the maximum entry for finite affine group sums. -/
theorem grouped_ap_length_bound (a : ℕ → ℕ) (A d p k n : ℕ)
    (hp : 0 < p) (hd : 0 < d)
    (ha : HasDistinctSums (fun i : Fin k ↦ a i.val))
    (hn : ∀ i < k, a i ≤ n)
    (hb : ∀ t, p*(t+1) ≤ k → (∑ s ∈ range p, a (p*t+s)) = A+d*t) :
    k < p*(3*Nat.sqrt (2*(p*n)+d*(2*d-1))+8*d+1) := by
  by_contra h
  have hk : p*(3*Nat.sqrt (2*(p*n)+d*(2*d-1))+8*d+1) ≤ k := by omega
  have hp' : p ≤ k := by
    have h1 : 1 ≤ 3*Nat.sqrt (2*(p*n)+d*(2*d-1))+8*d+1 := by omega
    have h2 := (Nat.mul_le_mul_left p h1).trans hk
    simpa using h2
  have hs : (∑ s ∈ range p, a s) ≤ p*n := by
    calc
      _ ≤ ∑ s ∈ range p, n := by
        apply sum_le_sum
        intro s hs
        exact hn s ((mem_range.mp hs).trans_le hp')
      _ = _ := by simp
  have hA : A ≤ p*n := by
    have h0 := hb 0 (by simpa using hp')
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h0
    exact h0.symm.trans_le hs
  have hsqrt := Nat.sqrt_le_sqrt (show 2*A+d*(2*d-1) ≤
    2*(p*n)+d*(2*d-1) by omega)
  have hbnd : 3*Nat.sqrt (2*A+d*(2*d-1))+8*d+1 ≤
      3*Nat.sqrt (2*(p*n)+d*(2*d-1))+8*d+1 := by omega
  exact grouped_ap_not_hasDistinctSums a A d p k hp hd
    ((Nat.mul_le_mul_left p hbnd).trans hk) hb ha

/-- Fixed p and q force square-root growth, uniformly over offsets and residue values. -/
theorem periodic_int_length_bound (B p q k n : ℕ) (R : ℕ → ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (ha : HasDistinctSums (fun i : Fin k ↦ ((B+q*(i.val/p)+R (i.val%p) : ℕ) : ℤ)))
    (hn : ∀ i < k, B+q*(i/p)+R (i%p) ≤ n) :
    k < p*(3*Nat.sqrt (2*p*n+(p*q)*(2*(p*q)-1))+8*(p*q)+1) := by
  have h := grouped_ap_length_bound (fun i ↦ B+q*(i/p)+R (i%p))
    (p*B+∑ s ∈ range p, R s) (p*q) p k n hp (Nat.mul_pos hp hq)
    ((hasDistinctSums_natCast_iff _).mp ha) hn
    (fun t _ ↦ periodic_block_sum B p q t R hp)
  simpa [Nat.mul_assoc] using h


/- BEGIN GENERATED JITTER42 CERTIFICATE -/
/- Generated by problems/0357/export_jitter.py via erdos.witness.
A finite lower bound only; the unrestricted conjecture is open. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def jitter42 : Fin 42 → ℤ := ![121, 123, 126, 130, 132, 135, 139, 142, 144, 147, 150, 154, 157, 160, 162, 166, 169, 172, 174, 178, 180, 183, 186, 189, 193, 196, 199, 202, 205, 207, 210, 213, 217, 220, 222, 226, 229, 231, 234, 238, 240, 243]

theorem jitter42_bounds : ∀ i, 1 ≤ jitter42 i ∧ jitter42 i ≤ 243 := by decide +kernel

theorem jitter42_mono : StrictMono jitter42 := by decide +kernel

theorem jitter42_prefix_values : finitePrefix jitter42 = (![0, 121, 244, 370, 500, 632, 767, 906, 1048, 1192, 1339, 1489, 1643, 1800, 1960, 2122, 2288, 2457, 2629, 2803, 2981, 3161, 3344, 3530, 3719, 3912, 4108, 4307, 4509, 4714, 4921, 5131, 5344, 5561, 5781, 6003, 6229, 6458, 6689, 6923, 7161, 7401, 7644] : Fin 43 → ℤ) := by ext i; fin_cases i <;> decide +kernel

theorem jitter42_prefixSet : prefixSet jitter42 = {0, 121, 244, 370, 500, 632, 767, 906, 1048, 1192, 1339, 1489, 1643, 1800, 1960, 2122, 2288, 2457, 2629, 2803, 2981, 3161, 3344, 3530, 3719, 3912, 4108, 4307, 4509, 4714, 4921, 5131, 5344, 5561, 5781, 6003, 6229, 6458, 6689, 6923, 7161, 7401, 7644} := by unfold prefixSet; rw [jitter42_prefix_values]; decide +kernel

def jitter42_decode (n : ℤ) : ℤ × ℤ := (if n < 2338 then (if n < 1098 then (if n < 572 then (if n < 328 then (if n < 205 then (if n < 162 then (if n < 142 then (if n < 130 then (if n < 123 then (0, 121) else (if n < 126 then (121, 244) else (244, 370))) else (if n < 135 then (if n < 132 then (370, 500) else (500, 632)) else (if n < 139 then (632, 767) else (767, 906)))) else (if n < 150 then (if n < 144 then (906, 1048) else (if n < 147 then (1048, 1192) else (1192, 1339))) else (if n < 157 then (if n < 154 then (1339, 1489) else (1489, 1643)) else (if n < 160 then (1643, 1800) else (1800, 1960))))) else (if n < 183 then (if n < 172 then (if n < 166 then (1960, 2122) else (if n < 169 then (2122, 2288) else (2288, 2457))) else (if n < 178 then (if n < 174 then (2457, 2629) else (2629, 2803)) else (if n < 180 then (2803, 2981) else (2981, 3161)))) else (if n < 193 then (if n < 186 then (3161, 3344) else (if n < 189 then (3344, 3530) else (3530, 3719))) else (if n < 199 then (if n < 196 then (3719, 3912) else (3912, 4108)) else (if n < 202 then (4108, 4307) else (4307, 4509)))))) else (if n < 244 then (if n < 226 then (if n < 213 then (if n < 207 then (4509, 4714) else (if n < 210 then (4714, 4921) else (4921, 5131))) else (if n < 220 then (if n < 217 then (5131, 5344) else (5344, 5561)) else (if n < 222 then (5561, 5781) else (5781, 6003)))) else (if n < 234 then (if n < 229 then (6003, 6229) else (if n < 231 then (6229, 6458) else (6458, 6689))) else (if n < 240 then (if n < 238 then (6689, 6923) else (6923, 7161)) else (if n < 243 then (7161, 7401) else (7401, 7644))))) else (if n < 286 then (if n < 262 then (if n < 249 then (0, 244) else (if n < 256 then (121, 370) else (244, 500))) else (if n < 274 then (if n < 267 then (370, 632) else (500, 767)) else (if n < 281 then (632, 906) else (767, 1048)))) else (if n < 304 then (if n < 291 then (906, 1192) else (if n < 297 then (1048, 1339) else (1192, 1489))) else (if n < 317 then (if n < 311 then (1339, 1643) else (1489, 1800)) else (if n < 322 then (1643, 1960) else (1800, 2122))))))) else (if n < 442 then (if n < 395 then (if n < 369 then (if n < 346 then (if n < 335 then (1960, 2288) else (if n < 341 then (2122, 2457) else (2288, 2629))) else (if n < 358 then (if n < 352 then (2457, 2803) else (2629, 2981)) else (if n < 363 then (2803, 3161) else (2981, 3344)))) else (if n < 379 then (if n < 370 then (3161, 3530) else (if n < 375 then (0, 370) else (3344, 3719))) else (if n < 388 then (if n < 382 then (121, 500) else (3530, 3912)) else (if n < 389 then (244, 632) else (3719, 4108))))) else (if n < 417 then (if n < 406 then (if n < 397 then (3912, 4307) else (if n < 401 then (370, 767) else (4108, 4509))) else (if n < 412 then (if n < 407 then (500, 906) else (4307, 4714)) else (if n < 416 then (4509, 4921) else (632, 1048)))) else (if n < 430 then (if n < 423 then (4714, 5131) else (if n < 425 then (4921, 5344) else (767, 1192))) else (if n < 437 then (if n < 433 then (5131, 5561) else (906, 1339)) else (if n < 441 then (5344, 5781) else (1048, 1489)))))) else (if n < 500 then (if n < 471 then (if n < 455 then (if n < 448 then (5561, 6003) else (if n < 451 then (5781, 6229) else (1192, 1643))) else (if n < 461 then (if n < 460 then (6003, 6458) else (6229, 6689)) else (if n < 465 then (1339, 1800) else (6458, 6923)))) else (if n < 479 then (if n < 472 then (1489, 1960) else (if n < 478 then (6689, 7161) else (6923, 7401))) else (if n < 488 then (if n < 483 then (1643, 2122) else (7161, 7644)) else (if n < 497 then (1800, 2288) else (1960, 2457))))) else (if n < 536 then (if n < 515 then (if n < 507 then (0, 500) else (if n < 511 then (2122, 2629) else (121, 632))) else (if n < 524 then (if n < 523 then (2288, 2803) else (244, 767)) else (if n < 532 then (2457, 2981) else (2629, 3161)))) else (if n < 549 then (if n < 541 then (370, 906) else (if n < 548 then (2803, 3344) else (500, 1048))) else (if n < 560 then (if n < 558 then (2981, 3530) else (3161, 3719)) else (if n < 568 then (632, 1192) else (3344, 3912)))))))) else (if n < 829 then (if n < 693 then (if n < 640 then (if n < 608 then (if n < 588 then (if n < 578 then (767, 1339) else (if n < 583 then (3530, 4108) else (906, 1489))) else (if n < 597 then (if n < 595 then (3719, 4307) else (1048, 1643)) else (if n < 606 then (3912, 4509) else (4108, 4714)))) else (if n < 622 then (if n < 614 then (1192, 1800) else (if n < 621 then (4307, 4921) else (1339, 1960))) else (if n < 632 then (if n < 630 then (4509, 5131) else (4714, 5344)) else (if n < 633 then (0, 632) else (1489, 2122))))) else (if n < 668 then (if n < 650 then (if n < 645 then (4921, 5561) else (if n < 646 then (1643, 2288) else (121, 767))) else (if n < 659 then (if n < 657 then (5131, 5781) else (1800, 2457)) else (if n < 662 then (5344, 6003) else (244, 906)))) else (if n < 678 then (if n < 669 then (5561, 6229) else (if n < 677 then (1960, 2629) else (5781, 6458))) else (if n < 686 then (if n < 681 then (370, 1048) else (2122, 2803)) else (if n < 692 then (6003, 6689) else (500, 1192)))))) else (if n < 764 then (if n < 721 then (if n < 704 then (if n < 694 then (2288, 2981) else (if n < 703 then (6229, 6923) else (6458, 7161))) else (if n < 712 then (if n < 707 then (2457, 3161) else (632, 1339)) else (if n < 715 then (6689, 7401) else (2629, 3344)))) else (if n < 737 then (if n < 722 then (6923, 7644) else (if n < 727 then (767, 1489) else (2803, 3530))) else (if n < 751 then (if n < 738 then (906, 1643) else (2981, 3719)) else (if n < 752 then (3161, 3912) else (1048, 1800))))) else (if n < 799 then (if n < 777 then (if n < 767 then (3344, 4108) else (if n < 768 then (0, 767) else (1192, 1960))) else (if n < 785 then (if n < 783 then (3530, 4307) else (1339, 2122)) else (if n < 790 then (121, 906) else (3719, 4509)))) else (if n < 813 then (if n < 802 then (1489, 2288) else (if n < 804 then (3912, 4714) else (244, 1048))) else (if n < 822 then (if n < 814 then (4108, 4921) else (1643, 2457)) else (if n < 824 then (370, 1192) else (4307, 5131))))))) else (if n < 949 then (if n < 897 then (if n < 860 then (if n < 843 then (if n < 835 then (1800, 2629) else (if n < 839 then (4509, 5344) else (500, 1339))) else (if n < 857 then (if n < 847 then (1960, 2803) else (4714, 5561)) else (if n < 859 then (632, 1489) else (2122, 2981)))) else (if n < 876 then (if n < 872 then (4921, 5781) else (if n < 873 then (5131, 6003) else (2288, 3161))) else (if n < 887 then (if n < 885 then (767, 1643) else (5344, 6229)) else (if n < 894 then (2457, 3344) else (906, 1800))))) else (if n < 927 then (if n < 908 then (if n < 901 then (5561, 6458) else (if n < 906 then (2629, 3530) else (0, 906))) else (if n < 916 then (if n < 912 then (5781, 6689) else (1048, 1960)) else (if n < 920 then (2803, 3719) else (6003, 6923)))) else (if n < 932 then (if n < 930 then (121, 1048) else (if n < 931 then (1192, 2122) else (2981, 3912))) else (if n < 947 then (if n < 943 then (6229, 7161) else (6458, 7401)) else (if n < 948 then (3161, 4108) else (244, 1192)))))) else (if n < 1033 then (if n < 989 then (if n < 968 then (if n < 955 then (1339, 2288) else (if n < 963 then (6689, 7644) else (3344, 4307))) else (if n < 979 then (if n < 969 then (1489, 2457) else (370, 1339)) else (if n < 986 then (3530, 4509) else (1643, 2629)))) else (if n < 1009 then (if n < 995 then (500, 1489) else (if n < 1003 then (3719, 4714) else (1800, 2803))) else (if n < 1021 then (if n < 1011 then (3912, 4921) else (632, 1643)) else (if n < 1023 then (1960, 2981) else (4108, 5131))))) else (if n < 1067 then (if n < 1048 then (if n < 1037 then (767, 1800) else (if n < 1039 then (4307, 5344) else (2122, 3161))) else (if n < 1054 then (if n < 1052 then (0, 1048) else (4509, 5561)) else (if n < 1056 then (906, 1960) else (2288, 3344)))) else (if n < 1082 then (if n < 1073 then (if n < 1071 then (4714, 5781) else (121, 1192)) else (if n < 1074 then (2457, 3530) else (1048, 2122))) else (if n < 1095 then (if n < 1090 then (4921, 6003) else (2629, 3719)) else (if n < 1096 then (244, 1339) else (1192, 2288))))))))) else (if n < 1679 then (if n < 1382 then (if n < 1240 then (if n < 1168 then (if n < 1140 then (if n < 1118 then (if n < 1109 then (5131, 6229) else (if n < 1114 then (2803, 3912) else (5344, 6458))) else (if n < 1127 then (if n < 1119 then (1339, 2457) else (370, 1489)) else (if n < 1128 then (2981, 4108) else (5561, 6689)))) else (if n < 1146 then (if n < 1142 then (1489, 2629) else (if n < 1143 then (5781, 6923) else (500, 1643))) else (if n < 1160 then (if n < 1158 then (3161, 4307) else (6003, 7161)) else (if n < 1165 then (1643, 2803) else (3344, 4509))))) else (if n < 1201 then (if n < 1184 then (if n < 1172 then (632, 1800) else (if n < 1181 then (6229, 7401) else (1800, 2981))) else (if n < 1192 then (if n < 1186 then (3530, 4714) else (6458, 7644)) else (if n < 1193 then (0, 1192) else (767, 1960)))) else (if n < 1218 then (if n < 1202 then (1960, 3161) else (if n < 1216 then (3719, 4921) else (906, 2122))) else (if n < 1222 then (if n < 1219 then (121, 1339) else (3912, 5131)) else (if n < 1236 then (2122, 3344) else (4108, 5344)))))) else (if n < 1314 then (if n < 1273 then (if n < 1254 then (if n < 1242 then (1048, 2288) else (if n < 1245 then (2288, 3530) else (244, 1489))) else (if n < 1265 then (if n < 1262 then (4307, 5561) else (2457, 3719)) else (if n < 1272 then (1192, 2457) else (4509, 5781)))) else (if n < 1290 then (if n < 1283 then (370, 1643) else (if n < 1289 then (2629, 3912) else (4714, 6003))) else (if n < 1305 then (if n < 1300 then (1339, 2629) else (500, 1800)) else (if n < 1308 then (2803, 4108) else (4921, 6229))))) else (if n < 1348 then (if n < 1328 then (if n < 1326 then (1489, 2803) else (if n < 1327 then (2981, 4307) else (5131, 6458))) else (if n < 1339 then (if n < 1338 then (632, 1960) else (1643, 2981)) else (if n < 1345 then (0, 1339) else (5344, 6689)))) else (if n < 1362 then (if n < 1355 then (3161, 4509) else (if n < 1361 then (767, 2122) else (1800, 3161))) else (if n < 1370 then (if n < 1368 then (5561, 6923) else (121, 1489)) else (if n < 1380 then (3344, 4714) else (5781, 7161))))))) else (if n < 1528 then (if n < 1455 then (if n < 1412 then (if n < 1398 then (if n < 1384 then (906, 2288) else (if n < 1391 then (1960, 3344) else (3530, 4921))) else (if n < 1408 then (if n < 1399 then (6003, 7401) else (244, 1643)) else (if n < 1409 then (2122, 3530) else (1048, 2457)))) else (if n < 1431 then (if n < 1415 then (3719, 5131) else (if n < 1430 then (6229, 7644) else (370, 1800))) else (if n < 1437 then (if n < 1432 then (2288, 3719) else (3912, 5344)) else (if n < 1453 then (1192, 2629) else (4108, 5561))))) else (if n < 1492 then (if n < 1474 then (if n < 1460 then (2457, 3912) else (if n < 1464 then (500, 1960) else (1339, 2803))) else (if n < 1489 then (if n < 1479 then (4307, 5781) else (2629, 4108)) else (if n < 1490 then (0, 1489) else (632, 2122)))) else (if n < 1515 then (if n < 1494 then (1489, 2981) else (if n < 1504 then (4509, 6003) else (2803, 4307))) else (if n < 1521 then (if n < 1518 then (4714, 6229) else (1643, 3161)) else (if n < 1522 then (767, 2288) else (121, 1643)))))) else (if n < 1601 then (if n < 1570 then (if n < 1551 then (if n < 1537 then (2981, 4509) else (if n < 1544 then (4921, 6458) else (1800, 3344))) else (if n < 1556 then (if n < 1553 then (906, 2457) else (3161, 4714)) else (if n < 1558 then (244, 1800) else (5131, 6689)))) else (if n < 1581 then (if n < 1577 then (1960, 3530) else (if n < 1579 then (3344, 4921) else (5344, 6923))) else (if n < 1597 then (if n < 1590 then (1048, 2629) else (370, 1960)) else (if n < 1600 then (2122, 3719) else (5561, 7161))))) else (if n < 1642 then (if n < 1622 then (if n < 1611 then (3530, 5131) else (if n < 1620 then (1192, 2803) else (5781, 7401))) else (if n < 1625 then (if n < 1624 then (500, 2122) else (2288, 3912)) else (if n < 1641 then (3719, 5344) else (6003, 7644)))) else (if n < 1656 then (if n < 1649 then (if n < 1643 then (1339, 2981) else (0, 1643)) else (if n < 1651 then (3912, 5561) else (2457, 4108))) else (if n < 1673 then (if n < 1672 then (632, 2288) else (1489, 3161)) else (if n < 1678 then (4108, 5781) else (2629, 4307)))))))) else (if n < 2001 then (if n < 1840 then (if n < 1760 then (if n < 1723 then (if n < 1701 then (if n < 1690 then (121, 1800) else (if n < 1696 then (767, 2457) else (4307, 6003))) else (if n < 1716 then (if n < 1706 then (1643, 3344) else (2803, 4509)) else (if n < 1720 then (244, 1960) else (4509, 6229)))) else (if n < 1744 then (if n < 1730 then (906, 2629) else (if n < 1733 then (1800, 3530) else (2981, 4714))) else (if n < 1755 then (if n < 1752 then (4714, 6458) else (370, 2122)) else (if n < 1759 then (1048, 2803) else (1960, 3719))))) else (if n < 1800 then (if n < 1788 then (if n < 1768 then (3161, 4921) else (if n < 1787 then (4921, 6689) else (3344, 5131))) else (if n < 1790 then (if n < 1789 then (500, 2288) else (1192, 2981)) else (if n < 1792 then (2122, 3912) else (5131, 6923)))) else (if n < 1820 then (if n < 1814 then (0, 1800) else (if n < 1817 then (3530, 5344) else (5344, 7161))) else (if n < 1825 then (if n < 1822 then (2288, 4108) else (1339, 3161)) else (if n < 1839 then (632, 2457) else (121, 1960)))))) else (if n < 1919 then (if n < 1878 then (if n < 1855 then (if n < 1842 then (5561, 7401) else (if n < 1850 then (3719, 5561) else (2457, 4307))) else (if n < 1863 then (if n < 1862 then (1489, 3344) else (767, 2629)) else (if n < 1869 then (5781, 7644) else (3912, 5781)))) else (if n < 1895 then (if n < 1880 then (244, 2122) else (if n < 1887 then (2629, 4509) else (1643, 3530))) else (if n < 1911 then (if n < 1897 then (4108, 6003) else (906, 2803)) else (if n < 1918 then (2803, 4714) else (370, 2288))))) else (if n < 1960 then (if n < 1940 then (if n < 1922 then (1800, 3719) else (if n < 1933 then (4307, 6229) else (1048, 2981))) else (if n < 1952 then (if n < 1949 then (2981, 4921) else (4509, 6458)) else (if n < 1957 then (1960, 3912) else (500, 2457)))) else (if n < 1975 then (if n < 1969 then (0, 1960) else (if n < 1970 then (1192, 3161) else (3161, 5131))) else (if n < 1997 then (if n < 1986 then (4714, 6689) else (2122, 4108)) else (if n < 2000 then (632, 2629) else (3344, 5344))))))) else (if n < 2167 then (if n < 2083 then (if n < 2041 then (if n < 2019 then (if n < 2002 then (121, 2122) else (if n < 2005 then (4921, 6923) else (1339, 3344))) else (if n < 2031 then (if n < 2030 then (2288, 4307) else (5131, 7161)) else (if n < 2036 then (3530, 5561) else (767, 2803)))) else (if n < 2057 then (if n < 2044 then (1489, 3530) else (if n < 2052 then (244, 2288) else (2457, 4509))) else (if n < 2075 then (if n < 2062 then (5344, 7401) else (3719, 5781)) else (if n < 2076 then (906, 2981) else (1643, 3719))))) else (if n < 2121 then (if n < 2091 then (if n < 2085 then (5561, 7644) else (if n < 2087 then (2629, 4714) else (370, 2457))) else (if n < 2113 then (if n < 2112 then (3912, 6003) else (1800, 3912)) else (if n < 2118 then (1048, 3161) else (2803, 4921)))) else (if n < 2148 then (if n < 2122 then (4108, 6229) else (if n < 2129 then (0, 2122) else (500, 2629))) else (if n < 2151 then (if n < 2150 then (1960, 4108) else (2981, 5131)) else (if n < 2152 then (4307, 6458) else (1192, 3344)))))) else (if n < 2255 then (if n < 2213 then (if n < 2183 then (if n < 2171 then (121, 2288) else (if n < 2180 then (632, 2803) else (4509, 6689))) else (if n < 2191 then (if n < 2185 then (3161, 5344) else (2122, 4307)) else (if n < 2209 then (1339, 3530) else (4714, 6923)))) else (if n < 2221 then (if n < 2214 then (244, 2457) else (if n < 2217 then (767, 2981) else (3344, 5561))) else (if n < 2240 then (if n < 2230 then (2288, 4509) else (1489, 3719)) else (if n < 2251 then (4921, 7161) else (3530, 5781))))) else (if n < 2292 then (if n < 2269 then (if n < 2257 then (906, 3161) else (if n < 2259 then (2457, 4714) else (370, 2629))) else (if n < 2284 then (if n < 2270 then (1643, 3912) else (5131, 7401)) else (if n < 2288 then (3719, 6003) else (0, 2288)))) else (if n < 2308 then (if n < 2300 then (if n < 2296 then (2629, 4921) else (1048, 3344)) else (if n < 2303 then (5344, 7644) else (500, 2803))) else (if n < 2328 then (if n < 2317 then (1800, 4108) else (3912, 6229)) else (if n < 2336 then (2803, 5131) else (121, 2457)))))))))) else (if n < 3987 then (if n < 3094 then (if n < 2699 then (if n < 2510 then (if n < 2433 then (if n < 2385 then (if n < 2350 then (if n < 2347 then (1192, 3530) else (if n < 2349 then (1960, 4307) else (632, 2981))) else (if n < 2380 then (if n < 2363 then (4108, 6458) else (2981, 5344)) else (if n < 2382 then (1339, 3719) else (4307, 6689)))) else (if n < 2400 then (if n < 2387 then (244, 2629) else (if n < 2394 then (2122, 4509) else (767, 3161))) else (if n < 2423 then (if n < 2414 then (3161, 5561) else (4509, 6923)) else (if n < 2426 then (1489, 3912) else (2288, 4714))))) else (if n < 2473 then (if n < 2447 then (if n < 2437 then (370, 2803) else (if n < 2438 then (3344, 5781) else (906, 3344))) else (if n < 2464 then (if n < 2457 then (4714, 7161) else (0, 2457)) else (if n < 2465 then (2457, 4921) else (1643, 4108)))) else (if n < 2482 then (if n < 2480 then (3530, 6003) else (if n < 2481 then (4921, 7401) else (500, 2981))) else (if n < 2507 then (if n < 2502 then (1048, 3530) else (2629, 5131)) else (if n < 2508 then (1800, 4307) else (121, 2629)))))) else (if n < 2616 then (if n < 2559 then (if n < 2529 then (if n < 2513 then (3719, 6229) else (if n < 2527 then (5131, 7644) else (1192, 3719))) else (if n < 2546 then (if n < 2541 then (632, 3161) else (2803, 5344)) else (if n < 2549 then (3912, 6458) else (1960, 4509)))) else (if n < 2580 then (if n < 2573 then (244, 2803) else (if n < 2577 then (1339, 3912) else (767, 3344))) else (if n < 2592 then (if n < 2581 then (2981, 5561) else (4108, 6689)) else (if n < 2611 then (2122, 4714) else (370, 2981))))) else (if n < 2659 then (if n < 2624 then (if n < 2619 then (4307, 6923) else (if n < 2620 then (1489, 4108) else (3161, 5781))) else (if n < 2633 then (if n < 2629 then (906, 3530) else (0, 2629)) else (if n < 2652 then (2288, 4921) else (4509, 7161)))) else (if n < 2671 then (if n < 2661 then (3344, 6003) else (if n < 2664 then (500, 3161) else (1643, 4307))) else (if n < 2682 then (if n < 2674 then (1048, 3719) else (2457, 5131)) else (if n < 2687 then (121, 2803) else (4714, 7401))))))) else (if n < 2887 then (if n < 2799 then (if n < 2739 then (if n < 2715 then (if n < 2709 then (3530, 6229) else (if n < 2712 then (1800, 4509) else (632, 3344))) else (if n < 2723 then (if n < 2720 then (2629, 5344) else (1192, 3912)) else (if n < 2737 then (4921, 7644) else (244, 2981)))) else (if n < 2763 then (if n < 2754 then (3719, 6458) else (if n < 2758 then (1960, 4714) else (2803, 5561))) else (if n < 2777 then (if n < 2769 then (767, 3530) else (1339, 4108)) else (if n < 2791 then (3912, 6689) else (370, 3161))))) else (if n < 2843 then (if n < 2813 then (if n < 2800 then (2122, 4921) else (if n < 2803 then (2981, 5781) else (0, 2803))) else (if n < 2818 then (if n < 2815 then (906, 3719) else (4108, 6923)) else (if n < 2842 then (1489, 4307) else (3161, 6003)))) else (if n < 2860 then (if n < 2844 then (2288, 5131) else (if n < 2854 then (500, 3344) else (4307, 7161))) else (if n < 2866 then (if n < 2864 then (121, 2981) else (1048, 3912)) else (if n < 2885 then (1643, 4509) else (3344, 6229)))))) else (if n < 2978 then (if n < 2930 then (if n < 2914 then (if n < 2892 then (2457, 5344) else (if n < 2898 then (4509, 7401) else (632, 3530))) else (if n < 2917 then (if n < 2916 then (1800, 4714) else (1192, 4108)) else (if n < 2928 then (244, 3161) else (3530, 6458)))) else (if n < 2961 then (if n < 2932 then (4714, 7644) else (if n < 2952 then (2629, 5561) else (767, 3719))) else (if n < 2970 then (if n < 2968 then (1960, 4921) else (1339, 4307)) else (if n < 2974 then (3719, 6689) else (370, 3344))))) else (if n < 3030 then (if n < 3009 then (if n < 2981 then (2803, 5781) else (if n < 3006 then (0, 2981) else (906, 3912))) else (if n < 3020 then (if n < 3011 then (2122, 5131) else (3912, 6923)) else (if n < 3022 then (1489, 4509) else (2981, 6003)))) else (if n < 3060 then (if n < 3053 then (if n < 3040 then (500, 3530) else (121, 3161)) else (if n < 3056 then (4108, 7161) else (2288, 5344))) else (if n < 3071 then (if n < 3068 then (1048, 4108) else (3161, 6229)) else (if n < 3087 then (1643, 4714) else (632, 3719)))))))) else (if n < 3522 then (if n < 3293 then (if n < 3200 then (if n < 3145 then (if n < 3114 then (if n < 3100 then (4307, 7401) else (if n < 3104 then (244, 3344) else (2457, 5561))) else (if n < 3121 then (if n < 3115 then (3344, 6458) else (1192, 4307)) else (if n < 3135 then (1800, 4921) else (4509, 7644)))) else (if n < 3160 then (if n < 3152 then (767, 3912) else (if n < 3159 then (2629, 5781) else (3530, 6689))) else (if n < 3170 then (if n < 3161 then (370, 3530) else (0, 3161)) else (if n < 3171 then (1339, 4509) else (1960, 5131))))) else (if n < 3248 then (if n < 3219 then (if n < 3202 then (2803, 6003) else (if n < 3204 then (906, 4108) else (3719, 6923))) else (if n < 3223 then (if n < 3222 then (500, 3719) else (2122, 5344)) else (if n < 3225 then (121, 3344) else (1489, 4714)))) else (if n < 3273 then (if n < 3249 then (2981, 6229) else (if n < 3259 then (3912, 7161) else (1048, 4307))) else (if n < 3280 then (if n < 3278 then (2288, 5561) else (1643, 4921)) else (if n < 3286 then (632, 3912) else (244, 3530)))))) else (if n < 3401 then (if n < 3344 then (if n < 3324 then (if n < 3297 then (4108, 7401) else (if n < 3317 then (3161, 6458) else (1192, 4509))) else (if n < 3337 then (if n < 3331 then (2457, 5781) else (1800, 5131)) else (if n < 3341 then (4307, 7644) else (767, 4108)))) else (if n < 3374 then (if n < 3345 then (0, 3344) else (if n < 3349 then (3344, 6689) else (370, 3719))) else (if n < 3384 then (if n < 3375 then (2629, 6003) else (1339, 4714)) else (if n < 3393 then (1960, 5344) else (3530, 6923))))) else (if n < 3461 then (if n < 3426 then (if n < 3409 then (906, 4307) else (if n < 3412 then (121, 3530) else (500, 3912))) else (if n < 3439 then (if n < 3432 then (2803, 6229) else (1489, 4921)) else (if n < 3442 then (2122, 5561) else (3719, 7161)))) else (if n < 3477 then (if n < 3475 then (1048, 4509) else (if n < 3476 then (244, 3719) else (632, 4108))) else (if n < 3489 then (if n < 3488 then (2981, 6458) else (1643, 5131)) else (if n < 3493 then (3912, 7401) else (2288, 5781))))))) else (if n < 3732 then (if n < 3608 then (if n < 3546 then (if n < 3536 then (if n < 3528 then (1192, 4714) else (if n < 3530 then (3161, 6689) else (0, 3530))) else (if n < 3542 then (if n < 3540 then (4108, 7644) else (767, 4307)) else (if n < 3544 then (370, 3912) else (1800, 5344)))) else (if n < 3598 then (if n < 3579 then (2457, 6003) else (if n < 3582 then (3344, 6923) else (1339, 4921))) else (if n < 3601 then (if n < 3600 then (121, 3719) else (2629, 6229)) else (if n < 3603 then (1960, 5561) else (906, 4509))))) else (if n < 3675 then (if n < 3655 then (if n < 3631 then (500, 4108) else (if n < 3642 then (3530, 7161) else (1489, 5131))) else (if n < 3666 then (if n < 3659 then (2803, 6458) else (2122, 5781)) else (if n < 3668 then (1048, 4714) else (244, 3912)))) else (if n < 3708 then (if n < 3682 then (632, 4307) else (if n < 3701 then (3719, 7401) else (1643, 5344))) else (if n < 3719 then (if n < 3715 then (2981, 6689) else (2288, 6003)) else (if n < 3729 then (0, 3719) else (1192, 4921)))))) else (if n < 3864 then (if n < 3792 then (if n < 3761 then (if n < 3738 then (3912, 7644) else (if n < 3742 then (370, 4108) else (767, 4509))) else (if n < 3772 then (if n < 3762 then (1800, 5561) else (3161, 6923)) else (if n < 3791 then (2457, 6229) else (121, 3912)))) else (if n < 3817 then (if n < 3807 then (1339, 5131) else (if n < 3808 then (500, 4307) else (906, 4714))) else (if n < 3829 then (if n < 3821 then (3344, 7161) else (1960, 5781)) else (if n < 3855 then (2629, 6458) else (1489, 5344))))) else (if n < 3918 then (if n < 3877 then (if n < 3871 then (244, 4108) else (if n < 3873 then (3530, 7401) else (1048, 4921))) else (if n < 3886 then (if n < 3881 then (632, 4509) else (2122, 6003)) else (if n < 3912 then (2803, 6689) else (0, 3912)))) else (if n < 3941 then (if n < 3937 then (if n < 3925 then (1643, 5561) else (3719, 7644)) else (if n < 3939 then (370, 4307) else (1192, 5131))) else (if n < 3947 then (if n < 3942 then (2288, 6229) else (2981, 6923)) else (if n < 3981 then (767, 4714) else (1800, 5781))))))))) else (if n < 5131 then (if n < 4509 then (if n < 4232 then (if n < 4108 then (if n < 4057 then (if n < 4005 then (if n < 4000 then (121, 4108) else (if n < 4001 then (3161, 7161) else (2457, 6458))) else (if n < 4015 then (if n < 4009 then (1339, 5344) else (500, 4509)) else (if n < 4043 then (906, 4921) else (1960, 6003)))) else (if n < 4072 then (if n < 4060 then (3344, 7401) else (if n < 4063 then (2629, 6689) else (244, 4307))) else (if n < 4083 then (if n < 4082 then (1489, 5561) else (632, 4714)) else (if n < 4107 then (1048, 5131) else (2122, 6229))))) else (if n < 4170 then (if n < 4138 then (if n < 4114 then (0, 4108) else (if n < 4120 then (3530, 7644) else (2803, 6923))) else (if n < 4152 then (if n < 4139 then (1643, 5781) else (370, 4509)) else (if n < 4154 then (1192, 5344) else (767, 4921)))) else (if n < 4203 then (if n < 4180 then (2288, 6458) else (if n < 4186 then (2981, 7161) else (121, 4307))) else (if n < 4222 then (if n < 4214 then (1800, 6003) else (500, 4714)) else (if n < 4225 then (1339, 5561) else (906, 5131)))))) else (if n < 4364 then (if n < 4296 then (if n < 4269 then (if n < 4240 then (2457, 6689) else (if n < 4265 then (3161, 7401) else (244, 4509))) else (if n < 4292 then (if n < 4289 then (1960, 6229) else (632, 4921)) else (if n < 4294 then (1489, 5781) else (2629, 6923)))) else (if n < 4336 then (if n < 4300 then (1048, 5344) else (if n < 4307 then (3344, 7644) else (0, 4307))) else (if n < 4358 then (if n < 4344 then (2122, 6458) else (370, 4714)) else (if n < 4360 then (2803, 7161) else (1643, 6003))))) else (if n < 4438 then (if n < 4401 then (if n < 4369 then (767, 5131) else (if n < 4388 then (1192, 5561) else (121, 4509))) else (if n < 4421 then (if n < 4420 then (2288, 6689) else (2981, 7401)) else (if n < 4429 then (500, 4921) else (1800, 6229)))) else (if n < 4470 then (if n < 4442 then (906, 5344) else (if n < 4466 then (1339, 5781) else (2457, 6923))) else (if n < 4498 then (if n < 4483 then (244, 4714) else (3161, 7644)) else (if n < 4499 then (1960, 6458) else (632, 5131))))))) else (if n < 4801 then (if n < 4658 then (if n < 4586 then (if n < 4532 then (if n < 4513 then (0, 4509) else (if n < 4514 then (1048, 5561) else (1489, 6003))) else (if n < 4567 then (if n < 4551 then (2629, 7161) else (370, 4921)) else (if n < 4577 then (2122, 6689) else (767, 5344)))) else (if n < 4598 then (if n < 4589 then (1643, 6229) else (if n < 4593 then (1192, 5781) else (121, 4714))) else (if n < 4635 then (if n < 4631 then (2803, 7401) else (500, 5131)) else (if n < 4655 then (2288, 6923) else (906, 5561))))) else (if n < 4729 then (if n < 4677 then (if n < 4663 then (1800, 6458) else (if n < 4664 then (2981, 7644) else (1339, 6003))) else (if n < 4712 then (if n < 4704 then (244, 4921) else (2457, 7161)) else (if n < 4714 then (632, 5344) else (0, 4714)))) else (if n < 4761 then (if n < 4733 then (1960, 6689) else (if n < 4740 then (1048, 5781) else (1489, 6229))) else (if n < 4794 then (if n < 4772 then (370, 5131) else (2629, 7401)) else (if n < 4800 then (767, 5561) else (121, 4921)))))) else (if n < 4963 then (if n < 4887 then (if n < 4841 then (if n < 4811 then (2122, 6923) else (if n < 4815 then (1192, 6003) else (1643, 6458))) else (if n < 4873 then (if n < 4844 then (2803, 7644) else (500, 5344)) else (if n < 4875 then (2288, 7161) else (906, 5781)))) else (if n < 4921 then (if n < 4889 then (244, 5131) else (if n < 4890 then (1800, 6689) else (1339, 6229))) else (if n < 4944 then (if n < 4929 then (0, 4921) else (632, 5561)) else (if n < 4955 then (2457, 7401) else (1048, 6003))))) else (if n < 5039 then (if n < 5010 then (if n < 4969 then (1960, 6923) else (if n < 4974 then (1489, 6458) else (370, 5344))) else (if n < 5015 then (if n < 5014 then (121, 5131) else (767, 5781)) else (if n < 5037 then (2629, 7644) else (1192, 6229)))) else (if n < 5100 then (if n < 5061 then (if n < 5046 then (2122, 7161) else (1643, 6689)) else (if n < 5097 then (500, 5561) else (906, 6003))) else (if n < 5119 then (if n < 5113 then (244, 5344) else (2288, 7401)) else (if n < 5123 then (1339, 6458) else (1800, 6923)))))))) else (if n < 5958 then (if n < 5518 then (if n < 5323 then (if n < 5223 then (if n < 5187 then (if n < 5149 then (0, 5131) else (if n < 5181 then (632, 5781) else (1048, 6229))) else (if n < 5200 then (if n < 5191 then (2457, 7644) else (370, 5561)) else (if n < 5201 then (1489, 6689) else (1960, 7161)))) else (if n < 5279 then (if n < 5236 then (121, 5344) else (if n < 5266 then (767, 6003) else (1192, 6458))) else (if n < 5281 then (if n < 5280 then (2122, 7401) else (1643, 6923)) else (if n < 5317 then (500, 5781) else (244, 5561))))) else (if n < 5411 then (if n < 5356 then (if n < 5344 then (906, 6229) else (if n < 5350 then (0, 5344) else (1339, 6689))) else (if n < 5371 then (if n < 5361 then (2288, 7644) else (1800, 7161)) else (if n < 5410 then (632, 6003) else (1048, 6458)))) else (if n < 5441 then (if n < 5434 then (370, 5781) else (if n < 5440 then (1489, 6923) else (121, 5561))) else (if n < 5497 then (if n < 5462 then (1960, 7401) else (767, 6229)) else (if n < 5503 then (1192, 6689) else (500, 6003)))))) else (if n < 5729 then (if n < 5601 then (if n < 5552 then (if n < 5522 then (1643, 7161) else (if n < 5537 then (2122, 7644) else (244, 5781))) else (if n < 5584 then (if n < 5561 then (906, 6458) else (0, 5561)) else (if n < 5597 then (1339, 6923) else (632, 6229)))) else (if n < 5660 then (if n < 5633 then (1800, 7401) else (if n < 5641 then (370, 6003) else (1048, 6689))) else (if n < 5684 then (if n < 5672 then (121, 5781) else (1489, 7161)) else (if n < 5691 then (1960, 7644) else (767, 6458))))) else (if n < 5826 then (if n < 5759 then (if n < 5731 then (500, 6229) else (if n < 5758 then (1192, 6923) else (1643, 7401))) else (if n < 5783 then (if n < 5781 then (244, 6003) else (0, 5781)) else (if n < 5822 then (906, 6689) else (1339, 7161)))) else (if n < 5875 then (if n < 5844 then (632, 6458) else (if n < 5859 then (1800, 7644) else (370, 6229))) else (if n < 5912 then (if n < 5882 then (1048, 6923) else (121, 6003)) else (if n < 5922 then (1489, 7401) else (767, 6689))))))) else (if n < 6495 then (if n < 6209 then (if n < 6062 then (if n < 6001 then (if n < 5969 then (500, 6458) else (if n < 5985 then (1192, 7161) else (244, 6229))) else (if n < 6017 then (if n < 6003 then (1643, 7644) else (0, 6003)) else (if n < 6057 then (906, 6923) else (632, 6689)))) else (if n < 6113 then (if n < 6088 then (1339, 7401) else (if n < 6108 then (370, 6458) else (121, 6229))) else (if n < 6156 then (if n < 6155 then (1048, 7161) else (1489, 7644)) else (if n < 6189 then (767, 6923) else (500, 6689))))) else (if n < 6337 then (if n < 6255 then (if n < 6214 then (1192, 7401) else (if n < 6229 then (244, 6458) else (0, 6229))) else (if n < 6305 then (if n < 6291 then (906, 7161) else (632, 6923)) else (if n < 6319 then (1339, 7644) else (370, 6689)))) else (if n < 6423 then (if n < 6353 then (121, 6458) else (if n < 6394 then (1048, 7401) else (767, 7161))) else (if n < 6452 then (if n < 6445 then (500, 6923) else (244, 6689)) else (if n < 6458 then (1192, 7644) else (0, 6458)))))) else (if n < 6901 then (if n < 6679 then (if n < 6568 then (if n < 6529 then (906, 7401) else (if n < 6553 then (632, 7161) else (370, 6923))) else (if n < 6634 then (if n < 6596 then (121, 6689) else (1048, 7644)) else (if n < 6661 then (767, 7401) else (500, 7161)))) else (if n < 6769 then (if n < 6689 then (244, 6923) else (if n < 6738 then (0, 6689) else (906, 7644))) else (if n < 6802 then (if n < 6791 then (632, 7401) else (370, 7161)) else (if n < 6877 then (121, 6923) else (767, 7644))))) else (if n < 7157 then (if n < 7012 then (if n < 6917 then (500, 7401) else (if n < 6923 then (244, 7161) else (0, 6923))) else (if n < 7040 then (if n < 7031 then (632, 7644) else (370, 7401)) else (if n < 7144 then (121, 7161) else (500, 7644)))) else (if n < 7400 then (if n < 7274 then (if n < 7161 then (244, 7401) else (0, 7161)) else (if n < 7280 then (370, 7644) else (121, 7401))) else (if n < 7523 then (if n < 7401 then (244, 7644) else (0, 7401)) else (if n < 7644 then (121, 7644) else (0, 7644)))))))))))

theorem jitter42_difference_certificate : ∀ x ∈ positivePairs (prefixSet jitter42), jitter42_decode (x.2-x.1) = x := by rw [jitter42_prefixSet]; decide +kernel

theorem jitter42_distinct : HasDistinctSums jitter42 := by
  apply (hasDistinctSums_iff_prefix_differences jitter42
    (fun i ↦ lt_of_lt_of_le (by norm_num) (jitter42_bounds i).1)).mpr
  intro x hx y hy he
  calc
    x = jitter42_decode (x.2-x.1) := (jitter42_difference_certificate x hx).symm
    _ = jitter42_decode (y.2-y.1) := congrArg jitter42_decode he
    _ = y := jitter42_difference_certificate y hy

theorem jitter42_lower : 42 ≤ f 243 := by
  apply admissible_length_le_f jitter42
  · rintro x ⟨i, rfl⟩
    exact jitter42_bounds i
  · exact jitter42_mono
  · exact jitter42_distinct
/- END GENERATED JITTER42 CERTIFICATE -/

end Erdos357
