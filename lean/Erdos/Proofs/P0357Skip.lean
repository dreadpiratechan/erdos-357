import Erdos.Proofs.P0357

/-! Erdos 357, the "skip" family: a modulus-42 pattern with 12 slots deleted at index `b`.

`sk u b t = 42 u + 42 (t / 6) + R (t mod 12) + 84 [b ≤ t]` with `R = (2,7,11,25,26,34)`.

Part A: the exact window-sum formula, the reduction of every ordered collision to a single divisor
equation `L * δ = 72 u + 66 + 12 b` (length gap 12, the skip lying strictly inside the short
window), all other collision types being excluded by size (`collision_pair`, `distinct_skip`).
Part B: for `b = 288 j`, `j ≥ 500`, a union bound over the divisor pairs shows that some `u` in the
window `[288 j² + 12 j + 1, 288 j² + 2012 j]` (length `2000 j`) has no solution (`exists_good`).
Part C: `skip_lower : 360 j ≤ f (12096 j² + 87024 j + 81)` and the real forms
`f n ≥ (15 / √21) √n - 1800` (`n ≥ 12096 * 504²`), `15/√21 = 360/√12096 = 3.2733...`.

`f` and `HasDistinctSums` are the pinned definitions of `Erdos.Proofs.P0357`.
See `problems/0357/SKIP.md` for the written proof.  No claim of literature priority is made. -/

namespace Erdos357
open Finset

namespace Skip

/-- Prefix sums of the offsets `ε = (2,0,-3,4,-2,-1)` of `R r = 7 r + ε r`. -/
def pe6 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | 2 => 2
  | 3 => -1
  | 4 => 3
  | 5 => 1
  | _ => 0

def pe (n : ℕ) : ℤ := pe6 (n % 6)

theorem pe_bounds (n : ℕ) : -1 ≤ pe n ∧ pe n ≤ 3 := by
  unfold pe
  have h : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at h ⊢
  interval_cases r <;> decide

/-- The skip sequence. -/
def sk (u b t : ℕ) : ℕ :=
  42 * u + 42 * (t / 6) + Mod42.residue (Mod42.phase t) + (if b ≤ t then 84 else 0)

theorem sk_cast (u b t : ℕ) : (sk u b t : ZMod 42) = Mod42.residue (Mod42.phase t) := by
  have h42 : (42 : ZMod 42) = 0 := by decide
  have h84 : (84 : ZMod 42) = 0 := by decide
  unfold sk
  split_ifs <;> simp [h42, h84]

theorem sk_prefix_cast (u b n : ℕ) :
    ((∑ t ∈ range n, sk u b t : ℕ) : ZMod 42) = Mod42.pref (Mod42.phase n) := by
  induction n with
  | zero => norm_num [Mod42.phase, Mod42.pref]
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_add, ih, sk_cast, Mod42.phase_succ, Mod42.pref_step]

theorem sk_block_cast (u b i l : ℕ) :
    ((∑ t ∈ range l, sk u b (i+t) : ℕ) : ZMod 42) =
      Mod42.pref (Mod42.phase (i+l)) - Mod42.pref (Mod42.phase i) := by
  have h := congrArg (fun x : ℕ ↦ (x : ZMod 42)) (sum_range_add (sk u b) i l)
  dsimp only at h
  rw [Nat.cast_add, sk_prefix_cast, sk_prefix_cast] at h
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h.symm)

/-- Equal block sums force equal lengths modulo 12 (spectral lemma of the modulus-42 pattern). -/
theorem sk_block_lengths_mod (u b i l j r : ℕ)
    (h : ∑ t ∈ range l, sk u b (i+t) = ∑ t ∈ range r, sk u b (j+t)) : l % 12 = r % 12 := by
  have hc := congrArg (fun x : ℕ ↦ (x : ZMod 42)) h
  dsimp only at hc
  rw [sk_block_cast, sk_block_cast] at hc
  have he := Mod42.length_certificate (Mod42.phase i) (Mod42.phase (i+l))
    (Mod42.phase j) (Mod42.phase (j+r)) hc
  dsimp [Mod42.phase] at he
  omega

theorem residue_pos (i : Fin 12) : 0 < Mod42.residue i := by
  fin_cases i <;> decide

theorem sk_pos (u b t : ℕ) : 0 < sk u b t := by
  have := residue_pos (Mod42.phase t)
  unfold sk
  omega

theorem sk_mono (u b : ℕ) : StrictMono (sk u b) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have h := Mod42.residue_step (Mod42.phase t)
  have hp : Mod42.phase (t+1) = Mod42.phase t + 1 := Mod42.phase_succ t
  unfold sk
  rw [hp]
  have hv : (Mod42.phase t).val = t % 12 := rfl
  rw [hv] at h
  by_cases h5 : (t % 12) % 6 = 5
  · have h5' : t % 6 = 5 := by omega
    have hd : (t+1)/6 = t/6 + 1 := by omega
    simp only [h5, if_true] at h
    rw [hd]
    split_ifs <;> omega
  · have h5' : ¬ t % 6 = 5 := by omega
    have hd : (t+1)/6 = t/6 := by omega
    simp only [h5, if_false] at h
    rw [hd]
    split_ifs <;> omega

theorem res_eq (t : ℕ) :
    (Mod42.residue (Mod42.phase t) : ℤ) + 42 * ((t / 6 : ℕ) : ℤ) = 7 * (t : ℤ) + (pe (t+1) - pe t) := by
  have key : ∀ c : Fin 12, (Mod42.residue c : ℤ) =
      7 * ((c.val % 6 : ℕ) : ℤ) + (pe6 ((c.val % 6 + 1) % 6) - pe6 (c.val % 6)) := by
    decide
  have h := key (Mod42.phase t)
  have hv : (Mod42.phase t).val % 6 = t % 6 := by
    simp only [Mod42.phase]
    omega
  rw [hv] at h
  unfold pe
  have h1 : (t + 1) % 6 = (t % 6 + 1) % 6 := by omega
  rw [h1, h]
  have h2 : 6 * (t / 6) + t % 6 = t := Nat.div_add_mod t 6
  have h3 : (6 : ℤ) * ((t / 6 : ℕ) : ℤ) + ((t % 6 : ℕ) : ℤ) = t := by exact_mod_cast h2
  linarith

theorem sk_int (u b t : ℕ) : (sk u b t : ℤ) =
    42 * u + 7 * t + (pe (t+1) - pe t) + (if b ≤ t then 84 else 0) := by
  have h := res_eq t
  unfold sk
  push_cast at h ⊢
  split_ifs <;> linarith

theorem sk_prefix (u b n : ℕ) :
    2 * ((∑ t ∈ range n, sk u b t : ℕ) : ℤ) =
      84 * u * n + 7 * n * (n - 1) + 2 * pe n + 168 * ((n - b : ℕ) : ℤ) := by
  induction n with
  | zero => simp [pe, pe6]
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_add, mul_add, ih, sk_int]
    by_cases hbn : b ≤ n
    · have hb1 : ((n + 1 - b : ℕ) : ℤ) = ((n - b : ℕ) : ℤ) + 1 := by omega
      rw [hb1]
      simp only [hbn, if_true]
      push_cast
      ring
    · have hb1 : ((n + 1 - b : ℕ) : ℤ) = ((n - b : ℕ) : ℤ) := by omega
      rw [hb1]
      simp only [hbn, if_false]
      push_cast
      ring

/-- Exact doubled window sum of the skip sequence. -/
theorem sk_block (u b x L : ℕ) :
    2 * ((∑ t ∈ range L, sk u b (x+t) : ℕ) : ℤ) =
      84 * u * L + 7 * L * (2 * x + L - 1) + 2 * (pe (x+L) - pe x)
        + 168 * (((x + L - b : ℕ) : ℤ) - ((x - b : ℕ) : ℤ)) := by
  have h := sum_range_add (sk u b) x L
  have h1 := sk_prefix u b (x+L)
  have h2 := sk_prefix u b x
  have h3 : ((∑ t ∈ range (x+L), sk u b t : ℕ) : ℤ) =
      ((∑ t ∈ range x, sk u b t : ℕ) : ℤ) + ((∑ t ∈ range L, sk u b (x+t) : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at h1 h2 h3 ⊢
  linear_combination h1 - h2 - 2 * h3

/-! ### Size exclusions: pure integer arithmetic -/

theorem bound_core (u s d h h0 x dE N : ℤ) (hu : 0 ≤ u) (h0pos : 1 ≤ h0) (hh : h0 ≤ h)
    (hx : 0 ≤ x) (hs : 0 ≤ s) (hdE : dE ≤ 8)
    (hK : 84 * u * h = 7 * (2 * s * d - 2 * h * x - 2 * h * s - h ^ 2 + h) + 2 * dE + 168 * N) :
    84 * h0 * u ≤ 14 * s * d + 16 + 168 * N := by
  have hh0 : 0 ≤ h := by linarith
  have h1 : h0 * u ≤ h * u := by nlinarith
  have h2 : h ≤ h ^ 2 := by nlinarith
  have h3 : 0 ≤ h * x := mul_nonneg hh0 hx
  have h4 : 0 ≤ h * s := mul_nonneg hh0 hs
  nlinarith

theorem caseAB (j u s d h x dE N : ℤ) (hj : 1 ≤ j) (hu : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hh : 12 ≤ h) (hx : 0 ≤ x) (hs : 0 ≤ s) (_hd : 0 ≤ d) (hsd : s + d ≤ 288 * j)
    (hdE : dE ≤ 8) (hN : N ≤ 0)
    (hK : 84 * u * h = 7 * (2 * s * d - 2 * h * x - 2 * h * s - h ^ 2 + h) + 2 * dE + 168 * N) :
    False := by
  have hu0 : 0 ≤ u := by nlinarith
  have core := bound_core u s d h 12 x dE N hu0 (by norm_num) hh hx hs hdE hK
  have h1 : 4 * (s * d) ≤ (s + d) ^ 2 := by nlinarith [sq_nonneg (s - d)]
  have h2 : (s + d) ^ 2 ≤ (288 * j) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hsd) (by linarith : (0 : ℤ) ≤ 288 * j + (s + d))]
  nlinarith

theorem caseC (j u s d h x dE N : ℤ) (hj : 1 ≤ j) (hu : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hh : 12 ≤ h) (hx : 0 ≤ x) (hs : 0 ≤ s) (_hd : 0 ≤ d)
    (hs72 : s ≤ 72 * j) (hdk : d + s ≤ 360 * j)
    (hdE : dE ≤ 8) (hN : N ≤ s)
    (hK : 84 * u * h = 7 * (2 * s * d - 2 * h * x - 2 * h * s - h ^ 2 + h) + 2 * dE + 168 * N) :
    False := by
  have hu0 : 0 ≤ u := by nlinarith
  have core := bound_core u s d h 12 x dE N hu0 (by norm_num) hh hx hs hdE hK
  have h1 : s * d ≤ s * (360 * j - s) := mul_le_mul_of_nonneg_left (by linarith) hs
  have h2 : 0 ≤ (72 * j - s) * (288 * j - s) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem caseD1 (j u s d h x dE N : ℤ) (hj : 1 ≤ j) (hu : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hh : 24 ≤ h) (hx : 0 ≤ x) (hs : 0 ≤ s) (hd : 0 ≤ d) (hsd : s + d ≤ 360 * j)
    (hdE : dE ≤ 8) (hN : N ≤ s)
    (hK : 84 * u * h = 7 * (2 * s * d - 2 * h * x - 2 * h * s - h ^ 2 + h) + 2 * dE + 168 * N) :
    False := by
  have hu0 : 0 ≤ u := by nlinarith
  have core := bound_core u s d h 24 x dE N hu0 (by norm_num) hh hx hs hdE hK
  have h1 : 4 * (s * d) ≤ (s + d) ^ 2 := by nlinarith [sq_nonneg (s - d)]
  have h2 : (s + d) ^ 2 ≤ (360 * j) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hsd) (by linarith : (0 : ℤ) ≤ 360 * j + (s + d))]
  have h3 : s ≤ 360 * j := by linarith
  have hjj : j ≤ j * j := by nlinarith
  nlinarith

/-! ### The mod-6 phase filter for the surviving case (length gap 12, S straddles the skip) -/

theorem phase_filter (ξ η l : ℕ) (hξ : ξ < 6) (hη : η < 6) (hl : l < 6)
    (h7 : ((pe6 ((η + l) % 6) - pe6 η) - (pe6 ((ξ + l) % 6) - pe6 ξ)) % 7 = 0)
    (h6 : 7 * (((η : ZMod 6) - ξ) * ((l : ZMod 6) + 12)) +
      ((((pe6 ((η + l) % 6) - pe6 η) - (pe6 ((ξ + l) % 6) - pe6 ξ) : ℤ)) : ZMod 6) = 0) :
    (pe6 ((η + l) % 6) - pe6 η) - (pe6 ((ξ + l) % 6) - pe6 ξ) = 0 := by
  interval_cases ξ <;> interval_cases η <;> interval_cases l <;> revert h7 h6 <;> decide

/-! ### Reduction of an ordered collision to a divisor equation -/

theorem collision_pair (j u x L y s b : ℕ) (hj : 1 ≤ j) (hb : b = 288 * j)
    (hu : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hs : 0 < s) (hsL : s < L) (hxy : x + L ≤ y) (hk : y + s ≤ 360 * j)
    (he : ∑ t ∈ range L, sk u b (x + t) = ∑ t ∈ range s, sk u b (y + t)) :
    ∃ L' δ : ℕ, 14 ≤ L' ∧ L' ≤ δ ∧ δ + 1 ≤ b ∧ L' * δ = 72 * u + 66 + 12 * b := by
  have hmod := sk_block_lengths_mod u b x L y s he
  obtain ⟨h, rfl⟩ : ∃ h, L = s + h := ⟨L - s, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
  have hh12 : 12 ≤ h := by omega
  have hh0 : h % 12 = 0 := by omega
  have e1 := sk_block u b x (s + h)
  have e2 := sk_block u b (x + d) s
  have hB : ((∑ t ∈ range (s + h), sk u b (x + t) : ℕ) : ℤ) =
      ((∑ t ∈ range s, sk u b (x + d + t) : ℕ) : ℤ) := by exact_mod_cast he
  obtain ⟨dE, hdE⟩ : ∃ dE : ℤ,
      dE = (pe (x + d + s) - pe (x + d)) - (pe (x + (s + h)) - pe x) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = (((x + d + s - b : ℕ) : ℤ) - ((x + d - b : ℕ) : ℤ)) -
      (((x + (s + h) - b : ℕ) : ℤ) - ((x - b : ℕ) : ℤ)) := ⟨_, rfl⟩
  have hK : (84 : ℤ) * u * h =
      7 * (2 * s * d - 2 * h * x - 2 * h * s - h ^ 2 + h) + 2 * dE + 168 * N := by
    rw [hdE, hN]
    push_cast at e1 e2 hB ⊢
    linear_combination 2 * hB - e1 + e2
  have p1 := pe_bounds (x + d + s)
  have p2 := pe_bounds (x + d)
  have p3 := pe_bounds (x + (s + h))
  have p4 := pe_bounds x
  have hdE8 : dE ≤ 8 := by rw [hdE]; linarith [p1.2, p2.1, p3.1, p4.2]
  have hu' : (288 : ℤ) * j ^ 2 + 12 * j + 1 ≤ u := by exact_mod_cast hu
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hh12' : (12 : ℤ) ≤ h := by exact_mod_cast hh12
  have hbj : (b : ℤ) = 288 * j := by exact_mod_cast hb
  by_cases hA : x + d + s ≤ b
  · exfalso
    have hN0 : N ≤ 0 := by rw [hN]; omega
    exact caseAB j u s d h x dE N hj' hu' hh12' (by positivity) (by positivity) (by positivity)
      (by omega) hdE8 hN0 hK
  by_cases hB' : b ≤ x
  · exfalso
    have hN0 : N ≤ 0 := by rw [hN]; omega
    exact caseAB j u s d h x dE N hj' hu' hh12' (by positivity) (by positivity) (by positivity)
      (by omega) hdE8 hN0 hK
  by_cases hC : b ≤ x + d
  · exfalso
    have hNs : N ≤ s := by rw [hN]; omega
    exact caseC j u s d h x dE N hj' hu' hh12' (by positivity) (by positivity) (by positivity)
      (by omega) (by omega) hdE8 hNs hK
  by_cases hh24 : 24 ≤ h
  · exfalso
    have hNs : N ≤ s := by rw [hN]; omega
    have hh24' : (24 : ℤ) ≤ h := by exact_mod_cast hh24
    exact caseD1 j u s d h x dE N hj' hu' hh24' (by positivity) (by positivity) (by positivity)
      (by omega) hdE8 hNs hK
  -- the surviving case: h = 12, x + d < b < x + d + s
  have hh : h = 12 := by omega
  subst hh
  have hN3 : N = ((x + d + s : ℕ) : ℤ) - b := by rw [hN]; omega
  have E12 : (504 : ℤ) * u + 462 + 84 * b = 7 * (d * (s + 12)) + dE := by
    have h2 : (2 : ℤ) * (504 * u + 462 + 84 * b) = 2 * (7 * (d * (s + 12)) + dE) := by
      rw [hN3] at hK
      push_cast at hK
      linear_combination hK
    linarith
  have h7 : dE % 7 = 0 := by
    have := E12
    generalize (d : ℤ) * (s + 12) = P at this
    omega
  have h6 : (6 : ℤ) ∣ 7 * (d * (s + 12)) + dE := ⟨84 * u + 77 + 14 * b, by linarith⟩
  have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mpr (by exact_mod_cast h6)
  push_cast at hZ
  have hd6 : (d : ZMod 6) = (((x + d) % 6 : ℕ) : ZMod 6) - ((x % 6 : ℕ) : ZMod 6) := by
    rw [ZMod.natCast_mod, ZMod.natCast_mod]
    push_cast
    ring
  have hs6 : (s : ZMod 6) = ((s % 6 : ℕ) : ZMod 6) := (ZMod.natCast_mod s 6).symm
  have hdE' : dE = (pe6 (((x + d) % 6 + s % 6) % 6) - pe6 ((x + d) % 6)) -
      (pe6 ((x % 6 + s % 6) % 6) - pe6 (x % 6)) := by
    rw [hdE]
    unfold pe
    have a1 : (x + d + s) % 6 = ((x + d) % 6 + s % 6) % 6 := by omega
    have a2 : (x + (s + 12)) % 6 = (x % 6 + s % 6) % 6 := by omega
    rw [a1, a2]
  have hres := phase_filter (x % 6) ((x + d) % 6) (s % 6) (by omega) (by omega) (by omega)
    (by rw [← hdE']; exact h7) (by rw [← hdE', ← hd6, ← hs6]; exact hZ)
  rw [← hdE'] at hres
  have hdE0 : dE = 0 := hres
  refine ⟨s + 12, d, by omega, by omega, by omega, ?_⟩
  have hfin : (d : ℤ) * (s + 12) = 72 * u + 66 + 12 * b := by
    rw [hdE0] at E12
    linarith
  zify
  linarith

/-- No ordered collision of the skip sequence unless the divisor equation `L δ = 72 u + 66 + 12 b`
has a solution in the box `14 ≤ L ≤ δ < b`. -/
theorem distinct_skip (j u b : ℕ) (hj : 1 ≤ j) (hb : b = 288 * j)
    (hu : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hno : ¬ ∃ L δ : ℕ, 14 ≤ L ∧ L ≤ δ ∧ δ + 1 ≤ b ∧ L * δ = 72 * u + 66 + 12 * b) :
    HasDistinctSums (fun i : Fin (360 * j) ↦ sk u b i.val) := by
  apply hasDistinctSums_of_no_ordered_collision (sk u b) (360 * j) (sk_pos u b) (sk_mono u b)
  intro i l j' r hr hrl hij hjr heq
  exact hno (collision_pair j u i l j' r b hj hb hu hr hrl hij hjr heq)



/-- number of residues `r` mod 72 with `ρ * r ≡ 66 (mod 72)`. -/
def nres (ρ : ℕ) : ℕ := ((range 72).filter (fun r => ρ * r % 72 = 66)).card

theorem nres_sum : ∑ ρ ∈ range 72, nres ρ = 96 := by
  unfold nres
  decide +kernel

theorem card_span (T : Finset ℕ) (m : ℕ) (hT : ∀ a ∈ T, ∀ b ∈ T, a ≤ b + m) :
    T.card ≤ m + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  · have h0 : T.min' hne ∈ T := T.min'_mem hne
    have hsub : T ⊆ Icc (T.min' hne) (T.min' hne + m) := by
      intro b hb
      rw [mem_Icc]
      exact ⟨T.min'_le b hb, hT b hb _ h0⟩
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    omega

/-- A set of naturals in one residue class mod 72 with `lo ≤ L δ ≤ hi`, `hi ≤ lo + 72 m`. -/
theorem card_class_le (L ρ lo hi m : ℕ) (hL : 0 < L) (hm : hi ≤ lo + 72 * m)
    (S : Finset ℕ) (hS : ∀ δ ∈ S, δ % 72 = ρ ∧ lo ≤ L * δ ∧ L * δ ≤ hi) :
    S.card ≤ m / L + 1 := by
  have key : (S.image (· / 72)).card ≤ m / L + 1 := by
    apply card_span
    intro a ha b hb
    obtain ⟨δa, hδa, rfl⟩ := mem_image.mp ha
    obtain ⟨δb, hδb, rfl⟩ := mem_image.mp hb
    obtain ⟨ra, la, ua⟩ := hS δa hδa
    obtain ⟨rb, lb, ub⟩ := hS δb hδb
    by_cases hab : δa ≤ δb
    · exact le_trans (Nat.div_le_div_right (c := 72) hab) (Nat.le_add_right _ _)
    · push_neg at hab
      obtain ⟨t, ht⟩ : ∃ t, δa / 72 = δb / 72 + t := ⟨δa / 72 - δb / 72, by omega⟩
      have e1 : δa = 72 * (δb / 72 + t) + ρ := by omega
      have e2 : δb = 72 * (δb / 72) + ρ := by omega
      have h1 : L * δa ≤ L * δb + 72 * m := by omega
      have h2 : L * t ≤ m := by
        rw [e1] at h1
        nth_rewrite 2 [e2] at h1
        nlinarith
      rw [ht]
      have : t ≤ m / L := (Nat.le_div_iff_mul_le hL).mpr (by rw [mul_comm]; exact h2)
      exact Nat.add_le_add_left this _
  rwa [card_image_of_injOn] at key
  intro a ha b hb hab
  have ha' := hS a ha
  have hb' := hS b hb
  simp only at hab
  omega


/-! ### The divisor-pair count -/

/-- lower end of the range of `L * δ`: `72 (288 j² + 12 j + 1) + 66 + 3456 j`. -/
def P1 (j : ℕ) : ℕ := 20736 * j ^ 2 + 4320 * j + 138
/-- upper end: `72 (288 j² + 2012 j) + 66 + 3456 j`. -/
def P2 (j : ℕ) : ℕ := 20736 * j ^ 2 + 148320 * j + 66

/-- the admissible cofactors `δ` for a given `L` -/
def Delta (j L : ℕ) : Finset ℕ :=
  (range (288 * j)).filter (fun δ => L * δ % 72 = 66 ∧ P1 j ≤ L * δ ∧ L * δ ≤ P2 j)

/-- the `u` values produced by the cofactors of `L` -/
def Gset (j L : ℕ) : Finset ℕ := (Delta j L).image (fun δ => (L * δ - 66 - 3456 * j) / 72)

theorem card_Delta_le (j L : ℕ) (hj : 1 ≤ j) (hL : 0 < L) :
    (Delta j L).card ≤ nres (L % 72) * ((2000 * j - 1) / L + 1) := by
  have hfib := card_eq_sum_card_fiberwise (s := Delta j L) (f := fun δ => δ % 72)
    (t := (range 72).filter (fun r => L * r % 72 = 66)) (by
      intro δ hδ
      rw [Finset.mem_coe, Delta, Finset.mem_filter, Finset.mem_range] at hδ
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (by norm_num), ?_⟩
      show L * (δ % 72) % 72 = 66
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      exact hδ.2.1)
  rw [hfib]
  have hcard : ((range 72).filter (fun r => L * r % 72 = 66)).card = nres (L % 72) := by
    unfold nres
    congr 1
    apply filter_congr
    intro r hr
    have hr' : r % 72 = r := Nat.mod_eq_of_lt (mem_range.mp hr)
    have : L * r % 72 = L % 72 * r % 72 := by rw [Nat.mul_mod, hr']
    rw [this]
  calc _ ≤ ((range 72).filter (fun r => L * r % 72 = 66)).card • ((2000 * j - 1) / L + 1) := by
        apply sum_le_card_nsmul
        intro ρ hρ
        apply card_class_le L ρ (P1 j) (P2 j) (2000 * j - 1) hL
        · unfold P1 P2
          omega
        · intro δ hδ
          simp only [Delta, mem_filter, mem_range] at hδ
          exact ⟨hδ.2, hδ.1.2.2.1, hδ.1.2.2.2⟩
    _ = nres (L % 72) * ((2000 * j - 1) / L + 1) := by rw [hcard, smul_eq_mul]

theorem card_Gset_le (j L : ℕ) (hj : 1 ≤ j) (hL : 0 < L) :
    (Gset j L).card ≤ nres (L % 72) * ((2000 * j - 1) / L + 1) :=
  (card_image_le).trans (card_Delta_le j L hj hL)


/-- Every `u` in the window that has a divisor pair lies in the union of the `Gset`s. -/
theorem bad_subset (j u : ℕ) (hj : 1 ≤ j) (hu1 : 288 * j ^ 2 + 12 * j + 1 ≤ u)
    (hu2 : u ≤ 288 * j ^ 2 + 2012 * j)
    (hbad : ∃ L δ : ℕ, 14 ≤ L ∧ L ≤ δ ∧ δ + 1 ≤ 288 * j ∧ L * δ = 72 * u + 66 + 12 * (288 * j)) :
    u ∈ (Icc j (2 * j + 7)).biUnion
      (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ))) := by
  obtain ⟨L, δ, hL14, hLδ, hδ, hprod⟩ := hbad
  have hLlow : 72 * j ≤ L := by
    by_contra hlt
    push_neg at hlt
    have h1 : L + 1 ≤ 72 * j := hlt
    have h2 := Nat.mul_le_mul h1 hδ
    nlinarith
  have hLhigh : L ≤ 144 * j + 514 := by
    by_contra hlt
    push_neg at hlt
    have h1 : 144 * j + 515 ≤ L := hlt
    have h2 := Nat.mul_le_mul h1 h1
    have h3 : L * L ≤ L * δ := Nat.mul_le_mul_left L hLδ
    nlinarith
  rw [mem_biUnion]
  refine ⟨L / 72, ?_, ?_⟩
  · rw [mem_Icc]
    exact ⟨by omega, by omega⟩
  · rw [mem_biUnion]
    refine ⟨L % 72, mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
    have hL : 72 * (L / 72) + L % 72 = L := Nat.div_add_mod L 72
    rw [hL]
    unfold Gset
    rw [mem_image]
    refine ⟨δ, ?_, ?_⟩
    · unfold Delta P1 P2
      rw [mem_filter, mem_range]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · omega

theorem union_card_nat (j Q : ℕ) (hj : 1 ≤ j) :
    ((Icc j Q).biUnion (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ)))).card ≤
    ∑ q ∈ Icc j Q, ∑ ρ ∈ range 72, nres ρ * ((2000 * j - 1) / (72 * q + ρ) + 1) := by
  refine (card_biUnion_le).trans (sum_le_sum fun q hq => ?_)
  refine (card_biUnion_le).trans (sum_le_sum fun ρ hρ => ?_)
  have hρ' : ρ < 72 := mem_range.mp hρ
  have hq' : j ≤ q := (mem_Icc.mp hq).1
  have h := card_Gset_le j (72 * q + ρ) hj (by omega)
  have hmod : (72 * q + ρ) % 72 = ρ := by omega
  rw [hmod] at h
  exact h

theorem union_card_real (j Q : ℕ) (hj : 1 ≤ j) :
    ((((Icc j Q).biUnion (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ)))).card : ℕ) : ℝ)
      ≤ ∑ q ∈ Icc j Q, 96 * (2000 * (j : ℝ) / (72 * q) + 1) := by
  have h' := Nat.cast_le (α := ℝ) |>.mpr (union_card_nat j Q hj)
  refine h'.trans ?_
  push_cast
  apply sum_le_sum
  intro q hq
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := le_trans hj (mem_Icc.mp hq).1
    exact_mod_cast this
  calc ∑ ρ ∈ range 72, (nres ρ : ℝ) * ((((2000 * j - 1) / (72 * q + ρ) : ℕ) : ℝ) + 1)
      ≤ ∑ ρ ∈ range 72, (nres ρ : ℝ) * (2000 * (j : ℝ) / (72 * q) + 1) := by
        apply sum_le_sum
        intro ρ hρ
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have e1 : (((2000 * j - 1) / (72 * q + ρ) : ℕ) : ℝ) ≤
            ((2000 * j - 1 : ℕ) : ℝ) / ((72 * q + ρ : ℕ) : ℝ) := Nat.cast_div_le
        have e2 : ((2000 * j - 1 : ℕ) : ℝ) ≤ 2000 * (j : ℝ) := by
          have : 2000 * j - 1 ≤ 2000 * j := Nat.sub_le _ _
          exact_mod_cast this
        have e3 : ((2000 * j - 1 : ℕ) : ℝ) / ((72 * q + ρ : ℕ) : ℝ) ≤
            2000 * (j : ℝ) / (72 * q) := by
          push_cast
          apply div_le_div₀ (by positivity) e2 (by positivity)
          have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
          linarith
        linarith
    _ = 96 * (2000 * (j : ℝ) / (72 * q) + 1) := by
        rw [← sum_mul]
        congr 1
        exact_mod_cast nres_sum

theorem harm_le (j N : ℕ) (hj : 1 ≤ j) (hN : j ≤ N) :
    ∑ q ∈ Icc j N, (1 : ℝ) / q ≤ 1 / j + Real.log N - Real.log j := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hj hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hx : (0 : ℝ) < (N : ℝ) / ((N : ℝ) + 1) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div hN0.ne' (by positivity)] at h1
    have h2 : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by field_simp; ring
    push_cast
    linarith


/-- Counting: for `j ≥ 500` some `u` of the window of length `2000 j` has no divisor pair in the box. -/
theorem exists_good (j : ℕ) (hj : 500 ≤ j) :
    ∃ u : ℕ, 288 * j ^ 2 + 12 * j + 1 ≤ u ∧ u ≤ 288 * j ^ 2 + 2012 * j ∧
      ¬ ∃ L δ : ℕ, 14 ≤ L ∧ L ≤ δ ∧ δ + 1 ≤ 288 * j ∧ L * δ = 72 * u + 66 + 12 * (288 * j) := by
  by_contra hcon
  push_neg at hcon
  have hj1 : 1 ≤ j := by omega
  have hsub : Icc (288 * j ^ 2 + 12 * j + 1) (288 * j ^ 2 + 2012 * j) ⊆
      (Icc j (2 * j + 7)).biUnion (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ))) := by
    intro u hu
    rw [mem_Icc] at hu
    exact bad_subset j u hj1 hu.1 hu.2 (hcon u hu.1 hu.2)
  have hc1 := card_le_card hsub
  rw [Nat.card_Icc] at hc1
  have hc1' : 2000 * j ≤ ((Icc j (2 * j + 7)).biUnion
      (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ)))).card := by omega
  have hc2 := union_card_real j (2 * j + 7) hj1
  have hc1r : (2000 * (j : ℝ)) ≤ ((((Icc j (2 * j + 7)).biUnion
      (fun q => (range 72).biUnion (fun ρ => Gset j (72 * q + ρ)))).card : ℕ) : ℝ) := by
    exact_mod_cast hc1'
  have hjQ : j ≤ 2 * j + 7 := by omega
  have hjr : (500 : ℝ) ≤ j := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < j := by linarith
  have hterm : ∑ q ∈ Icc j (2 * j + 7), 96 * (2000 * (j : ℝ) / (72 * q) + 1) =
      (8000 / 3) * (j : ℝ) * ∑ q ∈ Icc j (2 * j + 7), (1 : ℝ) / q +
        96 * ((2 * j + 7 + 1 - j : ℕ) : ℝ) := by
    rw [mul_sum]
    have : ((2 * j + 7 + 1 - j : ℕ) : ℝ) = ∑ q ∈ Icc j (2 * j + 7), (1 : ℝ) := by
      rw [sum_const, Nat.card_Icc]; simp
    rw [this, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by
      have : 1 ≤ q := le_trans hj1 (mem_Icc.mp hq).1
      exact_mod_cast this
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hharm := harm_le j (2 * j + 7) hj1 hjQ
  have hlogQ : Real.log ((2 * j + 7 : ℕ) : ℝ) ≤ Real.log 2 + Real.log j + 7 / (2 * j) := by
    have hx : (0 : ℝ) < ((2 * (j : ℝ) + 7) / (2 * j)) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : Real.log (2 * (j : ℝ)) = Real.log 2 + Real.log j :=
      Real.log_mul (by norm_num) hjpos.ne'
    have h3 : (2 * (j : ℝ) + 7) / (2 * j) - 1 = 7 / (2 * j) := by field_simp; ring
    push_cast
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hS : ∑ q ∈ Icc j (2 * j + 7), (1 : ℝ) / q ≤ 1 / j + Real.log 2 + 7 / (2 * j) := by
    linarith
  have hcard : ((2 * j + 7 + 1 - j : ℕ) : ℝ) = j + 8 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hmain : (8000 / 3) * (j : ℝ) * ∑ q ∈ Icc j (2 * j + 7), (1 : ℝ) / q ≤
      (8000 / 3) * (j : ℝ) * (1 / j + Real.log 2 + 7 / (2 * j)) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have hexp : (8000 / 3) * (j : ℝ) * (1 / j + Real.log 2 + 7 / (2 * j)) =
      12000 + (8000 / 3) * Real.log 2 * j := by
    field_simp
    ring
  have hl2 : Real.log 2 * (j : ℝ) ≤ 0.6931471808 * j :=
    mul_le_mul_of_nonneg_right hlog2.le hjpos.le
  rw [hcard] at hterm
  nlinarith


/-! ### Assembly: the admissible sequence and the lower bounds -/

theorem residue_le (i : Fin 12) : Mod42.residue i ≤ 34 := by
  fin_cases i <;> decide

/-- For `j ≥ 500` the skip sequence of length `360 j` is an admissible set in
`[1, 12096 j² + 87024 j + 81]`. -/
theorem skip_admissible (j : ℕ) (hj : 500 ≤ j) :
    ∃ a : Fin (360 * j) → ℤ,
      Set.range a ⊆ Set.Icc 1 (12096 * j ^ 2 + 87024 * j + 81 : ℕ) ∧
        StrictMono a ∧ HasDistinctSums a := by
  obtain ⟨u, hu1, hu2, hno⟩ := exists_good j hj
  have hdist := distinct_skip j u (288 * j) (by omega) rfl hu1 hno
  refine ⟨fun i => (sk u (288 * j) i.val : ℤ), ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    have hp := sk_pos u (288 * j) i.val
    have hi := i.isLt
    have hr := residue_le (Mod42.phase i.val)
    dsimp only
    constructor
    · exact_mod_cast hp
    · have hb : sk u (288 * j) i.val ≤ 12096 * j ^ 2 + 87024 * j + 81 := by
        unfold sk
        split_ifs <;> omega
      exact_mod_cast hb
  · intro i i' hii
    have h := sk_mono u (288 * j) hii
    change (sk u (288 * j) i.val : ℤ) < (sk u (288 * j) i'.val : ℤ)
    exact_mod_cast h
  · intro J hJ K hK he
    apply hdist hJ hK
    dsimp only at he
    exact_mod_cast he

/-- Explicit skip construction: `360 j ≤ f (12096 j² + 87024 j + 81)` for `j ≥ 500`. -/
theorem skip_lower (j : ℕ) (hj : 500 ≤ j) : 360 * j ≤ f (12096 * j ^ 2 + 87024 * j + 81) := by
  obtain ⟨a, hr, hm, ha⟩ := skip_admissible j hj
  exact admissible_length_le_f a hr hm ha

/-- Floor form, valid for every `n ≥ 12096 * 504²`. -/
theorem skip_lower_all (n : ℕ) (hn : 12096 * 504 ^ 2 ≤ n) :
    360 * (Nat.sqrt (n / 12096) - 4) ≤ f n := by
  have hq : 504 ≤ Nat.sqrt (n / 12096) := by
    rw [Nat.le_sqrt]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)
  obtain ⟨j, hj⟩ : ∃ j, Nat.sqrt (n / 12096) = j + 4 := ⟨Nat.sqrt (n / 12096) - 4, by omega⟩
  have hj500 : 500 ≤ j := by omega
  have hsq := Nat.sqrt_le (n / 12096)
  have hd := Nat.div_mul_le_self n 12096
  rw [hj] at hsq
  have hle : 12096 * j ^ 2 + 87024 * j + 81 ≤ n := by nlinarith
  obtain ⟨a, hr, hm, ha⟩ := skip_admissible j hj500
  have key : 360 * j ≤ f n := by
    apply admissible_length_le_f a ?_ hm ha
    intro x hx
    have hh := hr hx
    refine ⟨hh.1, hh.2.trans ?_⟩
    exact_mod_cast hle
  rw [hj]
  simpa using key

/-- Quantitative real form for `n ≥ 12096 * 504²`: the coefficient of `√n` is `15/√21 = 3.2733...`
(`360/√12096`), against `12/√21 = 2.6186...` for the pure modulus-42 pattern (`mod42_lower_real`). -/
theorem skip_lower_real_large (n : ℕ) (hn : 12096 * 504 ^ 2 ≤ n) :
    (15 / Real.sqrt 21) * Real.sqrt n - 1800 ≤ (f n : ℝ) := by
  let q := Nat.sqrt (n / 12096)
  have hf := skip_lower_all n hn
  have hq504 : 504 ≤ q := by
    show 504 ≤ Nat.sqrt (n / 12096)
    rw [Nat.le_sqrt]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)
  have hq : 360 * (q + 1) ≤ f n + 1800 := by dsimp [q] at hq504 ⊢; omega
  have hlt : n < 12096 * (q + 1) ^ 2 := by
    have hs := Nat.lt_succ_sqrt (n / 12096)
    have hd := Nat.mod_lt n (by decide : 0 < 12096)
    have he := Nat.div_add_mod n 12096
    dsimp [q]
    nlinarith
  have h0 : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hroot : Real.sqrt n ≤ Real.sqrt 21 * (24 * ((q : ℝ) + 1)) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hn' : (n : ℝ) ≤ 12096 * ((q : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.le_of_lt hlt
      calc (n : ℝ) ≤ 12096 * ((q : ℝ) + 1) ^ 2 := hn'
        _ = (Real.sqrt 21 * (24 * ((q : ℝ) + 1))) ^ 2 := by rw [mul_pow, mul_pow, hs0]; ring
  have hq' : (360 : ℝ) * ((q : ℝ) + 1) ≤ (f n : ℝ) + 1800 := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left hq' (le_of_lt h0)
  have hh' := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 15)
  have hfinal : (15 * Real.sqrt n) / Real.sqrt 21 ≤ (f n : ℝ) + 1800 := by
    apply (div_le_iff₀ h0).mpr
    linarith
  calc (15 / Real.sqrt 21) * Real.sqrt n - 1800 =
        (15 * Real.sqrt n) / Real.sqrt 21 - 1800 := by ring
    _ ≤ (f n : ℝ) := by linarith

/-- The same bound for every `n`, at the price of the constant `181440 = 360 * 504`. -/
theorem skip_lower_real (n : ℕ) :
    (15 / Real.sqrt 21) * Real.sqrt n - 181440 ≤ (f n : ℝ) := by
  by_cases hn : 12096 * 504 ^ 2 ≤ n
  · have := skip_lower_real_large n hn
    linarith
  · push_neg at hn
    have h0 : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
    have hs0 : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
    have hroot : Real.sqrt n ≤ Real.sqrt 21 * 12096 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hn' : (n : ℝ) ≤ 12096 * 504 ^ 2 := by exact_mod_cast Nat.le_of_lt hn
        calc (n : ℝ) ≤ 12096 * 504 ^ 2 := hn'
          _ = (Real.sqrt 21 * 12096) ^ 2 := by rw [mul_pow, hs0]; norm_num
    have hfn : (0 : ℝ) ≤ (f n : ℝ) := Nat.cast_nonneg _
    have h1 : (15 * Real.sqrt n) / Real.sqrt 21 ≤ 181440 := by
      apply (div_le_iff₀ h0).mpr
      linarith
    calc (15 / Real.sqrt 21) * Real.sqrt n - 181440 =
          (15 * Real.sqrt n) / Real.sqrt 21 - 181440 := by ring
      _ ≤ (f n : ℝ) := by linarith

/-- The headline constant: `f n ≥ 3.27 √n - 1800` once `n ≥ 12096 * 504²`. -/
theorem skip_lower_327 (n : ℕ) (hn : 12096 * 504 ^ 2 ≤ n) :
    (327 / 100 : ℝ) * Real.sqrt n - 1800 ≤ (f n : ℝ) := by
  have h := skip_lower_real_large n hn
  have h0 : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 21 ≤ 4.587 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hc : (327 / 100 : ℝ) ≤ 15 / Real.sqrt 21 := by
    rw [le_div_iff₀ h0]
    linarith
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  nlinarith

end Skip
end Erdos357
