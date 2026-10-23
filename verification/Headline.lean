import Erdos357

/-!
Prints the definitions and the exact statements of every theorem the paper relies on,
followed by the axioms each headline theorem depends on.
Run from `lean/`:  lake env lean ../verification/Headline.lean
-/

-- The problem: definitions copied verbatim from Formal Conjectures (see UpstreamPin.lean).
#print Erdos357.HasDistinctSums
#print Erdos357.f

-- Theorem 1 (upper bound) and the earlier forms of the same argument.
#check @Erdos357Upper.f_le_upper4
#check @Erdos357Upper.f_le_real4
#check @Erdos357Upper.f_le_upper2
#check @Erdos357Upper.f_le_real2
#check @Erdos357Upper.f_le_upper
#check @Erdos357Upper.f_le_real
#check @Erdos357.f_le_half_add_sqrt

-- Upper-bound lemmas named in the paper.
#print Erdos357Upper.blk
#print Erdos357Upper.Adm
#print Erdos357Upper.canon
#print Erdos357Upper.holes
#print Erdos357Upper.Hit
#print Erdos357Upper.cnt
#print Erdos357Upper.bandsL
#check @Erdos357Upper.adm_of_int
#check @Erdos357Upper.canon_spec
#check @Erdos357Upper.canon_le_n
#check @Erdos357Upper.chain
#check @Erdos357Upper.exists_beyond
#check @Erdos357Upper.main_count
#check @Erdos357Upper.consecutive_run
#check @Erdos357Upper.pattern_false_gen
#check @Erdos357Upper.pattern_hit
#check @Erdos357Upper.band_count
#check @Erdos357Upper.list_count
#check @Erdos357Upper.bandsL_ok
#check @Erdos357Upper.bandsL_fib
#check @Erdos357Upper.design_count
#check @Erdos357Upper.adm_bound4

-- Theorem 2 (lower bound) and the mod-42 construction.
#check @Erdos357.Skip.skip_lower
#check @Erdos357.Skip.skip_lower_all
#check @Erdos357.Skip.skip_lower_real_large
#check @Erdos357.Skip.skip_lower_real
#print Erdos357.Skip.sk
#check @Erdos357.Skip.skip_admissible
#check @Erdos357.Skip.distinct_skip
#check @Erdos357.Skip.collision_pair
#check @Erdos357.Skip.phase_filter
#check @Erdos357.Skip.nres_sum
#check @Erdos357.Skip.harm_le
#check @Erdos357.Skip.exists_good
#check @Erdos357.mod42_lower
#check @Erdos357.mod42_lower_all
#check @Erdos357.mod42_lower_real
#check @Erdos357.Mod42.int_admissible
#check @Erdos357.Mod42.length_certificate
#check @Erdos357.Mod42.block_length_eq
#check @Erdos357.mod22_lower_real

-- Supporting results mentioned in the paper.
#check @Erdos357.hasDistinctSums_iff_no_ordered_collision
#check @Erdos357.infinite_set_lower_density
#check @Erdos357.jitter42_lower

#print axioms Erdos357Upper.f_le_upper4
#print axioms Erdos357Upper.f_le_real4
#print axioms Erdos357Upper.f_le_real2
#print axioms Erdos357Upper.f_le_real
#print axioms Erdos357.f_le_half_add_sqrt
#print axioms Erdos357.Skip.skip_lower
#print axioms Erdos357.Skip.skip_lower_real_large
#print axioms Erdos357.Skip.skip_lower_real
#print axioms Erdos357.mod42_lower
#print axioms Erdos357.mod42_lower_real
#print axioms Erdos357.mod22_lower_real
#print axioms Erdos357.infinite_set_lower_density
#print axioms Erdos357.jitter42_lower
