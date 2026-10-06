/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/LargeSeedKernel.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SubsetBits
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.LargeSeed

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def largeKernelPrimes0 : List ℕ :=
  [20013883, 20028257, 20040329, 20103091, 20114821,
    20126671, 20147021, 20162027, 20177749, 20183239]

theorem largeKernelPrimes0_valid :
    ∀ p ∈ largeKernelPrimes0, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes1 : List ℕ :=
  [20188261, 20193037, 20212421, 20217409, 20244551,
    20245439, 20250869, 20266661, 20272309, 20290909]

theorem largeKernelPrimes1_valid :
    ∀ p ∈ largeKernelPrimes1, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes1, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes2 : List ℕ :=
  [20304983, 20313437, 20316577, 20321071, 20331263,
    20336149, 20352047, 20359487, 20365271, 20377087]

theorem largeKernelPrimes2_valid :
    ∀ p ∈ largeKernelPrimes2, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes3 : List ℕ :=
  [20380831, 20384603, 20401973, 20419753, 20421241,
    20426309, 20438051, 20448317, 20453683, 20457029]

theorem largeKernelPrimes3_valid :
    ∀ p ∈ largeKernelPrimes3, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes4 : List ℕ :=
  [20461631, 20473331, 20483279, 20490601, 20492377,
    20493371, 20506921, 20519281, 20537947, 20539609]

theorem largeKernelPrimes4_valid :
    ∀ p ∈ largeKernelPrimes4, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes5 : List ℕ :=
  [20543321, 20545097, 20550253, 20567203, 20572507,
    20595889, 20602019, 20618639, 20625421, 20628761]

theorem largeKernelPrimes5_valid :
    ∀ p ∈ largeKernelPrimes5, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes5, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes6 : List ℕ :=
  [20638819, 20665969, 20702329, 20722297, 20723503,
    20736337, 20745629, 20749681, 20752469, 20781349]

theorem largeKernelPrimes6_valid :
    ∀ p ∈ largeKernelPrimes6, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes7 : List ℕ :=
  [20788177, 20815037, 20835743, 20841871, 20870371,
    20870389, 20882567, 20882857, 20895139, 20897609]

theorem largeKernelPrimes7_valid :
    ∀ p ∈ largeKernelPrimes7, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes7, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes8 : List ℕ :=
  [20906201, 20921501, 20944291, 20947793, 20952161,
    20960689, 20966369, 20976343, 20997523, 21016753]

theorem largeKernelPrimes8_valid :
    ∀ p ∈ largeKernelPrimes8, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes8, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes9 : List ℕ :=
  [21047827, 21048641, 21048829, 21066823, 21067441,
    21069421, 21090439, 21097513, 21101027, 21129293]

theorem largeKernelPrimes9_valid :
    ∀ p ∈ largeKernelPrimes9, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes9, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes10 : List ℕ :=
  [21182741, 21243331, 21313829, 21393961, 21464459,
    21502001, 21580051, 21774847, 21965981, 22023481]

theorem largeKernelPrimes10_valid :
    ∀ p ∈ largeKernelPrimes10, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes10, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes11 : List ℕ :=
  [22151977, 22170013, 22265351, 22299601, 22390279,
    22444243, 22544189, 22974073, 23074297, 23126977]

theorem largeKernelPrimes11_valid :
    ∀ p ∈ largeKernelPrimes11, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes11, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes12 : List ℕ :=
  [23230631, 23313079, 23313691, 23406833, 23456309,
    23533327, 23560291, 23801171, 23945371, 24025951]

theorem largeKernelPrimes12_valid :
    ∀ p ∈ largeKernelPrimes12, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes12, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes13 : List ℕ :=
  [24075563, 24389693, 24445807, 24562361, 24878717,
    24944081, 25448989, 25747343, 25876969, 26032621]

theorem largeKernelPrimes13_valid :
    ∀ p ∈ largeKernelPrimes13, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes13, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes14 : List ℕ :=
  [26182463, 26316523, 26416781, 26830757, 26878693,
    26918963, 26945543, 27047477, 27083843, 27445109]

theorem largeKernelPrimes14_valid :
    ∀ p ∈ largeKernelPrimes14, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes14, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes15 : List ℕ :=
  [27607669, 27619147, 27696569, 27850793, 27860849,
    27868369, 27953641, 28035149, 28183153, 28344871]

theorem largeKernelPrimes15_valid :
    ∀ p ∈ largeKernelPrimes15, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes15, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes16 : List ℕ :=
  [28495351, 28656983, 28750031, 28808249, 28816877,
    29081093, 29126939, 29322299, 29414617, 29415961]

theorem largeKernelPrimes16_valid :
    ∀ p ∈ largeKernelPrimes16, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes16, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes17 : List ℕ :=
  [29540261, 29593643, 29672141, 29676943, 29825933,
    29850523, 29894531, 30084533, 30114173, 30212333]

theorem largeKernelPrimes17_valid :
    ∀ p ∈ largeKernelPrimes17, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes17, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes18 : List ℕ :=
  [30233363, 30396511, 30426271, 30509357, 30563363,
    30599809, 30663749, 30704717, 30710809, 31075027]

theorem largeKernelPrimes18_valid :
    ∀ p ∈ largeKernelPrimes18, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes18, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes19 : List ℕ :=
  [31127777, 31177093, 31251403, 31260847, 31275967,
    31643159, 31646033, 32083397, 32253281, 32614471]

theorem largeKernelPrimes19_valid :
    ∀ p ∈ largeKernelPrimes19, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes19, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes20 : List ℕ :=
  [32940629, 33083929, 33115997, 33161533, 33306731,
    33359881, 33435053, 33765547, 33995839, 34114499]

theorem largeKernelPrimes20_valid :
    ∀ p ∈ largeKernelPrimes20, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes20, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes21 : List ℕ :=
  [34125649, 34234517, 34318247, 34384303, 34391261,
    34412129, 34469389, 34691519, 34698113, 34718993]

theorem largeKernelPrimes21_valid :
    ∀ p ∈ largeKernelPrimes21, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes21, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes22 : List ℕ :=
  [35121883, 35123167, 35203633, 35258633, 35452873,
    35473957, 35738797, 35770481, 35773643, 36045203]

theorem largeKernelPrimes22_valid :
    ∀ p ∈ largeKernelPrimes22, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes22, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes23 : List ℕ :=
  [36163591, 36248627, 36281797, 36392437, 36514433,
    36516439, 36699347, 36807413, 36994597, 37013443]

theorem largeKernelPrimes23_valid :
    ∀ p ∈ largeKernelPrimes23, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes23, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes24 : List ℕ :=
  [37015549, 37027301, 37596001, 37747013, 37765573,
    37896641, 38060549, 38139253, 38140511, 38176753]

theorem largeKernelPrimes24_valid :
    ∀ p ∈ largeKernelPrimes24, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes24, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes25 : List ℕ :=
  [38239217, 38301281, 38338373, 38398727, 38478359,
    38529047, 38635447, 38724349, 38755303, 38931419]

theorem largeKernelPrimes25_valid :
    ∀ p ∈ largeKernelPrimes25, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes25, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes26 : List ℕ :=
  [38999579, 39129661, 39134761, 39152219, 39218449,
    39285511, 39376511, 39384151, 39418439, 39436939]

theorem largeKernelPrimes26_valid :
    ∀ p ∈ largeKernelPrimes26, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes26, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

def largeKernelPrimes27 : List ℕ :=
  [39488893, 39502963, 39538663, 39617177, 39657829,
    39766127, 39777817, 39807643, 39869701, 39940841]

theorem largeKernelPrimes27_valid :
    ∀ p ∈ largeKernelPrimes27, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  intro p hp
  simp only [largeKernelPrimes27, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact ⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, by decide, by decide⟩

/-- A compact certified seed; two fresh primes extend its covered interval. -/
def largeKernelPrimes : List ℕ :=
  largeKernelPrimes0 ++
  largeKernelPrimes1 ++
  largeKernelPrimes2 ++
  largeKernelPrimes3 ++
  largeKernelPrimes4 ++
  largeKernelPrimes5 ++
  largeKernelPrimes6 ++
  largeKernelPrimes7 ++
  largeKernelPrimes8 ++
  largeKernelPrimes9 ++
  largeKernelPrimes10 ++
  largeKernelPrimes11 ++
  largeKernelPrimes12 ++
  largeKernelPrimes13 ++
  largeKernelPrimes14 ++
  largeKernelPrimes15 ++
  largeKernelPrimes16 ++
  largeKernelPrimes17 ++
  largeKernelPrimes18 ++
  largeKernelPrimes19 ++
  largeKernelPrimes20 ++
  largeKernelPrimes21 ++
  largeKernelPrimes22 ++
  largeKernelPrimes23 ++
  largeKernelPrimes24 ++
  largeKernelPrimes25 ++
  largeKernelPrimes26 ++
  largeKernelPrimes27

theorem largeKernelPrimes_nodup : largeKernelPrimes.Nodup := by
  exact List.SortedLT.nodup (show largeKernelPrimes.SortedLT by decide +kernel)

theorem largeKernelPrimes_valid :
    ∀ p ∈ largeKernelPrimes, p.Prime ∧ 20000000 < p ∧ p ≤ 40000000 := by
  simp only [largeKernelPrimes, List.forall_mem_append, and_assoc]
  exact ⟨largeKernelPrimes0_valid,
    largeKernelPrimes1_valid,
    largeKernelPrimes2_valid,
    largeKernelPrimes3_valid,
    largeKernelPrimes4_valid,
    largeKernelPrimes5_valid,
    largeKernelPrimes6_valid,
    largeKernelPrimes7_valid,
    largeKernelPrimes8_valid,
    largeKernelPrimes9_valid,
    largeKernelPrimes10_valid,
    largeKernelPrimes11_valid,
    largeKernelPrimes12_valid,
    largeKernelPrimes13_valid,
    largeKernelPrimes14_valid,
    largeKernelPrimes15_valid,
    largeKernelPrimes16_valid,
    largeKernelPrimes17_valid,
    largeKernelPrimes18_valid,
    largeKernelPrimes19_valid,
    largeKernelPrimes20_valid,
    largeKernelPrimes21_valid,
    largeKernelPrimes22_valid,
    largeKernelPrimes23_valid,
    largeKernelPrimes24_valid,
    largeKernelPrimes25_valid,
    largeKernelPrimes26_valid,
    largeKernelPrimes27_valid⟩

/-- The shorter bitset reduces independent-kernel replay memory. -/
theorem largeKernelPrimes_coverage :
    subsetBitsCover 125000003 105000000 125000003 largeKernelPrimes := by
  decide +kernel

theorem largeKernelPrimes_initial :
    ∀ n, 105000000 ≤ n → n ≤ 125000003 → IsSubsetSum largeKernelPrimes.toFinset n :=
  subsetBits_interval (limit := 125000003) (lo := 105000000) (hi := 125000003)
    (ps := largeKernelPrimes) largeKernelPrimes_nodup largeKernelPrimes_coverage

private theorem fresh_three : 20000003 ∉ largeKernelPrimes.toFinset := by
  rw [List.mem_toFinset]
  decide +kernel

private theorem fresh_thirty_three :
    20000033 ∉ insert 20000003 largeKernelPrimes.toFinset := by
  simp only [Finset.mem_insert, List.mem_toFinset]
  decide +kernel

/-- The same complete large-seed interval as the original certificate. -/
theorem largeSeedGenerated_full :
    ∀ n, largeSeedStart ≤ n → n ≤ largeSeedEnd → IsSubsetSum largeSeedPrimeWindow n := by
  have h₁ := subsetSum_interval_extension
    (A := largeKernelPrimes.toFinset) (C := 105000000) (U := 125000003) (p := 20000003)
    (by decide) fresh_three largeKernelPrimes_initial (by decide)
  have h₂ := subsetSum_interval_extension
    (A := insert 20000003 largeKernelPrimes.toFinset)
    (C := 105000000) (U := 125000003 + 20000003) (p := 20000033)
    (by decide) fresh_thirty_three h₁ (by decide)
  intro n hlo hhi
  obtain ⟨s, hs, hsum⟩ := h₂ n hlo (by change n ≤ 165000039; change n ≤ 156000000 at hhi; omega)
  refine ⟨s, ?_, hsum⟩
  intro p hp
  have hpA := hs hp
  simp only [Finset.mem_insert, List.mem_toFinset] at hpA
  rcases hpA with rfl | rfl | hpA
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by decide, by decide⟩,
      Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by decide, by decide⟩,
      Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩⟩
  · obtain ⟨hpPrime, hpLower, hpUpper⟩ := largeKernelPrimes_valid p hpA
    have hpNe : p ≠ 40000000 := by
      intro heq
      subst p
      norm_num at hpPrime
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hpLower, by
      change p < 40000000
      omega⟩, hpPrime⟩

end Pntpp.DivisorPrefix.Computation
