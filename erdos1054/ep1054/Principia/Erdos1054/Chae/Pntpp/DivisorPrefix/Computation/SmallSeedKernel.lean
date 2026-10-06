/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/SmallSeedKernel.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SubsetBits
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.PrimeWindow

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix.Computation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smallKernelPrimes0 : List ℕ := [101, 103, 107, 109, 113, 127, 131, 137, 139, 149]

theorem smallKernelPrimes0_valid : ∀ p ∈ smallKernelPrimes0, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes1 : List ℕ := [151, 157, 163, 167, 173, 179, 181, 191, 193, 197]

theorem smallKernelPrimes1_valid : ∀ p ∈ smallKernelPrimes1, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes1, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes2 : List ℕ := [199, 211, 223, 227, 229, 233, 239, 241, 251, 257]

theorem smallKernelPrimes2_valid : ∀ p ∈ smallKernelPrimes2, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes2, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes3 : List ℕ := [263, 269, 271, 277, 281, 283, 293, 307, 311, 313]

theorem smallKernelPrimes3_valid : ∀ p ∈ smallKernelPrimes3, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes4 : List ℕ := [317, 331, 337, 347, 349, 353, 359, 367, 373, 379]

theorem smallKernelPrimes4_valid : ∀ p ∈ smallKernelPrimes4, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes5 : List ℕ := [383, 389, 397, 401, 409, 419, 421, 431, 433, 439]

theorem smallKernelPrimes5_valid : ∀ p ∈ smallKernelPrimes5, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes5, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes6 : List ℕ := [443, 449, 457, 461, 463, 467, 479, 487, 491, 499]

theorem smallKernelPrimes6_valid : ∀ p ∈ smallKernelPrimes6, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes7 : List ℕ := [503, 509, 521, 523, 541, 547, 557, 563, 569, 571]

theorem smallKernelPrimes7_valid : ∀ p ∈ smallKernelPrimes7, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes7, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes8 : List ℕ := [577, 587, 593, 599, 601, 607, 613, 617, 619, 631]

theorem smallKernelPrimes8_valid : ∀ p ∈ smallKernelPrimes8, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes8, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes9 : List ℕ := [641, 643, 647, 653, 659, 661, 673, 677, 683, 691]

theorem smallKernelPrimes9_valid : ∀ p ∈ smallKernelPrimes9, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes9, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes10 : List ℕ := [701, 709, 719, 727, 733, 739, 743, 751, 757, 761]

theorem smallKernelPrimes10_valid : ∀ p ∈ smallKernelPrimes10, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes10, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes11 : List ℕ := [769, 773, 787, 797, 809, 811, 821, 823, 827, 829]

theorem smallKernelPrimes11_valid : ∀ p ∈ smallKernelPrimes11, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes11, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes12 : List ℕ := [839, 853, 857, 859, 863, 877, 881, 883, 887, 907]

theorem smallKernelPrimes12_valid : ∀ p ∈ smallKernelPrimes12, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes12, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes13 : List ℕ := [911, 919, 929, 937, 941, 947, 953, 967, 971, 977]

theorem smallKernelPrimes13_valid : ∀ p ∈ smallKernelPrimes13, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes13, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes14 : List ℕ := [983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039]

theorem smallKernelPrimes14_valid : ∀ p ∈ smallKernelPrimes14, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes14, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes15 : List ℕ := [1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103]

theorem smallKernelPrimes15_valid : ∀ p ∈ smallKernelPrimes15, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes15, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes16 : List ℕ := [1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187]

theorem smallKernelPrimes16_valid : ∀ p ∈ smallKernelPrimes16, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes16, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes17 : List ℕ := [1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259]

theorem smallKernelPrimes17_valid : ∀ p ∈ smallKernelPrimes17, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes17, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes18 : List ℕ := [1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319]

theorem smallKernelPrimes18_valid : ∀ p ∈ smallKernelPrimes18, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes18, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes19 : List ℕ := [1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427]

theorem smallKernelPrimes19_valid : ∀ p ∈ smallKernelPrimes19, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes19, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes20 : List ℕ := [1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483]

theorem smallKernelPrimes20_valid : ∀ p ∈ smallKernelPrimes20, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes20, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes21 : List ℕ := [1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553]

theorem smallKernelPrimes21_valid : ∀ p ∈ smallKernelPrimes21, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes21, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes22 : List ℕ := [1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613]

theorem smallKernelPrimes22_valid : ∀ p ∈ smallKernelPrimes22, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes22, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes23 : List ℕ := [1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697]

theorem smallKernelPrimes23_valid : ∀ p ∈ smallKernelPrimes23, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes23, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes24 : List ℕ := [1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777]

theorem smallKernelPrimes24_valid : ∀ p ∈ smallKernelPrimes24, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes24, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes25 : List ℕ := [1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867]

theorem smallKernelPrimes25_valid : ∀ p ∈ smallKernelPrimes25, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes25, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes26 : List ℕ := [1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933]

theorem smallKernelPrimes26_valid : ∀ p ∈ smallKernelPrimes26, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes26, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes27 : List ℕ := [1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011]

theorem smallKernelPrimes27_valid : ∀ p ∈ smallKernelPrimes27, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes27, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes28 : List ℕ := [2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087]

theorem smallKernelPrimes28_valid : ∀ p ∈ smallKernelPrimes28, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes28, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes29 : List ℕ := [2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153]

theorem smallKernelPrimes29_valid : ∀ p ∈ smallKernelPrimes29, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes29, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes30 : List ℕ := [2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251]

theorem smallKernelPrimes30_valid : ∀ p ∈ smallKernelPrimes30, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes30, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes31 : List ℕ := [2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333]

theorem smallKernelPrimes31_valid : ∀ p ∈ smallKernelPrimes31, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes31, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes32 : List ℕ := [2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389]

theorem smallKernelPrimes32_valid : ∀ p ∈ smallKernelPrimes32, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes32, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes33 : List ℕ := [2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467]

theorem smallKernelPrimes33_valid : ∀ p ∈ smallKernelPrimes33, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes33, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes34 : List ℕ := [2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557]

theorem smallKernelPrimes34_valid : ∀ p ∈ smallKernelPrimes34, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes34, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes35 : List ℕ := [2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659]

theorem smallKernelPrimes35_valid : ∀ p ∈ smallKernelPrimes35, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes35, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes36 : List ℕ := [2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711]

theorem smallKernelPrimes36_valid : ∀ p ∈ smallKernelPrimes36, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes36, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes37 : List ℕ := [2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789]

theorem smallKernelPrimes37_valid : ∀ p ∈ smallKernelPrimes37, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes37, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes38 : List ℕ := [2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857]

theorem smallKernelPrimes38_valid : ∀ p ∈ smallKernelPrimes38, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes38, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes39 : List ℕ := [2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953]

theorem smallKernelPrimes39_valid : ∀ p ∈ smallKernelPrimes39, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes39, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes40 : List ℕ := [2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037]

theorem smallKernelPrimes40_valid : ∀ p ∈ smallKernelPrimes40, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes40, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes41 : List ℕ := [3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121]

theorem smallKernelPrimes41_valid : ∀ p ∈ smallKernelPrimes41, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes41, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes42 : List ℕ := [3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217]

theorem smallKernelPrimes42_valid : ∀ p ∈ smallKernelPrimes42, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes42, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def smallKernelPrimes43 : List ℕ := [3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299]

theorem smallKernelPrimes43_valid : ∀ p ∈ smallKernelPrimes43, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  intro p hp
  simp only [smallKernelPrimes43, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Explicit prime witnesses, independently checked by the kernel. -/
def smallKernelPrimes : List ℕ :=
  smallKernelPrimes0 ++
  smallKernelPrimes1 ++
  smallKernelPrimes2 ++
  smallKernelPrimes3 ++
  smallKernelPrimes4 ++
  smallKernelPrimes5 ++
  smallKernelPrimes6 ++
  smallKernelPrimes7 ++
  smallKernelPrimes8 ++
  smallKernelPrimes9 ++
  smallKernelPrimes10 ++
  smallKernelPrimes11 ++
  smallKernelPrimes12 ++
  smallKernelPrimes13 ++
  smallKernelPrimes14 ++
  smallKernelPrimes15 ++
  smallKernelPrimes16 ++
  smallKernelPrimes17 ++
  smallKernelPrimes18 ++
  smallKernelPrimes19 ++
  smallKernelPrimes20 ++
  smallKernelPrimes21 ++
  smallKernelPrimes22 ++
  smallKernelPrimes23 ++
  smallKernelPrimes24 ++
  smallKernelPrimes25 ++
  smallKernelPrimes26 ++
  smallKernelPrimes27 ++
  smallKernelPrimes28 ++
  smallKernelPrimes29 ++
  smallKernelPrimes30 ++
  smallKernelPrimes31 ++
  smallKernelPrimes32 ++
  smallKernelPrimes33 ++
  smallKernelPrimes34 ++
  smallKernelPrimes35 ++
  smallKernelPrimes36 ++
  smallKernelPrimes37 ++
  smallKernelPrimes38 ++
  smallKernelPrimes39 ++
  smallKernelPrimes40 ++
  smallKernelPrimes41 ++
  smallKernelPrimes42 ++
  smallKernelPrimes43

theorem smallKernelPrimes_nodup : smallKernelPrimes.Nodup := by
  exact List.SortedLT.nodup (show smallKernelPrimes.SortedLT by decide +kernel)

theorem smallKernelPrimes_valid : ∀ p ∈ smallKernelPrimes, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
  simp only [smallKernelPrimes, List.forall_mem_append, and_assoc]
  exact ⟨smallKernelPrimes0_valid,
    smallKernelPrimes1_valid,
    smallKernelPrimes2_valid,
    smallKernelPrimes3_valid,
    smallKernelPrimes4_valid,
    smallKernelPrimes5_valid,
    smallKernelPrimes6_valid,
    smallKernelPrimes7_valid,
    smallKernelPrimes8_valid,
    smallKernelPrimes9_valid,
    smallKernelPrimes10_valid,
    smallKernelPrimes11_valid,
    smallKernelPrimes12_valid,
    smallKernelPrimes13_valid,
    smallKernelPrimes14_valid,
    smallKernelPrimes15_valid,
    smallKernelPrimes16_valid,
    smallKernelPrimes17_valid,
    smallKernelPrimes18_valid,
    smallKernelPrimes19_valid,
    smallKernelPrimes20_valid,
    smallKernelPrimes21_valid,
    smallKernelPrimes22_valid,
    smallKernelPrimes23_valid,
    smallKernelPrimes24_valid,
    smallKernelPrimes25_valid,
    smallKernelPrimes26_valid,
    smallKernelPrimes27_valid,
    smallKernelPrimes28_valid,
    smallKernelPrimes29_valid,
    smallKernelPrimes30_valid,
    smallKernelPrimes31_valid,
    smallKernelPrimes32_valid,
    smallKernelPrimes33_valid,
    smallKernelPrimes34_valid,
    smallKernelPrimes35_valid,
    smallKernelPrimes36_valid,
    smallKernelPrimes37_valid,
    smallKernelPrimes38_valid,
    smallKernelPrimes39_valid,
    smallKernelPrimes40_valid,
    smallKernelPrimes41_valid,
    smallKernelPrimes42_valid,
    smallKernelPrimes43_valid⟩

theorem smallKernelPrimes_coverage :
    subsetBitsCover 469614 334 469614 smallKernelPrimes := by
  decide +kernel

/-- A small prime window replaces nearly all of the original finite Bq search. -/
theorem smallKernel_representation :
    ∀ n, 335 ≤ n → n ≤ 469615 → Represents n := by
  intro n hlo hhi
  have hn := subsetBits_interval (limit := 469614) (lo := 334) (hi := 469614)
    (ps := smallKernelPrimes) smallKernelPrimes_nodup smallKernelPrimes_coverage
    (n - 1) (by omega) (by omega)
  have hv : ∀ p ∈ smallKernelPrimes.toFinset, p.Prime ∧ 100 < p ∧ p ≤ 3300 := by
    simpa using smallKernelPrimes_valid
  have hr := represents_succ_of_subsetSum_prime_window
    smallKernelPrimes.toFinset 100 3300 (n - 1)
    (fun p hp => (hv p hp).1) (fun p hp => (hv p hp).2.1)
    (fun p hp => (hv p hp).2.2) (by norm_num) hn
  simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hr

end Pntpp.DivisorPrefix.Computation
