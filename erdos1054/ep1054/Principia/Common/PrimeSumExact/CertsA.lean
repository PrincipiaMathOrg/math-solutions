/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PrimeSumExact.Sieve
import Principia.Common.PrimeSumExact.SmallPrimes

set_option autoImplicit false

/-!
# Segment certificates for the primes of `(10883, 98999987]`, part A (segments 0–46)

Each theorem is one `decide +kernel` evaluation of `segSum 20 W lo primesTo9949` (a segmented
sieve plus a weighted popcount, `PrimeSumExact/Sieve.lean`) on a segment `[lo, lo + W)` of width
`W = 2^20` (the last segment has width `422960`). Measured on the pinned toolchain: about 2 s of
kernel time and 1.3 GB peak per segment. `segSum_eq` identifies each value with the sum of the
primes of its segment; `PrimeSumExact/Window.lean` chains them.
-/

namespace Principia.Common.PrimeSumExact

theorem seg_window1_00 : segSum 20 1048576 10884 primesTo9949 = 41969259156 := by
  decide +kernel

theorem seg_window1_01 : segSum 20 1048576 1059460 primesTo9949 = 116210427596 := by
  decide +kernel

theorem seg_window1_02 : segSum 20 1048576 2108036 primesTo9949 = 186544369850 := by
  decide +kernel

theorem seg_window1_03 : segSum 20 1048576 3156612 primesTo9949 = 255218746741 := by
  decide +kernel

theorem seg_window1_04 : segSum 20 1048576 4205188 primesTo9949 = 322836345939 := by
  decide +kernel

theorem seg_window1_05 : segSum 20 1048576 5253764 primesTo9949 = 388826182261 := by
  decide +kernel

theorem seg_window1_06 : segSum 20 1048576 6302340 primesTo9949 = 454771530473 := by
  decide +kernel

theorem seg_window1_07 : segSum 20 1048576 7350916 primesTo9949 = 519677994127 := by
  decide +kernel

theorem seg_window1_08 : segSum 20 1048576 8399492 primesTo9949 = 584575078603 := by
  decide +kernel

theorem seg_window1_09 : segSum 20 1048576 9448068 primesTo9949 = 648563859586 := by
  decide +kernel

theorem seg_window1_10 : segSum 20 1048576 10496644 primesTo9949 = 712973860590 := by
  decide +kernel

theorem seg_window1_11 : segSum 20 1048576 11545220 primesTo9949 = 776340438066 := by
  decide +kernel

theorem seg_window1_12 : segSum 20 1048576 12593796 primesTo9949 = 838095786348 := by
  decide +kernel

theorem seg_window1_13 : segSum 20 1048576 13642372 primesTo9949 = 902447459503 := by
  decide +kernel

theorem seg_window1_14 : segSum 20 1048576 14690948 primesTo9949 = 964353548419 := by
  decide +kernel

theorem seg_window1_15 : segSum 20 1048576 15739524 primesTo9949 = 1026465069858 := by
  decide +kernel

theorem seg_window1_16 : segSum 20 1048576 16788100 primesTo9949 = 1090661147970 := by
  decide +kernel

theorem seg_window1_17 : segSum 20 1048576 17836676 primesTo9949 = 1150919871070 := by
  decide +kernel

theorem seg_window1_18 : segSum 20 1048576 18885252 primesTo9949 = 1212270913183 := by
  decide +kernel

theorem seg_window1_19 : segSum 20 1048576 19933828 primesTo9949 = 1273518327023 := by
  decide +kernel

theorem seg_window1_20 : segSum 20 1048576 20982404 primesTo9949 = 1337805033799 := by
  decide +kernel

theorem seg_window1_21 : segSum 20 1048576 22030980 primesTo9949 = 1395298682070 := by
  decide +kernel

theorem seg_window1_22 : segSum 20 1048576 23079556 primesTo9949 = 1455181535457 := by
  decide +kernel

theorem seg_window1_23 : segSum 20 1048576 24128132 primesTo9949 = 1520537801778 := by
  decide +kernel

theorem seg_window1_24 : segSum 20 1048576 25176708 primesTo9949 = 1578178784106 := by
  decide +kernel

theorem seg_window1_25 : segSum 20 1048576 26225284 primesTo9949 = 1640552617025 := by
  decide +kernel

theorem seg_window1_26 : segSum 20 1048576 27273860 primesTo9949 = 1702790015915 := by
  decide +kernel

theorem seg_window1_27 : segSum 20 1048576 28322436 primesTo9949 = 1758837524979 := by
  decide +kernel

theorem seg_window1_28 : segSum 20 1048576 29371012 primesTo9949 = 1825696797958 := by
  decide +kernel

theorem seg_window1_29 : segSum 20 1048576 30419588 primesTo9949 = 1877673176387 := by
  decide +kernel

theorem seg_window1_30 : segSum 20 1048576 31468164 primesTo9949 = 1941889095776 := by
  decide +kernel

theorem seg_window1_31 : segSum 20 1048576 32516740 primesTo9949 = 2002876172432 := by
  decide +kernel

theorem seg_window1_32 : segSum 20 1048576 33565316 primesTo9949 = 2053879558812 := by
  decide +kernel

theorem seg_window1_33 : segSum 20 1048576 34613892 primesTo9949 = 2119110533123 := by
  decide +kernel

theorem seg_window1_34 : segSum 20 1048576 35662468 primesTo9949 = 2178604423475 := by
  decide +kernel

theorem seg_window1_35 : segSum 20 1048576 36711044 primesTo9949 = 2240114986179 := by
  decide +kernel

theorem seg_window1_36 : segSum 20 1048576 37759620 primesTo9949 = 2303532394689 := by
  decide +kernel

theorem seg_window1_37 : segSum 20 1048576 38808196 primesTo9949 = 2363945087582 := by
  decide +kernel

theorem seg_window1_38 : segSum 20 1048576 39856772 primesTo9949 = 2417105323939 := by
  decide +kernel

theorem seg_window1_39 : segSum 20 1048576 40905348 primesTo9949 = 2471849404568 := by
  decide +kernel

theorem seg_window1_40 : segSum 20 1048576 41953924 primesTo9949 = 2533151154179 := by
  decide +kernel

theorem seg_window1_41 : segSum 20 1048576 43002500 primesTo9949 = 2594549148900 := by
  decide +kernel

theorem seg_window1_42 : segSum 20 1048576 44051076 primesTo9949 = 2655966294743 := by
  decide +kernel

theorem seg_window1_43 : segSum 20 1048576 45099652 primesTo9949 = 2716991998491 := by
  decide +kernel

theorem seg_window1_44 : segSum 20 1048576 46148228 primesTo9949 = 2771933474707 := by
  decide +kernel

theorem seg_window1_45 : segSum 20 1048576 47196804 primesTo9949 = 2820853065628 := by
  decide +kernel

theorem seg_window1_46 : segSum 20 1048576 48245380 primesTo9949 = 2888722504888 := by
  decide +kernel

end Principia.Common.PrimeSumExact
