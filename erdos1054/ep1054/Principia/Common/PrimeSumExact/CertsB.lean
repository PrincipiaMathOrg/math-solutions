/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PrimeSumExact.Sieve
import Principia.Common.PrimeSumExact.SmallPrimes

set_option autoImplicit false

/-!
# Segment certificates for the primes of `(10883, 98999987]`, part B (segments 47–93 and the last)

Each theorem is one `decide +kernel` evaluation of `segSum 20 W lo primesTo9949` (a segmented
sieve plus a weighted popcount, `PrimeSumExact/Sieve.lean`) on a segment `[lo, lo + W)` of width
`W = 2^20` (the last segment has width `422960`). Measured on the pinned toolchain: about 2 s of
kernel time and 1.3 GB peak per segment. `segSum_eq` identifies each value with the sum of the
primes of its segment; `PrimeSumExact/Window.lean` chains them.
-/

namespace Principia.Common.PrimeSumExact

theorem seg_window1_47 : segSum 20 1048576 49293956 primesTo9949 = 2953391923418 := by
  decide +kernel

theorem seg_window1_48 : segSum 20 1048576 50342532 primesTo9949 = 3005684898893 := by
  decide +kernel

theorem seg_window1_49 : segSum 20 1048576 51391108 primesTo9949 = 3063251801301 := by
  decide +kernel

theorem seg_window1_50 : segSum 20 1048576 52439684 primesTo9949 = 3120763896753 := by
  decide +kernel

theorem seg_window1_51 : segSum 20 1048576 53488260 primesTo9949 = 3175336156913 := by
  decide +kernel

theorem seg_window1_52 : segSum 20 1048576 54536836 primesTo9949 = 3235482053894 := by
  decide +kernel

theorem seg_window1_53 : segSum 20 1048576 55585412 primesTo9949 = 3300586910895 := by
  decide +kernel

theorem seg_window1_54 : segSum 20 1048576 56633988 primesTo9949 = 3363470156786 := by
  decide +kernel

theorem seg_window1_55 : segSum 20 1048576 57682564 primesTo9949 = 3410906706803 := by
  decide +kernel

theorem seg_window1_56 : segSum 20 1048576 58731140 primesTo9949 = 3467731048912 := by
  decide +kernel

theorem seg_window1_57 : segSum 20 1048576 59779716 primesTo9949 = 3534986337981 := by
  decide +kernel

theorem seg_window1_58 : segSum 20 1048576 60828292 primesTo9949 = 3578449409286 := by
  decide +kernel

theorem seg_window1_59 : segSum 20 1048576 61876868 primesTo9949 = 3646158416175 := by
  decide +kernel

theorem seg_window1_60 : segSum 20 1048576 62925444 primesTo9949 = 3709824604716 := by
  decide +kernel

theorem seg_window1_61 : segSum 20 1048576 63974020 primesTo9949 = 3752110923648 := by
  decide +kernel

theorem seg_window1_62 : segSum 20 1048576 65022596 primesTo9949 = 3820702469325 := by
  decide +kernel

theorem seg_window1_63 : segSum 20 1048576 66071172 primesTo9949 = 3881263825370 := by
  decide +kernel

theorem seg_window1_64 : segSum 20 1048576 67119748 primesTo9949 = 3939951634916 := by
  decide +kernel

theorem seg_window1_65 : segSum 20 1048576 68168324 primesTo9949 = 3984910232105 := by
  decide +kernel

theorem seg_window1_66 : segSum 20 1048576 69216900 primesTo9949 = 4053749600350 := by
  decide +kernel

theorem seg_window1_67 : segSum 20 1048576 70265476 primesTo9949 = 4103736608385 := by
  decide +kernel

theorem seg_window1_68 : segSum 20 1048576 71314052 primesTo9949 = 4176422291988 := by
  decide +kernel

theorem seg_window1_69 : segSum 20 1048576 72362628 primesTo9949 = 4215419126977 := by
  decide +kernel

theorem seg_window1_70 : segSum 20 1048576 73411204 primesTo9949 = 4275451876273 := by
  decide +kernel

theorem seg_window1_71 : segSum 20 1048576 74459780 primesTo9949 = 4341258427197 := by
  decide +kernel

theorem seg_window1_72 : segSum 20 1048576 75508356 primesTo9949 = 4390629108199 := by
  decide +kernel

theorem seg_window1_73 : segSum 20 1048576 76556932 primesTo9949 = 4444983769626 := by
  decide +kernel

theorem seg_window1_74 : segSum 20 1048576 77605508 primesTo9949 = 4500265380340 := by
  decide +kernel

theorem seg_window1_75 : segSum 20 1048576 78654084 primesTo9949 = 4562962742855 := by
  decide +kernel

theorem seg_window1_76 : segSum 20 1048576 79702660 primesTo9949 = 4620040150229 := by
  decide +kernel

theorem seg_window1_77 : segSum 20 1048576 80751236 primesTo9949 = 4691133412032 := by
  decide +kernel

theorem seg_window1_78 : segSum 20 1048576 81799812 primesTo9949 = 4740971969277 := by
  decide +kernel

theorem seg_window1_79 : segSum 20 1048576 82848388 primesTo9949 = 4788294636822 := by
  decide +kernel

theorem seg_window1_80 : segSum 20 1048576 83896964 primesTo9949 = 4839331362444 := by
  decide +kernel

theorem seg_window1_81 : segSum 20 1048576 84945540 primesTo9949 = 4908974368729 := by
  decide +kernel

theorem seg_window1_82 : segSum 20 1048576 85994116 primesTo9949 = 4964003691989 := by
  decide +kernel

theorem seg_window1_83 : segSum 20 1048576 87042692 primesTo9949 = 5021672263376 := by
  decide +kernel

theorem seg_window1_84 : segSum 20 1048576 88091268 primesTo9949 = 5075547014364 := by
  decide +kernel

theorem seg_window1_85 : segSum 20 1048576 89139844 primesTo9949 = 5127290191281 := by
  decide +kernel

theorem seg_window1_86 : segSum 20 1048576 90188420 primesTo9949 = 5196669771629 := by
  decide +kernel

theorem seg_window1_87 : segSum 20 1048576 91236996 primesTo9949 = 5245248389318 := by
  decide +kernel

theorem seg_window1_88 : segSum 20 1048576 92285572 primesTo9949 = 5295908957952 := by
  decide +kernel

theorem seg_window1_89 : segSum 20 1048576 93334148 primesTo9949 = 5362882035316 := by
  decide +kernel

theorem seg_window1_90 : segSum 20 1048576 94382724 primesTo9949 = 5428965126267 := by
  decide +kernel

theorem seg_window1_91 : segSum 20 1048576 95431300 primesTo9949 = 5469728438047 := by
  decide +kernel

theorem seg_window1_92 : segSum 20 1048576 96479876 primesTo9949 = 5538849758807 := by
  decide +kernel

theorem seg_window1_93 : segSum 20 1048576 97528452 primesTo9949 = 5592142000670 := by
  decide +kernel

theorem seg_window1_last :
    segSum 20 422960 98577028 primesTo9949 = 2251381631874 := by
  decide +kernel

end Principia.Common.PrimeSumExact
