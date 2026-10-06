/-
Copyright (c) 2026 PrincipiaAI. Released under the Apache License, Version 2.0.
Audit script only: the declarations it names are Hyunsik Chae's (ported).
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindow
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks0
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks1
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks10
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks2
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks3
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks4
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks5
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks6
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks7
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks8
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowChecks9
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowCore
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.FirstWindowData
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.LargeSeed
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.LargeSeedKernel
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SmallBq
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SmallSeedKernel
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Computation.SubsetBits

set_option autoImplicit false

/-!
# Axiom gate for `Principia/Erdos1054/Chae/Pntpp/DivisorPrefix/Computation/`

Every public theorem of the ported files in this directory (302 declarations), one `#print axioms` each. Acceptance: each reads
`[propext, Classical.choice, Quot.sound]` or a subset. Private helpers are not addressable
from a gate; their axioms appear in the footprints of the public theorems that use them.
-/

-- FirstWindow.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindow_subsetSum_coverage

-- FirstWindowChecks.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_prime
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMaskChunk_sizes
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMaskChunks_valid

-- FirstWindowChecks0.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime0
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime1
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime2
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime3
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime4
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime5
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime6
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime7
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime8
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime9
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks0_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks1_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks2_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks3_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks4_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks5_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks6_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks7_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks8_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks9_valid

-- FirstWindowChecks1.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime10
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime11
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime12
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime13
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime14
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime15
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime16
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime17
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime18
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime19
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks10_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks11_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks12_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks13_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks14_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks15_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks16_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks17_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks18_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks19_valid

-- FirstWindowChecks10.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks100_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks101_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks102_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks103_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks104_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks105_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks106_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks107_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks108_valid

-- FirstWindowChecks2.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime20
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime21
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime22
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime23
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime24
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime25
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime26
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime27
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime28
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime29
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks20_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks21_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks22_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks23_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks24_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks25_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks26_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks27_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks28_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks29_valid

-- FirstWindowChecks3.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime30
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime31
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime32
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime33
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime34
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime35
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime36
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime37
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime38
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime39
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks30_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks31_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks32_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks33_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks34_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks35_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks36_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks37_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks38_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks39_valid

-- FirstWindowChecks4.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime40
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime41
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime42
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime43
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime44
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime45
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime46
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime47
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime48
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime49
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks40_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks41_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks42_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks43_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks44_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks45_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks46_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks47_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks48_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks49_valid

-- FirstWindowChecks5.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime50
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime51
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime52
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime53
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime54
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime55
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime56
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime57
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime58
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime59
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks50_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks51_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks52_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks53_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks54_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks55_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks56_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks57_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks58_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks59_valid

-- FirstWindowChecks6.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime60
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime61
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime62
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime63
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime64
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime65
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime66
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime67
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime68
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime69
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks60_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks61_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks62_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks63_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks64_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks65_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks66_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks67_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks68_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks69_valid

-- FirstWindowChecks7.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime70
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime71
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime72
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime73
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime74
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime75
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime76
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime77
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime78
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime79
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks70_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks71_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks72_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks73_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks74_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks75_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks76_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks77_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks78_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks79_valid

-- FirstWindowChecks8.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime80
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime81
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime82
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime83
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime84
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime85
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime86
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime87
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime88
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime89
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks80_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks81_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks82_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks83_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks84_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks85_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks86_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks87_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks88_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks89_valid

-- FirstWindowChecks9.lean
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime90
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime91
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime92
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime93
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks90_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks91_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks92_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks93_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks94_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks95_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks96_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks97_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks98_valid
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowMasks99_valid

-- FirstWindowCore.lean
#print axioms Pntpp.DivisorPrefix.Computation.maskFinset_subset_toFinset
#print axioms Pntpp.DivisorPrefix.Computation.sum_maskFinset
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_nodup
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_length
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_lower
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_upper
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowSeed_sorted
#print axioms Pntpp.DivisorPrefix.Computation.firstWindowPrime_card

-- FirstWindowData.lean

-- LargeSeed.lean
#print axioms Pntpp.DivisorPrefix.Computation.sum_toFinset_eq_sum

-- LargeSeedKernel.lean
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes0_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes1_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes2_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes3_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes4_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes5_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes6_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes7_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes8_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes9_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes10_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes11_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes12_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes13_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes14_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes15_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes16_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes17_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes18_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes19_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes20_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes21_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes22_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes23_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes24_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes25_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes26_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes27_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes_nodup
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes_valid
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes_coverage
#print axioms Pntpp.DivisorPrefix.Computation.largeKernelPrimes_initial
#print axioms Pntpp.DivisorPrefix.Computation.largeSeedGenerated_full

-- SmallBq.lean
#print axioms Pntpp.DivisorPrefix.Computation.SmallBqWitness.represents
#print axioms Pntpp.DivisorPrefix.Computation.tinyBq_representation
#print axioms Pntpp.DivisorPrefix.Computation.smallBq_representation

-- SmallSeedKernel.lean
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes0_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes1_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes2_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes3_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes4_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes5_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes6_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes7_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes8_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes9_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes10_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes11_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes12_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes13_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes14_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes15_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes16_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes17_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes18_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes19_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes20_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes21_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes22_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes23_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes24_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes25_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes26_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes27_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes28_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes29_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes30_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes31_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes32_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes33_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes34_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes35_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes36_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes37_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes38_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes39_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes40_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes41_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes42_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes43_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes_nodup
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes_valid
#print axioms Pntpp.DivisorPrefix.Computation.smallKernelPrimes_coverage
#print axioms Pntpp.DivisorPrefix.Computation.smallKernel_representation

-- SubsetBits.lean
#print axioms Pntpp.DivisorPrefix.Computation.subsetBits_sound
#print axioms Pntpp.DivisorPrefix.Computation.subsetBits_interval
