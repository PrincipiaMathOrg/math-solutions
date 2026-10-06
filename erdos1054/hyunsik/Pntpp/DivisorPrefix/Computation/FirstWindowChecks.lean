import Pntpp.DivisorPrefix.Computation.FirstWindowChecks10

namespace Pntpp.DivisorPrefix.Computation

set_option maxRecDepth 3000

theorem firstWindowSeed_prime :
    ∀ p ∈ firstWindowSeed, p.Prime := by
  simp [firstWindowSeed, firstWindowPrime0, firstWindowPrime1, firstWindowPrime2, firstWindowPrime3, firstWindowPrime4, firstWindowPrime5, firstWindowPrime6, firstWindowPrime7, firstWindowPrime8, firstWindowPrime9, firstWindowPrime10, firstWindowPrime11, firstWindowPrime12, firstWindowPrime13, firstWindowPrime14, firstWindowPrime15, firstWindowPrime16, firstWindowPrime17, firstWindowPrime18, firstWindowPrime19, firstWindowPrime20, firstWindowPrime21, firstWindowPrime22, firstWindowPrime23, firstWindowPrime24, firstWindowPrime25, firstWindowPrime26, firstWindowPrime27, firstWindowPrime28, firstWindowPrime29, firstWindowPrime30, firstWindowPrime31, firstWindowPrime32, firstWindowPrime33, firstWindowPrime34, firstWindowPrime35, firstWindowPrime36, firstWindowPrime37, firstWindowPrime38, firstWindowPrime39, firstWindowPrime40, firstWindowPrime41, firstWindowPrime42, firstWindowPrime43, firstWindowPrime44, firstWindowPrime45, firstWindowPrime46, firstWindowPrime47, firstWindowPrime48, firstWindowPrime49, firstWindowPrime50, firstWindowPrime51, firstWindowPrime52, firstWindowPrime53, firstWindowPrime54, firstWindowPrime55, firstWindowPrime56, firstWindowPrime57, firstWindowPrime58, firstWindowPrime59, firstWindowPrime60, firstWindowPrime61, firstWindowPrime62, firstWindowPrime63, firstWindowPrime64, firstWindowPrime65, firstWindowPrime66, firstWindowPrime67, firstWindowPrime68, firstWindowPrime69, firstWindowPrime70, firstWindowPrime71, firstWindowPrime72, firstWindowPrime73, firstWindowPrime74, firstWindowPrime75, firstWindowPrime76, firstWindowPrime77, firstWindowPrime78, firstWindowPrime79, firstWindowPrime80, firstWindowPrime81, firstWindowPrime82, firstWindowPrime83, firstWindowPrime84, firstWindowPrime85, firstWindowPrime86, firstWindowPrime87, firstWindowPrime88, firstWindowPrime89, firstWindowPrime90, firstWindowPrime91, firstWindowPrime92, firstWindowPrime93]

theorem firstWindowMaskChunk_sizes :
    ∀ j : Fin 109,
      (firstWindowMaskChunk j).size =
        if j.val = 108 then 89 else 100 := by
  intro j
  fin_cases j <;> decide

theorem firstWindowMaskChunks_valid
    (j : Fin 109)
    (i : Fin (firstWindowMaskChunk j).size) :
    maskSum firstWindowSeed (firstWindowMaskChunk j)[i] =
      firstWindowLower + 100 * j + i := by
  fin_cases j
  · exact firstWindowMasks0_valid i
  · exact firstWindowMasks1_valid i
  · exact firstWindowMasks2_valid i
  · exact firstWindowMasks3_valid i
  · exact firstWindowMasks4_valid i
  · exact firstWindowMasks5_valid i
  · exact firstWindowMasks6_valid i
  · exact firstWindowMasks7_valid i
  · exact firstWindowMasks8_valid i
  · exact firstWindowMasks9_valid i
  · exact firstWindowMasks10_valid i
  · exact firstWindowMasks11_valid i
  · exact firstWindowMasks12_valid i
  · exact firstWindowMasks13_valid i
  · exact firstWindowMasks14_valid i
  · exact firstWindowMasks15_valid i
  · exact firstWindowMasks16_valid i
  · exact firstWindowMasks17_valid i
  · exact firstWindowMasks18_valid i
  · exact firstWindowMasks19_valid i
  · exact firstWindowMasks20_valid i
  · exact firstWindowMasks21_valid i
  · exact firstWindowMasks22_valid i
  · exact firstWindowMasks23_valid i
  · exact firstWindowMasks24_valid i
  · exact firstWindowMasks25_valid i
  · exact firstWindowMasks26_valid i
  · exact firstWindowMasks27_valid i
  · exact firstWindowMasks28_valid i
  · exact firstWindowMasks29_valid i
  · exact firstWindowMasks30_valid i
  · exact firstWindowMasks31_valid i
  · exact firstWindowMasks32_valid i
  · exact firstWindowMasks33_valid i
  · exact firstWindowMasks34_valid i
  · exact firstWindowMasks35_valid i
  · exact firstWindowMasks36_valid i
  · exact firstWindowMasks37_valid i
  · exact firstWindowMasks38_valid i
  · exact firstWindowMasks39_valid i
  · exact firstWindowMasks40_valid i
  · exact firstWindowMasks41_valid i
  · exact firstWindowMasks42_valid i
  · exact firstWindowMasks43_valid i
  · exact firstWindowMasks44_valid i
  · exact firstWindowMasks45_valid i
  · exact firstWindowMasks46_valid i
  · exact firstWindowMasks47_valid i
  · exact firstWindowMasks48_valid i
  · exact firstWindowMasks49_valid i
  · exact firstWindowMasks50_valid i
  · exact firstWindowMasks51_valid i
  · exact firstWindowMasks52_valid i
  · exact firstWindowMasks53_valid i
  · exact firstWindowMasks54_valid i
  · exact firstWindowMasks55_valid i
  · exact firstWindowMasks56_valid i
  · exact firstWindowMasks57_valid i
  · exact firstWindowMasks58_valid i
  · exact firstWindowMasks59_valid i
  · exact firstWindowMasks60_valid i
  · exact firstWindowMasks61_valid i
  · exact firstWindowMasks62_valid i
  · exact firstWindowMasks63_valid i
  · exact firstWindowMasks64_valid i
  · exact firstWindowMasks65_valid i
  · exact firstWindowMasks66_valid i
  · exact firstWindowMasks67_valid i
  · exact firstWindowMasks68_valid i
  · exact firstWindowMasks69_valid i
  · exact firstWindowMasks70_valid i
  · exact firstWindowMasks71_valid i
  · exact firstWindowMasks72_valid i
  · exact firstWindowMasks73_valid i
  · exact firstWindowMasks74_valid i
  · exact firstWindowMasks75_valid i
  · exact firstWindowMasks76_valid i
  · exact firstWindowMasks77_valid i
  · exact firstWindowMasks78_valid i
  · exact firstWindowMasks79_valid i
  · exact firstWindowMasks80_valid i
  · exact firstWindowMasks81_valid i
  · exact firstWindowMasks82_valid i
  · exact firstWindowMasks83_valid i
  · exact firstWindowMasks84_valid i
  · exact firstWindowMasks85_valid i
  · exact firstWindowMasks86_valid i
  · exact firstWindowMasks87_valid i
  · exact firstWindowMasks88_valid i
  · exact firstWindowMasks89_valid i
  · exact firstWindowMasks90_valid i
  · exact firstWindowMasks91_valid i
  · exact firstWindowMasks92_valid i
  · exact firstWindowMasks93_valid i
  · exact firstWindowMasks94_valid i
  · exact firstWindowMasks95_valid i
  · exact firstWindowMasks96_valid i
  · exact firstWindowMasks97_valid i
  · exact firstWindowMasks98_valid i
  · exact firstWindowMasks99_valid i
  · exact firstWindowMasks100_valid i
  · exact firstWindowMasks101_valid i
  · exact firstWindowMasks102_valid i
  · exact firstWindowMasks103_valid i
  · exact firstWindowMasks104_valid i
  · exact firstWindowMasks105_valid i
  · exact firstWindowMasks106_valid i
  · exact firstWindowMasks107_valid i
  · exact firstWindowMasks108_valid i

end Pntpp.DivisorPrefix.Computation
