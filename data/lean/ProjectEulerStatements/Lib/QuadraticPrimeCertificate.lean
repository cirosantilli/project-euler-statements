import ProjectEulerStatements.P27

/-! A finite, kernel-checked necessary-candidate certificate for problem 27.
The row declarations are separate so ordinary builds bound their live work. -/
namespace ProjectEulerStatements.QuadraticPrimeCertificate
open P27

def smallPrimes : List Int := [2,3,5,7,11,13,17,19,23,29,31,37,41]
def survives (value : Int) : Bool :=
  decide (1 < value) && smallPrimes.all (fun divisor => decide (value = divisor ∨ value % divisor ≠ 0))
def eligibleBs : List Int :=
  ((List.range 930).map (fun (i : Nat) => (71 + (i : Int)))).filter survives
def row (b : Int) : List (Int × Int) :=
  (List.range 532).map fun (i : Nat) => (-63 + 2 * (i : Int), b)
def candidates : List (Int × Int) := eligibleBs.flatMap row
def sieve (pairs : List (Int × Int)) : List (Int × Int) :=
  (List.range' 1 70).foldl (fun pairs n => pairs.filter (fun p => survives (quad p.1 p.2 n))) pairs
def remaining : List (Int × Int) := eligibleBs.flatMap (fun b => sieve (row b))

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Each kernel check handles at most one row of 532 candidate coefficients.
-- Separate declarations keep the finite reduction bounded rather than retaining
-- the complete 79,268-pair rectangle in one normalization task.
private theorem eligibleBs_checked : eligibleBs =
  [71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997] := by decide +kernel

private theorem row_71 : sieve (row 71) = [] := by decide +kernel
private theorem row_73 : sieve (row 73) = [] := by decide +kernel
private theorem row_79 : sieve (row 79) = [] := by decide +kernel
private theorem row_83 : sieve (row 83) = [(463,83)] := by decide +kernel
private theorem row_89 : sieve (row 89) = [] := by decide +kernel
private theorem row_97 : sieve (row 97) = [] := by decide +kernel
private theorem row_101 : sieve (row 101) = [] := by decide +kernel
private theorem row_103 : sieve (row 103) = [] := by decide +kernel
private theorem row_107 : sieve (row 107) = [] := by decide +kernel
private theorem row_109 : sieve (row 109) = [(273,109)] := by decide +kernel
private theorem row_113 : sieve (row 113) = [] := by decide +kernel
private theorem row_127 : sieve (row 127) = [(801,127)] := by decide +kernel
private theorem row_131 : sieve (row 131) = [] := by decide +kernel
private theorem row_137 : sieve (row 137) = [(475,137)] := by decide +kernel
private theorem row_139 : sieve (row 139) = [] := by decide +kernel
private theorem row_149 : sieve (row 149) = [] := by decide +kernel
private theorem row_151 : sieve (row 151) = [] := by decide +kernel
private theorem row_157 : sieve (row 157) = [] := by decide +kernel
private theorem row_163 : sieve (row 163) = [] := by decide +kernel
private theorem row_167 : sieve (row 167) = [] := by decide +kernel
private theorem row_173 : sieve (row 173) = [] := by decide +kernel
private theorem row_179 : sieve (row 179) = [] := by decide +kernel
private theorem row_181 : sieve (row 181) = [] := by decide +kernel
private theorem row_191 : sieve (row 191) = [] := by decide +kernel
private theorem row_193 : sieve (row 193) = [] := by decide +kernel
private theorem row_197 : sieve (row 197) = [] := by decide +kernel
private theorem row_199 : sieve (row 199) = [] := by decide +kernel
private theorem row_211 : sieve (row 211) = [] := by decide +kernel
private theorem row_223 : sieve (row 223) = [(825,223)] := by decide +kernel
private theorem row_227 : sieve (row 227) = [(601,227)] := by decide +kernel
private theorem row_229 : sieve (row 229) = [] := by decide +kernel
private theorem row_233 : sieve (row 233) = [] := by decide +kernel
private theorem row_239 : sieve (row 239) = [] := by decide +kernel
private theorem row_241 : sieve (row 241) = [] := by decide +kernel
private theorem row_251 : sieve (row 251) = [] := by decide +kernel
private theorem row_257 : sieve (row 257) = [] := by decide +kernel
private theorem row_263 : sieve (row 263) = [] := by decide +kernel
private theorem row_269 : sieve (row 269) = [] := by decide +kernel
private theorem row_271 : sieve (row 271) = [] := by decide +kernel
private theorem row_277 : sieve (row 277) = [] := by decide +kernel
private theorem row_281 : sieve (row 281) = [] := by decide +kernel
private theorem row_283 : sieve (row 283) = [] := by decide +kernel
private theorem row_293 : sieve (row 293) = [(725,293)] := by decide +kernel
private theorem row_307 : sieve (row 307) = [] := by decide +kernel
private theorem row_311 : sieve (row 311) = [] := by decide +kernel
private theorem row_313 : sieve (row 313) = [] := by decide +kernel
private theorem row_317 : sieve (row 317) = [(415,317)] := by decide +kernel
private theorem row_331 : sieve (row 331) = [] := by decide +kernel
private theorem row_337 : sieve (row 337) = [] := by decide +kernel
private theorem row_347 : sieve (row 347) = [(629,347)] := by decide +kernel
private theorem row_349 : sieve (row 349) = [] := by decide +kernel
private theorem row_353 : sieve (row 353) = [] := by decide +kernel
private theorem row_359 : sieve (row 359) = [] := by decide +kernel
private theorem row_367 : sieve (row 367) = [] := by decide +kernel
private theorem row_373 : sieve (row 373) = [] := by decide +kernel
private theorem row_379 : sieve (row 379) = [] := by decide +kernel
private theorem row_383 : sieve (row 383) = [(275,383)] := by decide +kernel
private theorem row_389 : sieve (row 389) = [] := by decide +kernel
private theorem row_397 : sieve (row 397) = [] := by decide +kernel
private theorem row_401 : sieve (row 401) = [] := by decide +kernel
private theorem row_409 : sieve (row 409) = [(477,409)] := by decide +kernel
private theorem row_419 : sieve (row 419) = [] := by decide +kernel
private theorem row_421 : sieve (row 421) = [] := by decide +kernel
private theorem row_431 : sieve (row 431) = [] := by decide +kernel
private theorem row_433 : sieve (row 433) = [(783,433)] := by decide +kernel
private theorem row_439 : sieve (row 439) = [] := by decide +kernel
private theorem row_443 : sieve (row 443) = [] := by decide +kernel
private theorem row_449 : sieve (row 449) = [] := by decide +kernel
private theorem row_457 : sieve (row 457) = [] := by decide +kernel
private theorem row_461 : sieve (row 461) = [] := by decide +kernel
private theorem row_463 : sieve (row 463) = [] := by decide +kernel
private theorem row_467 : sieve (row 467) = [] := by decide +kernel
private theorem row_479 : sieve (row 479) = [] := by decide +kernel
private theorem row_487 : sieve (row 487) = [] := by decide +kernel
private theorem row_491 : sieve (row 491) = [] := by decide +kernel
private theorem row_499 : sieve (row 499) = [] := by decide +kernel
private theorem row_503 : sieve (row 503) = [] := by decide +kernel
private theorem row_509 : sieve (row 509) = [] := by decide +kernel
private theorem row_521 : sieve (row 521) = [] := by decide +kernel
private theorem row_523 : sieve (row 523) = [] := by decide +kernel
private theorem row_541 : sieve (row 541) = [] := by decide +kernel
private theorem row_547 : sieve (row 547) = [(465,547)] := by decide +kernel
private theorem row_557 : sieve (row 557) = [(721,557)] := by decide +kernel
private theorem row_563 : sieve (row 563) = [] := by decide +kernel
private theorem row_569 : sieve (row 569) = [] := by decide +kernel
private theorem row_571 : sieve (row 571) = [] := by decide +kernel
private theorem row_577 : sieve (row 577) = [] := by decide +kernel
private theorem row_587 : sieve (row 587) = [] := by decide +kernel
private theorem row_593 : sieve (row 593) = [] := by decide +kernel
private theorem row_599 : sieve (row 599) = [] := by decide +kernel
private theorem row_601 : sieve (row 601) = [] := by decide +kernel
private theorem row_607 : sieve (row 607) = [] := by decide +kernel
private theorem row_613 : sieve (row 613) = [(477,613)] := by decide +kernel
private theorem row_617 : sieve (row 617) = [] := by decide +kernel
private theorem row_619 : sieve (row 619) = [] := by decide +kernel
private theorem row_631 : sieve (row 631) = [] := by decide +kernel
private theorem row_641 : sieve (row 641) = [] := by decide +kernel
private theorem row_643 : sieve (row 643) = [] := by decide +kernel
private theorem row_647 : sieve (row 647) = [] := by decide +kernel
private theorem row_653 : sieve (row 653) = [] := by decide +kernel
private theorem row_659 : sieve (row 659) = [(277,659)] := by decide +kernel
private theorem row_661 : sieve (row 661) = [] := by decide +kernel
private theorem row_673 : sieve (row 673) = [] := by decide +kernel
private theorem row_677 : sieve (row 677) = [(991,677)] := by decide +kernel
private theorem row_683 : sieve (row 683) = [(925,683)] := by decide +kernel
private theorem row_691 : sieve (row 691) = [] := by decide +kernel
private theorem row_701 : sieve (row 701) = [] := by decide +kernel
private theorem row_709 : sieve (row 709) = [] := by decide +kernel
private theorem row_719 : sieve (row 719) = [] := by decide +kernel
private theorem row_727 : sieve (row 727) = [] := by decide +kernel
private theorem row_733 : sieve (row 733) = [(417,733)] := by decide +kernel
private theorem row_739 : sieve (row 739) = [] := by decide +kernel
private theorem row_743 : sieve (row 743) = [] := by decide +kernel
private theorem row_751 : sieve (row 751) = [] := by decide +kernel
private theorem row_757 : sieve (row 757) = [] := by decide +kernel
private theorem row_761 : sieve (row 761) = [] := by decide +kernel
private theorem row_769 : sieve (row 769) = [] := by decide +kernel
private theorem row_773 : sieve (row 773) = [] := by decide +kernel
private theorem row_787 : sieve (row 787) = [] := by decide +kernel
private theorem row_797 : sieve (row 797) = [] := by decide +kernel
private theorem row_809 : sieve (row 809) = [] := by decide +kernel
private theorem row_811 : sieve (row 811) = [] := by decide +kernel
private theorem row_821 : sieve (row 821) = [] := by decide +kernel
private theorem row_823 : sieve (row 823) = [] := by decide +kernel
private theorem row_827 : sieve (row 827) = [] := by decide +kernel
private theorem row_829 : sieve (row 829) = [(603,829)] := by decide +kernel
private theorem row_839 : sieve (row 839) = [] := by decide +kernel
private theorem row_853 : sieve (row 853) = [] := by decide +kernel
private theorem row_857 : sieve (row 857) = [] := by decide +kernel
private theorem row_859 : sieve (row 859) = [] := by decide +kernel
private theorem row_863 : sieve (row 863) = [] := by decide +kernel
private theorem row_877 : sieve (row 877) = [] := by decide +kernel
private theorem row_881 : sieve (row 881) = [] := by decide +kernel
private theorem row_883 : sieve (row 883) = [] := by decide +kernel
private theorem row_887 : sieve (row 887) = [(479,887)] := by decide +kernel
private theorem row_907 : sieve (row 907) = [] := by decide +kernel
private theorem row_911 : sieve (row 911) = [] := by decide +kernel
private theorem row_919 : sieve (row 919) = [] := by decide +kernel
private theorem row_929 : sieve (row 929) = [(803,929)] := by decide +kernel
private theorem row_937 : sieve (row 937) = [(279,937)] := by decide +kernel
private theorem row_941 : sieve (row 941) = [] := by decide +kernel
private theorem row_947 : sieve (row 947) = [] := by decide +kernel
private theorem row_953 : sieve (row 953) = [] := by decide +kernel
private theorem row_967 : sieve (row 967) = [] := by decide +kernel
private theorem row_971 : sieve (row 971) = [(-61,971)] := by decide +kernel
private theorem row_977 : sieve (row 977) = [(631,977)] := by decide +kernel
private theorem row_983 : sieve (row 983) = [(923,983)] := by decide +kernel
private theorem row_991 : sieve (row 991) = [] := by decide +kernel
private theorem row_997 : sieve (row 997) = [] := by decide +kernel

theorem remaining_checked : remaining =
  [(463,83),(273,109),(801,127),(475,137),(825,223),(601,227),(725,293),(415,317),(629,347),(275,383),(477,409),(783,433),(465,547),(721,557),(477,613),(277,659),(991,677),(925,683),(417,733),(603,829),(479,887),(803,929),(279,937),(-61,971),(631,977),(923,983)] := by
  simp only [remaining, eligibleBs_checked, List.flatMap_cons, List.flatMap_nil,
    row_71, row_73, row_79, row_83, row_89, row_97, row_101, row_103, row_107, row_109,
    row_113, row_127, row_131, row_137, row_139, row_149, row_151, row_157, row_163, row_167,
    row_173, row_179, row_181, row_191, row_193, row_197, row_199, row_211, row_223, row_227,
    row_229, row_233, row_239, row_241, row_251, row_257, row_263, row_269, row_271, row_277,
    row_281, row_283, row_293, row_307, row_311, row_313, row_317, row_331, row_337, row_347,
    row_349, row_353, row_359, row_367, row_373, row_379, row_383, row_389, row_397, row_401,
    row_409, row_419, row_421, row_431, row_433, row_439, row_443, row_449, row_457, row_461,
    row_463, row_467, row_479, row_487, row_491, row_499, row_503, row_509, row_521, row_523,
    row_541, row_547, row_557, row_563, row_569, row_571, row_577, row_587, row_593, row_599,
    row_601, row_607, row_613, row_617, row_619, row_631, row_641, row_643, row_647, row_653,
    row_659, row_661, row_673, row_677, row_683, row_691, row_701, row_709, row_719, row_727,
    row_733, row_739, row_743, row_751, row_757, row_761, row_769, row_773, row_787, row_797,
    row_809, row_811, row_821, row_823, row_827, row_829, row_839, row_853, row_857, row_859,
    row_863, row_877, row_881, row_883, row_887, row_907, row_911, row_919, row_929, row_937,
    row_941, row_947, row_953, row_967, row_971, row_977, row_983, row_991, row_997,
    List.nil_append, List.append_nil, List.cons_append]


end ProjectEulerStatements.QuadraticPrimeCertificate
