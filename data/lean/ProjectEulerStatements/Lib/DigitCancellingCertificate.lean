import ProjectEulerStatements.Lib.DigitCancellingFractions

/-! Each independent kernel check covers at most one hundred numerator/denominator
pairs. The final list equalities reuse the checked rows; they do not reduce the
whole search again. Elaboration remains serial for predictable memory use. -/
namespace ProjectEulerStatements.DigitCancellingFractions

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem reference_0 : referenceRow 0 = [] := by decide +kernel
private theorem reference_1 : referenceRow 1 = [] := by decide +kernel
private theorem reference_2 : referenceRow 2 = [] := by decide +kernel
private theorem reference_3 : referenceRow 3 = [] := by decide +kernel
private theorem reference_4 : referenceRow 4 = [] := by decide +kernel
private theorem reference_5 : referenceRow 5 = [] := by decide +kernel
private theorem reference_6 : referenceRow 6 = [] := by decide +kernel
private theorem reference_7 : referenceRow 7 = [] := by decide +kernel
private theorem reference_8 : referenceRow 8 = [] := by decide +kernel
private theorem reference_9 : referenceRow 9 = [] := by decide +kernel
private theorem reference_10 : referenceRow 10 = [] := by decide +kernel
private theorem reference_11 : referenceRow 11 = [] := by decide +kernel
private theorem reference_12 : referenceRow 12 = [] := by decide +kernel
private theorem reference_13 : referenceRow 13 = [] := by decide +kernel
private theorem reference_14 : referenceRow 14 = [] := by decide +kernel
private theorem reference_15 : referenceRow 15 = [] := by decide +kernel
private theorem reference_16 : referenceRow 16 = [(16, 64)] := by decide +kernel
private theorem reference_17 : referenceRow 17 = [] := by decide +kernel
private theorem reference_18 : referenceRow 18 = [] := by decide +kernel
private theorem reference_19 : referenceRow 19 = [(19, 95)] := by decide +kernel
private theorem reference_20 : referenceRow 20 = [] := by decide +kernel
private theorem reference_21 : referenceRow 21 = [] := by decide +kernel
private theorem reference_22 : referenceRow 22 = [] := by decide +kernel
private theorem reference_23 : referenceRow 23 = [] := by decide +kernel
private theorem reference_24 : referenceRow 24 = [] := by decide +kernel
private theorem reference_25 : referenceRow 25 = [] := by decide +kernel
private theorem reference_26 : referenceRow 26 = [(26, 65)] := by decide +kernel
private theorem reference_27 : referenceRow 27 = [] := by decide +kernel
private theorem reference_28 : referenceRow 28 = [] := by decide +kernel
private theorem reference_29 : referenceRow 29 = [] := by decide +kernel
private theorem reference_30 : referenceRow 30 = [] := by decide +kernel
private theorem reference_31 : referenceRow 31 = [] := by decide +kernel
private theorem reference_32 : referenceRow 32 = [] := by decide +kernel
private theorem reference_33 : referenceRow 33 = [] := by decide +kernel
private theorem reference_34 : referenceRow 34 = [] := by decide +kernel
private theorem reference_35 : referenceRow 35 = [] := by decide +kernel
private theorem reference_36 : referenceRow 36 = [] := by decide +kernel
private theorem reference_37 : referenceRow 37 = [] := by decide +kernel
private theorem reference_38 : referenceRow 38 = [] := by decide +kernel
private theorem reference_39 : referenceRow 39 = [] := by decide +kernel
private theorem reference_40 : referenceRow 40 = [] := by decide +kernel
private theorem reference_41 : referenceRow 41 = [] := by decide +kernel
private theorem reference_42 : referenceRow 42 = [] := by decide +kernel
private theorem reference_43 : referenceRow 43 = [] := by decide +kernel
private theorem reference_44 : referenceRow 44 = [] := by decide +kernel
private theorem reference_45 : referenceRow 45 = [] := by decide +kernel
private theorem reference_46 : referenceRow 46 = [] := by decide +kernel
private theorem reference_47 : referenceRow 47 = [] := by decide +kernel
private theorem reference_48 : referenceRow 48 = [] := by decide +kernel
private theorem reference_49 : referenceRow 49 = [(49, 98)] := by decide +kernel
private theorem reference_50 : referenceRow 50 = [] := by decide +kernel
private theorem reference_51 : referenceRow 51 = [] := by decide +kernel
private theorem reference_52 : referenceRow 52 = [] := by decide +kernel
private theorem reference_53 : referenceRow 53 = [] := by decide +kernel
private theorem reference_54 : referenceRow 54 = [] := by decide +kernel
private theorem reference_55 : referenceRow 55 = [] := by decide +kernel
private theorem reference_56 : referenceRow 56 = [] := by decide +kernel
private theorem reference_57 : referenceRow 57 = [] := by decide +kernel
private theorem reference_58 : referenceRow 58 = [] := by decide +kernel
private theorem reference_59 : referenceRow 59 = [] := by decide +kernel
private theorem reference_60 : referenceRow 60 = [] := by decide +kernel
private theorem reference_61 : referenceRow 61 = [] := by decide +kernel
private theorem reference_62 : referenceRow 62 = [] := by decide +kernel
private theorem reference_63 : referenceRow 63 = [] := by decide +kernel
private theorem reference_64 : referenceRow 64 = [] := by decide +kernel
private theorem reference_65 : referenceRow 65 = [] := by decide +kernel
private theorem reference_66 : referenceRow 66 = [] := by decide +kernel
private theorem reference_67 : referenceRow 67 = [] := by decide +kernel
private theorem reference_68 : referenceRow 68 = [] := by decide +kernel
private theorem reference_69 : referenceRow 69 = [] := by decide +kernel
private theorem reference_70 : referenceRow 70 = [] := by decide +kernel
private theorem reference_71 : referenceRow 71 = [] := by decide +kernel
private theorem reference_72 : referenceRow 72 = [] := by decide +kernel
private theorem reference_73 : referenceRow 73 = [] := by decide +kernel
private theorem reference_74 : referenceRow 74 = [] := by decide +kernel
private theorem reference_75 : referenceRow 75 = [] := by decide +kernel
private theorem reference_76 : referenceRow 76 = [] := by decide +kernel
private theorem reference_77 : referenceRow 77 = [] := by decide +kernel
private theorem reference_78 : referenceRow 78 = [] := by decide +kernel
private theorem reference_79 : referenceRow 79 = [] := by decide +kernel
private theorem reference_80 : referenceRow 80 = [] := by decide +kernel
private theorem reference_81 : referenceRow 81 = [] := by decide +kernel
private theorem reference_82 : referenceRow 82 = [] := by decide +kernel
private theorem reference_83 : referenceRow 83 = [] := by decide +kernel
private theorem reference_84 : referenceRow 84 = [] := by decide +kernel
private theorem reference_85 : referenceRow 85 = [] := by decide +kernel
private theorem reference_86 : referenceRow 86 = [] := by decide +kernel
private theorem reference_87 : referenceRow 87 = [] := by decide +kernel
private theorem reference_88 : referenceRow 88 = [] := by decide +kernel
private theorem reference_89 : referenceRow 89 = [] := by decide +kernel
private theorem reference_90 : referenceRow 90 = [] := by decide +kernel
private theorem reference_91 : referenceRow 91 = [] := by decide +kernel
private theorem reference_92 : referenceRow 92 = [] := by decide +kernel
private theorem reference_93 : referenceRow 93 = [] := by decide +kernel
private theorem reference_94 : referenceRow 94 = [] := by decide +kernel
private theorem reference_95 : referenceRow 95 = [] := by decide +kernel
private theorem reference_96 : referenceRow 96 = [] := by decide +kernel
private theorem reference_97 : referenceRow 97 = [] := by decide +kernel
private theorem reference_98 : referenceRow 98 = [] := by decide +kernel
private theorem reference_99 : referenceRow 99 = [] := by decide +kernel

private theorem reference_block0 :
    (List.range' 0 10).flatMap referenceRow = [] := by
  change referenceRow 0 ++ (referenceRow 1 ++ (referenceRow 2 ++ (referenceRow 3 ++ (referenceRow 4 ++ (referenceRow 5 ++ (referenceRow 6 ++ (referenceRow 7 ++ (referenceRow 8 ++ (referenceRow 9 ++ ([])))))))))) = _
  rewrite [reference_0, reference_1, reference_2, reference_3, reference_4, reference_5, reference_6, reference_7, reference_8, reference_9]
  rfl

private theorem reference_block10 :
    (List.range' 10 10).flatMap referenceRow = [(16, 64), (19, 95)] := by
  change referenceRow 10 ++ (referenceRow 11 ++ (referenceRow 12 ++ (referenceRow 13 ++ (referenceRow 14 ++ (referenceRow 15 ++ (referenceRow 16 ++ (referenceRow 17 ++ (referenceRow 18 ++ (referenceRow 19 ++ ([])))))))))) = _
  rewrite [reference_10, reference_11, reference_12, reference_13, reference_14, reference_15, reference_16, reference_17, reference_18, reference_19]
  rfl

private theorem reference_block20 :
    (List.range' 20 10).flatMap referenceRow = [(26, 65)] := by
  change referenceRow 20 ++ (referenceRow 21 ++ (referenceRow 22 ++ (referenceRow 23 ++ (referenceRow 24 ++ (referenceRow 25 ++ (referenceRow 26 ++ (referenceRow 27 ++ (referenceRow 28 ++ (referenceRow 29 ++ ([])))))))))) = _
  rewrite [reference_20, reference_21, reference_22, reference_23, reference_24, reference_25, reference_26, reference_27, reference_28, reference_29]
  rfl

private theorem reference_block30 :
    (List.range' 30 10).flatMap referenceRow = [] := by
  change referenceRow 30 ++ (referenceRow 31 ++ (referenceRow 32 ++ (referenceRow 33 ++ (referenceRow 34 ++ (referenceRow 35 ++ (referenceRow 36 ++ (referenceRow 37 ++ (referenceRow 38 ++ (referenceRow 39 ++ ([])))))))))) = _
  rewrite [reference_30, reference_31, reference_32, reference_33, reference_34, reference_35, reference_36, reference_37, reference_38, reference_39]
  rfl

private theorem reference_block40 :
    (List.range' 40 10).flatMap referenceRow = [(49, 98)] := by
  change referenceRow 40 ++ (referenceRow 41 ++ (referenceRow 42 ++ (referenceRow 43 ++ (referenceRow 44 ++ (referenceRow 45 ++ (referenceRow 46 ++ (referenceRow 47 ++ (referenceRow 48 ++ (referenceRow 49 ++ ([])))))))))) = _
  rewrite [reference_40, reference_41, reference_42, reference_43, reference_44, reference_45, reference_46, reference_47, reference_48, reference_49]
  rfl

private theorem reference_block50 :
    (List.range' 50 10).flatMap referenceRow = [] := by
  change referenceRow 50 ++ (referenceRow 51 ++ (referenceRow 52 ++ (referenceRow 53 ++ (referenceRow 54 ++ (referenceRow 55 ++ (referenceRow 56 ++ (referenceRow 57 ++ (referenceRow 58 ++ (referenceRow 59 ++ ([])))))))))) = _
  rewrite [reference_50, reference_51, reference_52, reference_53, reference_54, reference_55, reference_56, reference_57, reference_58, reference_59]
  rfl

private theorem reference_block60 :
    (List.range' 60 10).flatMap referenceRow = [] := by
  change referenceRow 60 ++ (referenceRow 61 ++ (referenceRow 62 ++ (referenceRow 63 ++ (referenceRow 64 ++ (referenceRow 65 ++ (referenceRow 66 ++ (referenceRow 67 ++ (referenceRow 68 ++ (referenceRow 69 ++ ([])))))))))) = _
  rewrite [reference_60, reference_61, reference_62, reference_63, reference_64, reference_65, reference_66, reference_67, reference_68, reference_69]
  rfl

private theorem reference_block70 :
    (List.range' 70 10).flatMap referenceRow = [] := by
  change referenceRow 70 ++ (referenceRow 71 ++ (referenceRow 72 ++ (referenceRow 73 ++ (referenceRow 74 ++ (referenceRow 75 ++ (referenceRow 76 ++ (referenceRow 77 ++ (referenceRow 78 ++ (referenceRow 79 ++ ([])))))))))) = _
  rewrite [reference_70, reference_71, reference_72, reference_73, reference_74, reference_75, reference_76, reference_77, reference_78, reference_79]
  rfl

private theorem reference_block80 :
    (List.range' 80 10).flatMap referenceRow = [] := by
  change referenceRow 80 ++ (referenceRow 81 ++ (referenceRow 82 ++ (referenceRow 83 ++ (referenceRow 84 ++ (referenceRow 85 ++ (referenceRow 86 ++ (referenceRow 87 ++ (referenceRow 88 ++ (referenceRow 89 ++ ([])))))))))) = _
  rewrite [reference_80, reference_81, reference_82, reference_83, reference_84, reference_85, reference_86, reference_87, reference_88, reference_89]
  rfl

private theorem reference_block90 :
    (List.range' 90 10).flatMap referenceRow = [] := by
  change referenceRow 90 ++ (referenceRow 91 ++ (referenceRow 92 ++ (referenceRow 93 ++ (referenceRow 94 ++ (referenceRow 95 ++ (referenceRow 96 ++ (referenceRow 97 ++ (referenceRow 98 ++ (referenceRow 99 ++ ([])))))))))) = _
  rewrite [reference_90, reference_91, reference_92, reference_93, reference_94, reference_95, reference_96, reference_97, reference_98, reference_99]
  rfl

private theorem optimized_10 : optimizedRow 10 = [] := by decide +kernel
private theorem optimized_11 : optimizedRow 11 = [] := by decide +kernel
private theorem optimized_12 : optimizedRow 12 = [] := by decide +kernel
private theorem optimized_13 : optimizedRow 13 = [] := by decide +kernel
private theorem optimized_14 : optimizedRow 14 = [] := by decide +kernel
private theorem optimized_15 : optimizedRow 15 = [] := by decide +kernel
private theorem optimized_16 : optimizedRow 16 = [(16, 64)] := by decide +kernel
private theorem optimized_17 : optimizedRow 17 = [] := by decide +kernel
private theorem optimized_18 : optimizedRow 18 = [] := by decide +kernel
private theorem optimized_19 : optimizedRow 19 = [(19, 95)] := by decide +kernel
private theorem optimized_20 : optimizedRow 20 = [] := by decide +kernel
private theorem optimized_21 : optimizedRow 21 = [] := by decide +kernel
private theorem optimized_22 : optimizedRow 22 = [] := by decide +kernel
private theorem optimized_23 : optimizedRow 23 = [] := by decide +kernel
private theorem optimized_24 : optimizedRow 24 = [] := by decide +kernel
private theorem optimized_25 : optimizedRow 25 = [] := by decide +kernel
private theorem optimized_26 : optimizedRow 26 = [(26, 65)] := by decide +kernel
private theorem optimized_27 : optimizedRow 27 = [] := by decide +kernel
private theorem optimized_28 : optimizedRow 28 = [] := by decide +kernel
private theorem optimized_29 : optimizedRow 29 = [] := by decide +kernel
private theorem optimized_30 : optimizedRow 30 = [] := by decide +kernel
private theorem optimized_31 : optimizedRow 31 = [] := by decide +kernel
private theorem optimized_32 : optimizedRow 32 = [] := by decide +kernel
private theorem optimized_33 : optimizedRow 33 = [] := by decide +kernel
private theorem optimized_34 : optimizedRow 34 = [] := by decide +kernel
private theorem optimized_35 : optimizedRow 35 = [] := by decide +kernel
private theorem optimized_36 : optimizedRow 36 = [] := by decide +kernel
private theorem optimized_37 : optimizedRow 37 = [] := by decide +kernel
private theorem optimized_38 : optimizedRow 38 = [] := by decide +kernel
private theorem optimized_39 : optimizedRow 39 = [] := by decide +kernel
private theorem optimized_40 : optimizedRow 40 = [] := by decide +kernel
private theorem optimized_41 : optimizedRow 41 = [] := by decide +kernel
private theorem optimized_42 : optimizedRow 42 = [] := by decide +kernel
private theorem optimized_43 : optimizedRow 43 = [] := by decide +kernel
private theorem optimized_44 : optimizedRow 44 = [] := by decide +kernel
private theorem optimized_45 : optimizedRow 45 = [] := by decide +kernel
private theorem optimized_46 : optimizedRow 46 = [] := by decide +kernel
private theorem optimized_47 : optimizedRow 47 = [] := by decide +kernel
private theorem optimized_48 : optimizedRow 48 = [] := by decide +kernel
private theorem optimized_49 : optimizedRow 49 = [(49, 98)] := by decide +kernel
private theorem optimized_50 : optimizedRow 50 = [] := by decide +kernel
private theorem optimized_51 : optimizedRow 51 = [] := by decide +kernel
private theorem optimized_52 : optimizedRow 52 = [] := by decide +kernel
private theorem optimized_53 : optimizedRow 53 = [] := by decide +kernel
private theorem optimized_54 : optimizedRow 54 = [] := by decide +kernel
private theorem optimized_55 : optimizedRow 55 = [] := by decide +kernel
private theorem optimized_56 : optimizedRow 56 = [] := by decide +kernel
private theorem optimized_57 : optimizedRow 57 = [] := by decide +kernel
private theorem optimized_58 : optimizedRow 58 = [] := by decide +kernel
private theorem optimized_59 : optimizedRow 59 = [] := by decide +kernel
private theorem optimized_60 : optimizedRow 60 = [] := by decide +kernel
private theorem optimized_61 : optimizedRow 61 = [] := by decide +kernel
private theorem optimized_62 : optimizedRow 62 = [] := by decide +kernel
private theorem optimized_63 : optimizedRow 63 = [] := by decide +kernel
private theorem optimized_64 : optimizedRow 64 = [] := by decide +kernel
private theorem optimized_65 : optimizedRow 65 = [] := by decide +kernel
private theorem optimized_66 : optimizedRow 66 = [] := by decide +kernel
private theorem optimized_67 : optimizedRow 67 = [] := by decide +kernel
private theorem optimized_68 : optimizedRow 68 = [] := by decide +kernel
private theorem optimized_69 : optimizedRow 69 = [] := by decide +kernel
private theorem optimized_70 : optimizedRow 70 = [] := by decide +kernel
private theorem optimized_71 : optimizedRow 71 = [] := by decide +kernel
private theorem optimized_72 : optimizedRow 72 = [] := by decide +kernel
private theorem optimized_73 : optimizedRow 73 = [] := by decide +kernel
private theorem optimized_74 : optimizedRow 74 = [] := by decide +kernel
private theorem optimized_75 : optimizedRow 75 = [] := by decide +kernel
private theorem optimized_76 : optimizedRow 76 = [] := by decide +kernel
private theorem optimized_77 : optimizedRow 77 = [] := by decide +kernel
private theorem optimized_78 : optimizedRow 78 = [] := by decide +kernel
private theorem optimized_79 : optimizedRow 79 = [] := by decide +kernel
private theorem optimized_80 : optimizedRow 80 = [] := by decide +kernel
private theorem optimized_81 : optimizedRow 81 = [] := by decide +kernel
private theorem optimized_82 : optimizedRow 82 = [] := by decide +kernel
private theorem optimized_83 : optimizedRow 83 = [] := by decide +kernel
private theorem optimized_84 : optimizedRow 84 = [] := by decide +kernel
private theorem optimized_85 : optimizedRow 85 = [] := by decide +kernel
private theorem optimized_86 : optimizedRow 86 = [] := by decide +kernel
private theorem optimized_87 : optimizedRow 87 = [] := by decide +kernel
private theorem optimized_88 : optimizedRow 88 = [] := by decide +kernel
private theorem optimized_89 : optimizedRow 89 = [] := by decide +kernel
private theorem optimized_90 : optimizedRow 90 = [] := by decide +kernel
private theorem optimized_91 : optimizedRow 91 = [] := by decide +kernel
private theorem optimized_92 : optimizedRow 92 = [] := by decide +kernel
private theorem optimized_93 : optimizedRow 93 = [] := by decide +kernel
private theorem optimized_94 : optimizedRow 94 = [] := by decide +kernel
private theorem optimized_95 : optimizedRow 95 = [] := by decide +kernel
private theorem optimized_96 : optimizedRow 96 = [] := by decide +kernel
private theorem optimized_97 : optimizedRow 97 = [] := by decide +kernel
private theorem optimized_98 : optimizedRow 98 = [] := by decide +kernel
private theorem optimized_99 : optimizedRow 99 = [] := by decide +kernel

private theorem optimized_block10 :
    (List.range' 10 10).flatMap optimizedRow = [(16, 64), (19, 95)] := by
  change optimizedRow 10 ++ (optimizedRow 11 ++ (optimizedRow 12 ++ (optimizedRow 13 ++ (optimizedRow 14 ++ (optimizedRow 15 ++ (optimizedRow 16 ++ (optimizedRow 17 ++ (optimizedRow 18 ++ (optimizedRow 19 ++ ([])))))))))) = _
  rewrite [optimized_10, optimized_11, optimized_12, optimized_13, optimized_14, optimized_15, optimized_16, optimized_17, optimized_18, optimized_19]
  rfl

private theorem optimized_block20 :
    (List.range' 20 10).flatMap optimizedRow = [(26, 65)] := by
  change optimizedRow 20 ++ (optimizedRow 21 ++ (optimizedRow 22 ++ (optimizedRow 23 ++ (optimizedRow 24 ++ (optimizedRow 25 ++ (optimizedRow 26 ++ (optimizedRow 27 ++ (optimizedRow 28 ++ (optimizedRow 29 ++ ([])))))))))) = _
  rewrite [optimized_20, optimized_21, optimized_22, optimized_23, optimized_24, optimized_25, optimized_26, optimized_27, optimized_28, optimized_29]
  rfl

private theorem optimized_block30 :
    (List.range' 30 10).flatMap optimizedRow = [] := by
  change optimizedRow 30 ++ (optimizedRow 31 ++ (optimizedRow 32 ++ (optimizedRow 33 ++ (optimizedRow 34 ++ (optimizedRow 35 ++ (optimizedRow 36 ++ (optimizedRow 37 ++ (optimizedRow 38 ++ (optimizedRow 39 ++ ([])))))))))) = _
  rewrite [optimized_30, optimized_31, optimized_32, optimized_33, optimized_34, optimized_35, optimized_36, optimized_37, optimized_38, optimized_39]
  rfl

private theorem optimized_block40 :
    (List.range' 40 10).flatMap optimizedRow = [(49, 98)] := by
  change optimizedRow 40 ++ (optimizedRow 41 ++ (optimizedRow 42 ++ (optimizedRow 43 ++ (optimizedRow 44 ++ (optimizedRow 45 ++ (optimizedRow 46 ++ (optimizedRow 47 ++ (optimizedRow 48 ++ (optimizedRow 49 ++ ([])))))))))) = _
  rewrite [optimized_40, optimized_41, optimized_42, optimized_43, optimized_44, optimized_45, optimized_46, optimized_47, optimized_48, optimized_49]
  rfl

private theorem optimized_block50 :
    (List.range' 50 10).flatMap optimizedRow = [] := by
  change optimizedRow 50 ++ (optimizedRow 51 ++ (optimizedRow 52 ++ (optimizedRow 53 ++ (optimizedRow 54 ++ (optimizedRow 55 ++ (optimizedRow 56 ++ (optimizedRow 57 ++ (optimizedRow 58 ++ (optimizedRow 59 ++ ([])))))))))) = _
  rewrite [optimized_50, optimized_51, optimized_52, optimized_53, optimized_54, optimized_55, optimized_56, optimized_57, optimized_58, optimized_59]
  rfl

private theorem optimized_block60 :
    (List.range' 60 10).flatMap optimizedRow = [] := by
  change optimizedRow 60 ++ (optimizedRow 61 ++ (optimizedRow 62 ++ (optimizedRow 63 ++ (optimizedRow 64 ++ (optimizedRow 65 ++ (optimizedRow 66 ++ (optimizedRow 67 ++ (optimizedRow 68 ++ (optimizedRow 69 ++ ([])))))))))) = _
  rewrite [optimized_60, optimized_61, optimized_62, optimized_63, optimized_64, optimized_65, optimized_66, optimized_67, optimized_68, optimized_69]
  rfl

private theorem optimized_block70 :
    (List.range' 70 10).flatMap optimizedRow = [] := by
  change optimizedRow 70 ++ (optimizedRow 71 ++ (optimizedRow 72 ++ (optimizedRow 73 ++ (optimizedRow 74 ++ (optimizedRow 75 ++ (optimizedRow 76 ++ (optimizedRow 77 ++ (optimizedRow 78 ++ (optimizedRow 79 ++ ([])))))))))) = _
  rewrite [optimized_70, optimized_71, optimized_72, optimized_73, optimized_74, optimized_75, optimized_76, optimized_77, optimized_78, optimized_79]
  rfl

private theorem optimized_block80 :
    (List.range' 80 10).flatMap optimizedRow = [] := by
  change optimizedRow 80 ++ (optimizedRow 81 ++ (optimizedRow 82 ++ (optimizedRow 83 ++ (optimizedRow 84 ++ (optimizedRow 85 ++ (optimizedRow 86 ++ (optimizedRow 87 ++ (optimizedRow 88 ++ (optimizedRow 89 ++ ([])))))))))) = _
  rewrite [optimized_80, optimized_81, optimized_82, optimized_83, optimized_84, optimized_85, optimized_86, optimized_87, optimized_88, optimized_89]
  rfl

private theorem optimized_block90 :
    (List.range' 90 10).flatMap optimizedRow = [] := by
  change optimizedRow 90 ++ (optimizedRow 91 ++ (optimizedRow 92 ++ (optimizedRow 93 ++ (optimizedRow 94 ++ (optimizedRow 95 ++ (optimizedRow 96 ++ (optimizedRow 97 ++ (optimizedRow 98 ++ (optimizedRow 99 ++ ([])))))))))) = _
  rewrite [optimized_90, optimized_91, optimized_92, optimized_93, optimized_94, optimized_95, optimized_96, optimized_97, optimized_98, optimized_99]
  rfl

theorem reference_fractions : P33.curiousFractions = fractions := by
  rewrite [curiousFractions_eq_rows]
  change (List.range' 0 100).flatMap referenceRow = _
  rewrite [← List.range'_append_1 (s := 0) (m := 10) (n := 90), List.flatMap_append, reference_block0]
  rewrite [← List.range'_append_1 (s := 10) (m := 10) (n := 80), List.flatMap_append, reference_block10]
  rewrite [← List.range'_append_1 (s := 20) (m := 10) (n := 70), List.flatMap_append, reference_block20]
  rewrite [← List.range'_append_1 (s := 30) (m := 10) (n := 60), List.flatMap_append, reference_block30]
  rewrite [← List.range'_append_1 (s := 40) (m := 10) (n := 50), List.flatMap_append, reference_block40]
  rewrite [← List.range'_append_1 (s := 50) (m := 10) (n := 40), List.flatMap_append, reference_block50]
  rewrite [← List.range'_append_1 (s := 60) (m := 10) (n := 30), List.flatMap_append, reference_block60]
  rewrite [← List.range'_append_1 (s := 70) (m := 10) (n := 20), List.flatMap_append, reference_block70]
  rewrite [← List.range'_append_1 (s := 80) (m := 10) (n := 10), List.flatMap_append, reference_block80]
  rewrite [reference_block90]
  rfl

theorem optimized_fractions : optimizedFractions = fractions := by
  change (List.range' 10 90).flatMap optimizedRow = _
  rewrite [← List.range'_append_1 (s := 10) (m := 10) (n := 80), List.flatMap_append, optimized_block10]
  rewrite [← List.range'_append_1 (s := 20) (m := 10) (n := 70), List.flatMap_append, optimized_block20]
  rewrite [← List.range'_append_1 (s := 30) (m := 10) (n := 60), List.flatMap_append, optimized_block30]
  rewrite [← List.range'_append_1 (s := 40) (m := 10) (n := 50), List.flatMap_append, optimized_block40]
  rewrite [← List.range'_append_1 (s := 50) (m := 10) (n := 40), List.flatMap_append, optimized_block50]
  rewrite [← List.range'_append_1 (s := 60) (m := 10) (n := 30), List.flatMap_append, optimized_block60]
  rewrite [← List.range'_append_1 (s := 70) (m := 10) (n := 20), List.flatMap_append, optimized_block70]
  rewrite [← List.range'_append_1 (s := 80) (m := 10) (n := 10), List.flatMap_append, optimized_block80]
  rewrite [optimized_block90]
  rfl

/-- Both exact source search orders produce the same four fractions. -/
theorem fractions_equiv : optimizedFractions = P33.curiousFractions := by
  rw [optimized_fractions, reference_fractions]

theorem reference_value : P33.naive = 100 := by
  rw [naive_eq_denominator, reference_fractions, fractions_denominator]

theorem optimized_value : denominator optimizedFractions = 100 := by
  rw [optimized_fractions, fractions_denominator]

end ProjectEulerStatements.DigitCancellingFractions
