import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős 686: length-eight and length-twelve exclusions

Formalization of the explicit cases in IRAMBONA's forum post 9291 (2026-10-05),
with a polynomial cross-multiplication argument for length twelve.
Reference: https://www.erdosproblems.com/forum/thread/686#post-9291

The integer-square and finite-certificate framework adapts the published
length-six contribution 1e9266022bf5586a144c4e5c2901d43cfb58994fe3184e45a38113e4db7a98e1.
All dependencies are Mathlib imports. The generated bracketing tables are
checked by kernel reduction. These results do not settle the unrestricted target.
-/

namespace Contribution.Erdos686EightTwelveTwentyFive

/-- Integer squares with errors smaller than their positive roots have the same root. -/
lemma square_gap_force (p q c d : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcp : c < p) (hdq : d < q)
    (h : p^2 - q^2 = c-d) : p=q := by
  rcases lt_trichotomy p q with hl | he | hg
  · have hmul := mul_nonneg (show 0 ≤ q-p-1 by omega) (show 0 ≤ q+p by omega)
    nlinarith
  · exact he
  · have hmul := mul_nonneg (show 0 ≤ p-q-1 by omega) (show 0 ≤ p+q by omega)
    nlinarith

def block8 (n : ℕ) : ℕ := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*(n+7)*(n+8)
def center8 (n : ℕ) : ℤ := 2*n+9
def poly8 (q : ℤ) : ℤ := q^4-42*q^2+105
def near8 (n : ℕ) : ℤ := poly8 (center8 n)
def rem8 (n : ℕ) : ℤ := 4096*(center8 n)^2

lemma identity8 (n : ℕ) : (near8 n)^2-256*(block8 n : ℤ)=rem8 n := by
  simp only [near8, poly8, center8, rem8, block8, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma center8_ge (n : ℕ) : 9 ≤ center8 n := by dsimp [center8]; omega

lemma near8_pos (n : ℕ) : 0 < near8 n := by
  have hq := center8_ge n
  have hq2 : 81 ≤ (center8 n)^2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (center8 n)^2-81 by omega) (sq_nonneg (center8 n))
  dsimp [near8, poly8]
  nlinarith

lemma rem8_nonneg (n : ℕ) : 0 ≤ rem8 n := by dsimp [rem8]; positivity

lemma error8_small (n : ℕ) (hn : 68 ≤ n) : 5*rem8 n < near8 n := by
  have hq : 145 ≤ center8 n := by dsimp [center8]; omega
  have hq2 : 20522 ≤ (center8 n)^2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (center8 n)^2-20522 by omega) (sq_nonneg (center8 n))
  dsimp [near8, poly8, rem8]
  nlinarith

/-- The explicit finite bound for the length-eight equation. -/
theorem bound8 (n m : ℕ) (hmn : n ≤ m)
    (h : block8 m = 25*block8 n) : n ≤ 67 := by
  by_contra hn
  have hn' : 68 ≤ n := by omega
  have hm' : 68 ≤ m := by omega
  have hnid := identity8 n
  have hmid := identity8 m
  have hz : (block8 m : ℤ) = 25*(block8 n : ℤ) := by exact_mod_cast h
  have hp := near8_pos m
  have hq := near8_pos n
  have hc := rem8_nonneg m
  have hd := rem8_nonneg n
  have hsm := error8_small m hm'
  have hsn := error8_small n hn'
  have heq := square_gap_force (near8 m) (5*near8 n) (rem8 m) (25*rem8 n)
    (by omega) (by omega) hc (by omega) (by omega) (by omega) (by nlinarith only [hnid,hmid,hz])
  have hrem : rem8 m = 25*rem8 n := by
    rw [heq] at hmid
    nlinarith only [hnid,hmid,hz]
  have hcm := center8_ge m
  have hcn := center8_ge n
  have hcenter : center8 m = 5*center8 n := by
    apply (sq_eq_sq₀ (by omega : 0 ≤ center8 m) (by omega : 0 ≤ 5*center8 n)).mp
    dsimp [rem8] at hrem
    nlinarith only [hrem]
  change poly8 (center8 m) = 5*poly8 (center8 n) at heq
  rw [hcenter] at heq
  have hq2 : 81 ≤ (center8 n)^2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (center8 n)^2-81 by omega) (sq_nonneg (center8 n))
  dsimp [poly8] at heq
  nlinarith only [heq,hq2,hmul]

def cut8 (n : Fin 68) : ℕ :=
  ([1, 3, 4, 6, 7, 9, 10, 12, 14, 15, 17, 18, 20, 21, 23, 24, 26, 27, 29, 30, 32, 33, 35, 36, 38, 39, 41, 42, 44, 45, 47, 48, 50, 51, 53, 54, 56, 57, 59, 60, 61, 63, 64, 66, 67, 69, 70, 72, 73, 75, 76, 78, 79, 81, 82, 84, 85, 87, 88, 90, 91, 93, 94, 96, 97, 99, 100, 102] : List ℕ).getD n 0

lemma certificate8 (n : Fin 68) :
    block8 (cut8 n) < 25*block8 n ∧ 25*block8 n < block8 (cut8 n+1) := by
  revert n
  decide +kernel

lemma block8_strictMono : StrictMono block8 := by
  intro a b hab
  dsimp [block8]
  gcongr

/-- Every bounded candidate is excluded by a kernel-checked bracketing certificate. -/
theorem finite_check8 (n m : ℕ) (hn : n ≤ 67) : block8 m ≠ 25*block8 n := by
  intro h
  let i : Fin 68 := ⟨n, by omega⟩
  obtain ⟨hlo,hhi⟩ := certificate8 i
  change block8 (cut8 i) < 25*block8 n at hlo
  change 25*block8 n < block8 (cut8 i+1) at hhi
  by_cases hm : m ≤ cut8 i
  · have hmono := block8_strictMono.monotone hm
    omega
  · have hmono := block8_strictMono.monotone (show cut8 i+1 ≤ m by omega)
    omega

/-- Ratio 25 is impossible at length eight, even without disjointness. -/
theorem length_eight (m n : ℕ) : block8 m ≠ 25*block8 n := by
  intro h
  have hmn : n ≤ m := by
    by_contra hn
    have hlt := block8_strictMono (show m < n by omega)
    have hp : 0 < block8 n := by dsimp [block8]; positivity
    omega
  exact finite_check8 n m (bound8 n m hmn h) h

/-- Direct use at the length-eight rational-product obligation. -/
theorem no_ratio_eight (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 8, (m+i)) / (∏ i ∈ Finset.Icc 1 8, (n+i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*(n+7)*(n+8) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 25*block8 n = block8 m := by dsimp [block8]; exact_mod_cast hz
  exact length_eight m n hn.symm


def block12 (n : ℕ) : ℕ := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*
  (n+7)*(n+8)*(n+9)*(n+10)*(n+11)*(n+12)
def w12 (n : ℕ) : ℤ := (2*n+13)^2
def poly12 (w : ℤ) : ℤ := w^3-143*w^2+4147*w-24453
def residual12 (w : ℤ) : ℤ := 429*w^2-14274*w+94501
def near12 (n : ℕ) : ℤ := poly12 (w12 n)
def rem12 (n : ℕ) : ℤ := 5184*residual12 (w12 n)

lemma identity12 (n : ℕ) : (near12 n)^2-4096*(block12 n : ℤ)=rem12 n := by
  simp only [near12, poly12, w12, rem12, residual12, block12,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma w12_ge (n : ℕ) : 169 ≤ w12 n := by
  have hn : (0:ℤ) ≤ n := by positivity
  dsimp [w12]
  nlinarith

lemma residual12_pos (w : ℤ) (hw : 169 ≤ w) : 0 < residual12 w := by
  dsimp [residual12]
  nlinarith [sq_nonneg (w-169)]

lemma near12_pos (n : ℕ) : 0 < near12 n := by
  have hw := w12_ge n
  have hmul := mul_nonneg (show 0 ≤ w12 n-143 by omega) (sq_nonneg (w12 n))
  dsimp [near12, poly12]
  nlinarith

lemma rem12_pos (n : ℕ) : 0 < rem12 n := by
  have hr := residual12_pos (w12 n) (w12_ge n)
  dsimp [rem12]
  omega

/-- Cross multiplication proves strict increase of the polynomial/remainder ratio. -/
lemma cross12_pos (u v : ℤ) (hv : 169 ≤ v) (hu : v < u) :
    0 < poly12 u*residual12 v-poly12 v*residual12 u := by
  let d := u-v
  let z := v-169
  have hd : 0 < d := by dsimp [d]; omega
  have hz : 0 ≤ z := by dsimp [z]; omega
  have hid : poly12 u*residual12 v-poly12 v*residual12 u = d*(
      (429*z^2+130728*z+9934864)*d^2 +
      (858*z^3+392184*z^2+59587800*z+3007549792)*d +
      429*z^4+261456*z^3+59587800*z^2+6015099584*z+226757222016) := by
    dsimp [poly12, residual12, d, z]
    ring
  rw [hid]
  positivity

lemma error12_small (n : ℕ) (hn : 1661 ≤ n) : 5*rem12 n < near12 n := by
  have hc : (1661:ℤ) ≤ n := by exact_mod_cast hn
  have hw : 11119823 ≤ w12 n := by dsimp [w12]; nlinarith
  have hrem : rem12 n < 2223936*(w12 n)^2 := by
    dsimp [rem12, residual12]
    nlinarith only [hw]
  have hnear : (w12 n)^3-143*(w12 n)^2 < near12 n := by
    dsimp [near12, poly12]
    nlinarith only [hw]
  have hmul := mul_nonneg (show 0 ≤ w12 n-11119823 by omega) (sq_nonneg (w12 n))
  nlinarith only [hrem,hnear,hmul]

lemma block12_strictMono : StrictMono block12 := by
  intro a b hab
  dsimp [block12]
  gcongr

/-- The explicit finite bound for the length-twelve equation. -/
theorem bound12 (n m : ℕ) (hmn : n ≤ m)
    (h : block12 m = 25*block12 n) : n ≤ 1660 := by
  by_contra hn
  have hn' : 1661 ≤ n := by omega
  have hm' : 1661 ≤ m := by omega
  have hnid := identity12 n
  have hmid := identity12 m
  have hz : (block12 m : ℤ) = 25*(block12 n : ℤ) := by exact_mod_cast h
  have hp := near12_pos m
  have hq := near12_pos n
  have hc := rem12_pos m
  have hd := rem12_pos n
  have hsm := error12_small m hm'
  have hsn := error12_small n hn'
  have heq := square_gap_force (near12 m) (5*near12 n) (rem12 m) (25*rem12 n)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by nlinarith only [hnid,hmid,hz])
  have hrem : rem12 m = 25*rem12 n := by
    rw [heq] at hmid
    nlinarith only [hnid,hmid,hz]
  have hr : residual12 (w12 m) = 25*residual12 (w12 n) := by
    dsimp [rem12] at hrem
    linarith only [hrem]
  have hnm : n < m := by
    have hbp : 0 < block12 n := by dsimp [block12]; positivity
    by_contra hnot
    have he : m=n := by omega
    rw [he] at h
    omega
  have hwm : w12 n < w12 m := by
    have hnmz : (n:ℤ) < m := by exact_mod_cast hnm
    have hprod := mul_pos (show 0 < (m:ℤ)-n by omega)
      (show 0 < 4*((m:ℤ)+n)+52 by positivity)
    dsimp [w12]
    nlinarith only [hprod]
  have hcross := cross12_pos (w12 m) (w12 n) (w12_ge n) hwm
  change 0 < near12 m*residual12 (w12 n)-near12 n*residual12 (w12 m) at hcross
  rw [heq,hr] at hcross
  have hprod := mul_pos hq (residual12_pos (w12 n) (w12_ge n))
  nlinarith only [hcross,hprod]

/-- The finite bracketing data; no external computation is a proof premise. -/
def table12 : List ℕ :=
  [1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22, 24, 25, 26, 28, 29, 30, 31,
    33, 34, 35, 37, 38, 39, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 58, 59, 60, 62, 63,
    64, 66, 67, 68, 69, 71, 72, 73, 75, 76, 77, 79, 80, 81, 83, 84, 85, 86, 88, 89, 90, 92, 93, 94,
    96, 97, 98, 100, 101, 102, 103, 105, 106, 107, 109, 110, 111, 113, 114, 115, 117, 118, 119, 120, 122, 123, 124, 126,
    127, 128, 130, 131, 132, 134, 135, 136, 137, 139, 140, 141, 143, 144, 145, 147, 148, 149, 151, 152, 153, 154, 156, 157,
    158, 160, 161, 162, 164, 165, 166, 168, 169, 170, 171, 173, 174, 175, 177, 178, 179, 181, 182, 183, 185, 186, 187, 188,
    190, 191, 192, 194, 195, 196, 198, 199, 200, 202, 203, 204, 205, 207, 208, 209, 211, 212, 213, 215, 216, 217, 219, 220,
    221, 222, 224, 225, 226, 228, 229, 230, 232, 233, 234, 236, 237, 238, 239, 241, 242, 243, 245, 246, 247, 249, 250, 251,
    253, 254, 255, 256, 258, 259, 260, 262, 263, 264, 266, 267, 268, 270, 271, 272, 273, 275, 276, 277, 279, 280, 281, 283,
    284, 285, 287, 288, 289, 290, 292, 293, 294, 296, 297, 298, 300, 301, 302, 304, 305, 306, 307, 309, 310, 311, 313, 314,
    315, 317, 318, 319, 321, 322, 323, 324, 326, 327, 328, 330, 331, 332, 334, 335, 336, 338, 339, 340, 341, 343, 344, 345,
    347, 348, 349, 351, 352, 353, 355, 356, 357, 358, 360, 361, 362, 364, 365, 366, 368, 369, 370, 372, 373, 374, 375, 377,
    378, 379, 381, 382, 383, 385, 386, 387, 389, 390, 391, 392, 394, 395, 396, 398, 399, 400, 402, 403, 404, 406, 407, 408,
    409, 411, 412, 413, 415, 416, 417, 419, 420, 421, 423, 424, 425, 426, 428, 429, 430, 432, 433, 434, 436, 437, 438, 440,
    441, 442, 443, 445, 446, 447, 449, 450, 451, 453, 454, 455, 457, 458, 459, 460, 462, 463, 464, 466, 467, 468, 470, 471,
    472, 474, 475, 476, 477, 479, 480, 481, 483, 484, 485, 487, 488, 489, 491, 492, 493, 494, 496, 497, 498, 500, 501, 502,
    504, 505, 506, 508, 509, 510, 511, 513, 514, 515, 517, 518, 519, 521, 522, 523, 525, 526, 527, 528, 530, 531, 532, 534,
    535, 536, 538, 539, 540, 542, 543, 544, 545, 547, 548, 549, 551, 552, 553, 555, 556, 557, 559, 560, 561, 562, 564, 565,
    566, 568, 569, 570, 572, 573, 574, 576, 577, 578, 579, 581, 582, 583, 585, 586, 587, 589, 590, 591, 593, 594, 595, 596,
    598, 599, 600, 602, 603, 604, 606, 607, 608, 610, 611, 612, 613, 615, 616, 617, 619, 620, 621, 623, 624, 625, 627, 628,
    629, 630, 632, 633, 634, 636, 637, 638, 640, 641, 642, 644, 645, 646, 647, 649, 650, 651, 653, 654, 655, 657, 658, 659,
    661, 662, 663, 664, 666, 667, 668, 670, 671, 672, 674, 675, 676, 678, 679, 680, 681, 683, 684, 685, 687, 688, 689, 691,
    692, 693, 695, 696, 697, 698, 700, 701, 702, 704, 705, 706, 708, 709, 710, 712, 713, 714, 715, 717, 718, 719, 721, 722,
    723, 725, 726, 727, 729, 730, 731, 732, 734, 735, 736, 738, 739, 740, 742, 743, 744, 746, 747, 748, 749, 751, 752, 753,
    755, 756, 757, 759, 760, 761, 763, 764, 765, 766, 768, 769, 770, 772, 773, 774, 776, 777, 778, 780, 781, 782, 783, 785,
    786, 787, 789, 790, 791, 793, 794, 795, 797, 798, 799, 800, 802, 803, 804, 806, 807, 808, 810, 811, 812, 814, 815, 816,
    817, 819, 820, 821, 823, 824, 825, 827, 828, 829, 831, 832, 833, 834, 836, 837, 838, 840, 841, 842, 844, 845, 846, 848,
    849, 850, 851, 853, 854, 855, 857, 858, 859, 861, 862, 863, 865, 866, 867, 868, 870, 871, 872, 874, 875, 876, 878, 879,
    880, 882, 883, 884, 885, 887, 888, 889, 891, 892, 893, 895, 896, 897, 899, 900, 901, 902, 904, 905, 906, 908, 909, 910,
    912, 913, 914, 916, 917, 918, 919, 921, 922, 923, 925, 926, 927, 929, 930, 931, 933, 934, 935, 936, 938, 939, 940, 942,
    943, 944, 946, 947, 948, 950, 951, 952, 953, 955, 956, 957, 959, 960, 961, 963, 964, 965, 967, 968, 969, 970, 972, 973,
    974, 976, 977, 978, 980, 981, 982, 984, 985, 986, 987, 989, 990, 991, 993, 994, 995, 997, 998, 999, 1001, 1002, 1003, 1004,
    1006, 1007, 1008, 1010, 1011, 1012, 1014, 1015, 1016, 1018, 1019, 1020, 1021, 1023, 1024, 1025, 1027, 1028, 1029, 1031, 1032, 1033, 1035, 1036,
    1037, 1038, 1040, 1041, 1042, 1044, 1045, 1046, 1048, 1049, 1050, 1052, 1053, 1054, 1055, 1057, 1058, 1059, 1061, 1062, 1063, 1065, 1066, 1067,
    1069, 1070, 1071, 1072, 1074, 1075, 1076, 1078, 1079, 1080, 1082, 1083, 1084, 1086, 1087, 1088, 1089, 1091, 1092, 1093, 1095, 1096, 1097, 1099,
    1100, 1101, 1103, 1104, 1105, 1106, 1108, 1109, 1110, 1112, 1113, 1114, 1116, 1117, 1118, 1120, 1121, 1122, 1123, 1125, 1126, 1127, 1129, 1130,
    1131, 1133, 1134, 1135, 1137, 1138, 1139, 1140, 1142, 1143, 1144, 1146, 1147, 1148, 1150, 1151, 1152, 1154, 1155, 1156, 1157, 1159, 1160, 1161,
    1163, 1164, 1165, 1167, 1168, 1169, 1171, 1172, 1173, 1174, 1176, 1177, 1178, 1180, 1181, 1182, 1184, 1185, 1186, 1188, 1189, 1190, 1191, 1193,
    1194, 1195, 1197, 1198, 1199, 1201, 1202, 1203, 1205, 1206, 1207, 1208, 1210, 1211, 1212, 1214, 1215, 1216, 1218, 1219, 1220, 1222, 1223, 1224,
    1225, 1227, 1228, 1229, 1231, 1232, 1233, 1235, 1236, 1237, 1239, 1240, 1241, 1242, 1244, 1245, 1246, 1248, 1249, 1250, 1252, 1253, 1254, 1256,
    1257, 1258, 1259, 1261, 1262, 1263, 1265, 1266, 1267, 1269, 1270, 1271, 1273, 1274, 1275, 1276, 1278, 1279, 1280, 1282, 1283, 1284, 1286, 1287,
    1288, 1290, 1291, 1292, 1293, 1295, 1296, 1297, 1299, 1300, 1301, 1303, 1304, 1305, 1307, 1308, 1309, 1310, 1312, 1313, 1314, 1316, 1317, 1318,
    1320, 1321, 1322, 1324, 1325, 1326, 1327, 1329, 1330, 1331, 1333, 1334, 1335, 1337, 1338, 1339, 1341, 1342, 1343, 1344, 1346, 1347, 1348, 1350,
    1351, 1352, 1354, 1355, 1356, 1358, 1359, 1360, 1361, 1363, 1364, 1365, 1367, 1368, 1369, 1371, 1372, 1373, 1375, 1376, 1377, 1378, 1380, 1381,
    1382, 1384, 1385, 1386, 1388, 1389, 1390, 1392, 1393, 1394, 1395, 1397, 1398, 1399, 1401, 1402, 1403, 1405, 1406, 1407, 1409, 1410, 1411, 1412,
    1414, 1415, 1416, 1418, 1419, 1420, 1422, 1423, 1424, 1426, 1427, 1428, 1429, 1431, 1432, 1433, 1435, 1436, 1437, 1439, 1440, 1441, 1443, 1444,
    1445, 1446, 1448, 1449, 1450, 1452, 1453, 1454, 1456, 1457, 1458, 1460, 1461, 1462, 1463, 1465, 1466, 1467, 1469, 1470, 1471, 1473, 1474, 1475,
    1477, 1478, 1479, 1480, 1482, 1483, 1484, 1486, 1487, 1488, 1490, 1491, 1492, 1494, 1495, 1496, 1497, 1499, 1500, 1501, 1503, 1504, 1505, 1507,
    1508, 1509, 1511, 1512, 1513, 1514, 1516, 1517, 1518, 1520, 1521, 1522, 1524, 1525, 1526, 1528, 1529, 1530, 1531, 1533, 1534, 1535, 1537, 1538,
    1539, 1541, 1542, 1543, 1545, 1546, 1547, 1548, 1550, 1551, 1552, 1554, 1555, 1556, 1558, 1559, 1560, 1562, 1563, 1564, 1565, 1567, 1568, 1569,
    1571, 1572, 1573, 1575, 1576, 1577, 1579, 1580, 1581, 1582, 1584, 1585, 1586, 1588, 1589, 1590, 1592, 1593, 1594, 1596, 1597, 1598, 1599, 1601,
    1602, 1603, 1605, 1606, 1607, 1609, 1610, 1611, 1613, 1614, 1615, 1616, 1618, 1619, 1620, 1622, 1623, 1624, 1626, 1627, 1628, 1630, 1631, 1632,
    1633, 1635, 1636, 1637, 1639, 1640, 1641, 1643, 1644, 1645, 1647, 1648, 1649, 1650, 1652, 1653, 1654, 1656, 1657, 1658, 1660, 1661, 1662, 1664,
    1665, 1666, 1667, 1669, 1670, 1671, 1673, 1674, 1675, 1677, 1678, 1679, 1681, 1682, 1683, 1684, 1686, 1687, 1688, 1690, 1691, 1692, 1694, 1695,
    1696, 1698, 1699, 1700, 1701, 1703, 1704, 1705, 1707, 1708, 1709, 1711, 1712, 1713, 1715, 1716, 1717, 1718, 1720, 1721, 1722, 1724, 1725, 1726,
    1728, 1729, 1730, 1732, 1733, 1734, 1735, 1737, 1738, 1739, 1741, 1742, 1743, 1745, 1746, 1747, 1749, 1750, 1751, 1752, 1754, 1755, 1756, 1758,
    1759, 1760, 1762, 1763, 1764, 1766, 1767, 1768, 1769, 1771, 1772, 1773, 1775, 1776, 1777, 1779, 1780, 1781, 1783, 1784, 1785, 1786, 1788, 1789,
    1790, 1792, 1793, 1794, 1796, 1797, 1798, 1800, 1801, 1802, 1803, 1805, 1806, 1807, 1809, 1810, 1811, 1813, 1814, 1815, 1817, 1818, 1819, 1820,
    1822, 1823, 1824, 1826, 1827, 1828, 1830, 1831, 1832, 1834, 1835, 1836, 1837, 1839, 1840, 1841, 1843, 1844, 1845, 1847, 1848, 1849, 1851, 1852,
    1853, 1854, 1856, 1857, 1858, 1860, 1861, 1862, 1864, 1865, 1866, 1868, 1869, 1870, 1871, 1873, 1874, 1875, 1877, 1878, 1879, 1881, 1882, 1883,
    1885, 1886, 1887, 1888, 1890, 1891, 1892, 1894, 1895, 1896, 1898, 1899, 1900, 1902, 1903, 1904, 1905, 1907, 1908, 1909, 1911, 1912, 1913, 1915,
    1916, 1917, 1919, 1920, 1921, 1922, 1924, 1925, 1926, 1928, 1929, 1930, 1932, 1933, 1934, 1936, 1937, 1938, 1939, 1941, 1942, 1943, 1945, 1946,
    1947, 1949, 1950, 1951, 1953, 1954, 1955, 1956, 1958, 1959, 1960, 1962, 1963, 1964, 1966, 1967, 1968, 1970, 1971, 1972, 1973, 1975, 1976, 1977,
    1979, 1980, 1981, 1983, 1984, 1985, 1987, 1988, 1989, 1990, 1992, 1993, 1994, 1996, 1997, 1998, 2000, 2001, 2002, 2004, 2005, 2006, 2007, 2009,
    2010, 2011, 2013, 2014, 2015, 2017, 2018, 2019, 2021, 2022, 2023, 2024, 2026, 2027, 2028, 2030, 2031, 2032, 2034, 2035, 2036, 2038, 2039, 2040,
    2041, 2043, 2044, 2045, 2047, 2048, 2049, 2051, 2052, 2053, 2055, 2056, 2057, 2058, 2060, 2061, 2062, 2064, 2065, 2066, 2068, 2069, 2070, 2072,
    2073, 2074, 2075, 2077, 2078, 2079, 2081, 2082, 2083, 2085, 2086, 2087, 2089, 2090, 2091, 2092, 2094, 2095, 2096, 2098, 2099, 2100, 2102, 2103,
    2104, 2106, 2107, 2108, 2109, 2111, 2112, 2113, 2115, 2116, 2117, 2119, 2120, 2121, 2123, 2124, 2125, 2126, 2128, 2129, 2130, 2132, 2133, 2134,
    2136, 2137, 2138, 2140, 2141, 2142, 2143, 2145, 2146, 2147, 2149, 2150, 2151, 2153, 2154, 2155, 2157, 2158, 2159, 2160, 2162, 2163, 2164, 2166,
    2167, 2168, 2170, 2171, 2172]

def row12 (n m : ℕ) : Prop :=
  block12 m ≤ 25*block12 n ∧ 25*block12 n < block12 (m+1) ∧
  (block12 m = 25*block12 n → False)

instance row12_decidable (n m : ℕ) : Decidable (row12 n m) := by
  unfold row12
  infer_instance

def checkTable12 (n : ℕ) : List ℕ → Bool
  | [] => true
  | m :: ms => decide (row12 n m) && checkTable12 (n+1) ms

lemma checkTable12_sound (ms : List ℕ) (n : ℕ)
    (h : checkTable12 n ms = true) (i : ℕ) (hi : i < ms.length) :
    row12 (n+i) (ms.getD i 0) := by
  induction ms generalizing n i with
  | nil => simp at hi
  | cons m ms ih =>
    simp only [checkTable12, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < ms.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n+1) h.2 i hi'

set_option maxRecDepth 4096 in
lemma table12_valid : checkTable12 0 table12 = true := by decide +kernel

def cut12 (n : Fin 1661) : ℕ := table12.getD n 0

set_option maxRecDepth 4096 in
lemma certificate12 (n : Fin 1661) :
    block12 (cut12 n) ≤ 25*block12 n ∧
    25*block12 n < block12 (cut12 n+1) ∧
    (block12 (cut12 n) = 25*block12 n → False) := by
  have hi : (n:ℕ) < table12.length := by change (n:ℕ) < 1661; exact n.isLt
  simpa [row12, cut12] using checkTable12_sound table12 0 table12_valid n hi

/-- Complete classification of the bounded candidates. -/
theorem finite_check12 (n m : ℕ) (hn : n ≤ 1660)
    (h : block12 m = 25*block12 n) : False := by
  let i : Fin 1661 := ⟨n, by omega⟩
  obtain ⟨hlo,hhi,heq⟩ := certificate12 i
  change block12 (cut12 i) ≤ 25*block12 n at hlo
  change 25*block12 n < block12 (cut12 i+1) at hhi
  have hmle : m ≤ cut12 i := by
    by_contra hnot
    have hmono := block12_strictMono.monotone (show cut12 i+1 ≤ m by omega)
    omega
  have hmge : cut12 i ≤ m := by
    by_contra hnot
    have hmono := block12_strictMono (show m < cut12 i by omega)
    omega
  have hmc : m=cut12 i := by omega
  have hci : block12 (cut12 i) = 25*block12 i := by simpa [i, ← hmc] using h
  exact heq hci

/-- Equality forces the upper block to start no earlier than the lower block. -/
lemma solution12_monotone (m n : ℕ) (h : block12 m = 25*block12 n) : n ≤ m := by
  by_contra hn
  have hlt := block12_strictMono (show m < n by omega)
  have hp : 0 < block12 n := by dsimp [block12]; positivity
  omega

/-- Ratio 25 is impossible at length twelve, even without disjointness. -/
theorem length_twelve (m n : ℕ) : block12 m ≠ 25*block12 n := by
  intro h
  have hf := finite_check12 n m (bound12 n m (solution12_monotone m n h) h) h
  exact hf

/-- Direct use at the length-twelve rational-product obligation. -/
theorem no_ratio_twelve (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 12, (m+i)) / (∏ i ∈ Finset.Icc 1 12, (n+i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*
    (n+7)*(n+8)*(n+9)*(n+10)*(n+11)*(n+12) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 25*block12 n = block12 m := by dsimp [block12]; exact_mod_cast hz
  exact length_twelve m n hn.symm

end Contribution.Erdos686EightTwelveTwentyFive
