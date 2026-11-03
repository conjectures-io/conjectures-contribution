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

namespace Contribution.Erdos686EightTwelveFour

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

lemma error8_small (n : ℕ) (hn : 41 ≤ n) : 2*rem8 n < near8 n := by
  have hq : 91 ≤ center8 n := by dsimp [center8]; omega
  have hq2 : 8234 ≤ (center8 n)^2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (center8 n)^2-8234 by omega) (sq_nonneg (center8 n))
  dsimp [near8, poly8, rem8]
  nlinarith

/-- The explicit finite bound for the length-eight equation. -/
theorem bound8 (n m : ℕ) (hmn : n ≤ m)
    (h : block8 m = 4*block8 n) : n ≤ 40 := by
  by_contra hn
  have hn' : 41 ≤ n := by omega
  have hm' : 41 ≤ m := by omega
  have hnid := identity8 n
  have hmid := identity8 m
  have hz : (block8 m : ℤ) = 4*(block8 n : ℤ) := by exact_mod_cast h
  have hp := near8_pos m
  have hq := near8_pos n
  have hc := rem8_nonneg m
  have hd := rem8_nonneg n
  have hsm := error8_small m hm'
  have hsn := error8_small n hn'
  have heq := square_gap_force (near8 m) (2*near8 n) (rem8 m) (4*rem8 n)
    (by omega) (by omega) hc (by omega) (by omega) (by omega) (by nlinarith only [hnid,hmid,hz])
  have hrem : rem8 m = 4*rem8 n := by
    rw [heq] at hmid
    nlinarith only [hnid,hmid,hz]
  have hcm := center8_ge m
  have hcn := center8_ge n
  have hcenter : center8 m = 2*center8 n := by
    apply (sq_eq_sq₀ (by omega : 0 ≤ center8 m) (by omega : 0 ≤ 2*center8 n)).mp
    dsimp [rem8] at hrem
    nlinarith only [hrem]
  change poly8 (center8 m) = 2*poly8 (center8 n) at heq
  rw [hcenter] at heq
  have hq2 : 81 ≤ (center8 n)^2 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (center8 n)^2-81 by omega) (sq_nonneg (center8 n))
  dsimp [poly8] at heq
  nlinarith only [heq,hq2,hmul]

def cut8 (n : Fin 41) : ℕ :=
  ([0, 1, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 46, 47, 48] : List ℕ).getD n 0

lemma certificate8 (n : Fin 41) :
    block8 (cut8 n) < 4*block8 n ∧ 4*block8 n < block8 (cut8 n+1) := by
  revert n
  decide +kernel

lemma block8_strictMono : StrictMono block8 := by
  intro a b hab
  dsimp [block8]
  gcongr

/-- Every bounded candidate is excluded by a kernel-checked bracketing certificate. -/
theorem finite_check8 (n m : ℕ) (hn : n ≤ 40) : block8 m ≠ 4*block8 n := by
  intro h
  let i : Fin 41 := ⟨n, by omega⟩
  obtain ⟨hlo,hhi⟩ := certificate8 i
  change block8 (cut8 i) < 4*block8 n at hlo
  change 4*block8 n < block8 (cut8 i+1) at hhi
  by_cases hm : m ≤ cut8 i
  · have hmono := block8_strictMono.monotone hm
    omega
  · have hmono := block8_strictMono.monotone (show cut8 i+1 ≤ m by omega)
    omega

/-- Ratio 4 is impossible at length eight, even without disjointness. -/
theorem length_eight (m n : ℕ) : block8 m ≠ 4*block8 n := by
  intro h
  have hmn : n ≤ m := by
    by_contra hn
    have hlt := block8_strictMono (show m < n by omega)
    have hp : 0 < block8 n := by dsimp [block8]; positivity
    omega
  exact finite_check8 n m (bound8 n m hmn h) h

/-- Direct use at the length-eight rational-product obligation. -/
theorem no_ratio_eight (m n : ℕ) :
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 8, (m+i)) / (∏ i ∈ Finset.Icc 1 8, (n+i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*(n+7)*(n+8) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 4*block8 n = block8 m := by dsimp [block8]; exact_mod_cast hz
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

lemma error12_small (n : ℕ) (hn : 1049 ≤ n) : 2*rem12 n < near12 n := by
  have hc : (1049:ℤ) ≤ n := by exact_mod_cast hn
  have hw : 4448015 ≤ w12 n := by dsimp [w12]; nlinarith
  have hrem : rem12 n < 2223936*(w12 n)^2 := by
    dsimp [rem12, residual12]
    nlinarith only [hw]
  have hnear : (w12 n)^3-143*(w12 n)^2 < near12 n := by
    dsimp [near12, poly12]
    nlinarith only [hw]
  have hmul := mul_nonneg (show 0 ≤ w12 n-4448015 by omega) (sq_nonneg (w12 n))
  nlinarith only [hrem,hnear,hmul]

lemma block12_strictMono : StrictMono block12 := by
  intro a b hab
  dsimp [block12]
  gcongr

/-- The explicit finite bound for the length-twelve equation. -/
theorem bound12 (n m : ℕ) (hmn : n ≤ m)
    (h : block12 m = 4*block12 n) : n ≤ 1048 := by
  by_contra hn
  have hn' : 1049 ≤ n := by omega
  have hm' : 1049 ≤ m := by omega
  have hnid := identity12 n
  have hmid := identity12 m
  have hz : (block12 m : ℤ) = 4*(block12 n : ℤ) := by exact_mod_cast h
  have hp := near12_pos m
  have hq := near12_pos n
  have hc := rem12_pos m
  have hd := rem12_pos n
  have hsm := error12_small m hm'
  have hsn := error12_small n hn'
  have heq := square_gap_force (near12 m) (2*near12 n) (rem12 m) (4*rem12 n)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by nlinarith only [hnid,hmid,hz])
  have hrem : rem12 m = 4*rem12 n := by
    rw [heq] at hmid
    nlinarith only [hnid,hmid,hz]
  have hr : residual12 (w12 m) = 4*residual12 (w12 n) := by
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
  [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26,
    27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53,
    54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 78, 79, 80,
    81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107,
    108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 134,
    135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161,
    162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 177, 178, 179, 180, 181, 182, 183, 184, 185, 187, 188,
    189, 190, 191, 192, 193, 194, 196, 197, 198, 199, 200, 201, 202, 203, 205, 206, 207, 208, 209, 210, 211, 212, 214, 215,
    216, 217, 218, 219, 220, 221, 223, 224, 225, 226, 227, 228, 229, 230, 232, 233, 234, 235, 236, 237, 238, 239, 240, 242,
    243, 244, 245, 246, 247, 248, 249, 251, 252, 253, 254, 255, 256, 257, 258, 260, 261, 262, 263, 264, 265, 266, 267, 269,
    270, 271, 272, 273, 274, 275, 276, 278, 279, 280, 281, 282, 283, 284, 285, 287, 288, 289, 290, 291, 292, 293, 294, 295,
    297, 298, 299, 300, 301, 302, 303, 304, 306, 307, 308, 309, 310, 311, 312, 313, 315, 316, 317, 318, 319, 320, 321, 322,
    324, 325, 326, 327, 328, 329, 330, 331, 333, 334, 335, 336, 337, 338, 339, 340, 342, 343, 344, 345, 346, 347, 348, 349,
    350, 352, 353, 354, 355, 356, 357, 358, 359, 361, 362, 363, 364, 365, 366, 367, 368, 370, 371, 372, 373, 374, 375, 376,
    377, 379, 380, 381, 382, 383, 384, 385, 386, 388, 389, 390, 391, 392, 393, 394, 395, 397, 398, 399, 400, 401, 402, 403,
    404, 406, 407, 408, 409, 410, 411, 412, 413, 414, 416, 417, 418, 419, 420, 421, 422, 423, 425, 426, 427, 428, 429, 430,
    431, 432, 434, 435, 436, 437, 438, 439, 440, 441, 443, 444, 445, 446, 447, 448, 449, 450, 452, 453, 454, 455, 456, 457,
    458, 459, 461, 462, 463, 464, 465, 466, 467, 468, 469, 471, 472, 473, 474, 475, 476, 477, 478, 480, 481, 482, 483, 484,
    485, 486, 487, 489, 490, 491, 492, 493, 494, 495, 496, 498, 499, 500, 501, 502, 503, 504, 505, 507, 508, 509, 510, 511,
    512, 513, 514, 516, 517, 518, 519, 520, 521, 522, 523, 524, 526, 527, 528, 529, 530, 531, 532, 533, 535, 536, 537, 538,
    539, 540, 541, 542, 544, 545, 546, 547, 548, 549, 550, 551, 553, 554, 555, 556, 557, 558, 559, 560, 562, 563, 564, 565,
    566, 567, 568, 569, 571, 572, 573, 574, 575, 576, 577, 578, 579, 581, 582, 583, 584, 585, 586, 587, 588, 590, 591, 592,
    593, 594, 595, 596, 597, 599, 600, 601, 602, 603, 604, 605, 606, 608, 609, 610, 611, 612, 613, 614, 615, 617, 618, 619,
    620, 621, 622, 623, 624, 626, 627, 628, 629, 630, 631, 632, 633, 634, 636, 637, 638, 639, 640, 641, 642, 643, 645, 646,
    647, 648, 649, 650, 651, 652, 654, 655, 656, 657, 658, 659, 660, 661, 663, 664, 665, 666, 667, 668, 669, 670, 672, 673,
    674, 675, 676, 677, 678, 679, 681, 682, 683, 684, 685, 686, 687, 688, 689, 691, 692, 693, 694, 695, 696, 697, 698, 700,
    701, 702, 703, 704, 705, 706, 707, 709, 710, 711, 712, 713, 714, 715, 716, 718, 719, 720, 721, 722, 723, 724, 725, 727,
    728, 729, 730, 731, 732, 733, 734, 736, 737, 738, 739, 740, 741, 742, 743, 744, 746, 747, 748, 749, 750, 751, 752, 753,
    755, 756, 757, 758, 759, 760, 761, 762, 764, 765, 766, 767, 768, 769, 770, 771, 773, 774, 775, 776, 777, 778, 779, 780,
    782, 783, 784, 785, 786, 787, 788, 789, 791, 792, 793, 794, 795, 796, 797, 798, 799, 801, 802, 803, 804, 805, 806, 807,
    808, 810, 811, 812, 813, 814, 815, 816, 817, 819, 820, 821, 822, 823, 824, 825, 826, 828, 829, 830, 831, 832, 833, 834,
    835, 837, 838, 839, 840, 841, 842, 843, 844, 846, 847, 848, 849, 850, 851, 852, 853, 854, 856, 857, 858, 859, 860, 861,
    862, 863, 865, 866, 867, 868, 869, 870, 871, 872, 874, 875, 876, 877, 878, 879, 880, 881, 883, 884, 885, 886, 887, 888,
    889, 890, 892, 893, 894, 895, 896, 897, 898, 899, 901, 902, 903, 904, 905, 906, 907, 908, 909, 911, 912, 913, 914, 915,
    916, 917, 918, 920, 921, 922, 923, 924, 925, 926, 927, 929, 930, 931, 932, 933, 934, 935, 936, 938, 939, 940, 941, 942,
    943, 944, 945, 947, 948, 949, 950, 951, 952, 953, 954, 956, 957, 958, 959, 960, 961, 962, 963, 964, 966, 967, 968, 969,
    970, 971, 972, 973, 975, 976, 977, 978, 979, 980, 981, 982, 984, 985, 986, 987, 988, 989, 990, 991, 993, 994, 995, 996,
    997, 998, 999, 1000, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1021, 1022, 1023,
    1024, 1025, 1026, 1027, 1028, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1048, 1049, 1050,
    1051, 1052, 1053, 1054, 1055, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1076, 1077,
    1078, 1079, 1080, 1081, 1082, 1083, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1103, 1104,
    1105, 1106, 1107, 1108, 1109, 1110, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1131,
    1132, 1133, 1134, 1135, 1136, 1137, 1138, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1158,
    1159, 1160, 1161, 1162, 1163, 1164, 1165, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1176, 1177]

def row12 (n m : ℕ) : Prop :=
  block12 m ≤ 4*block12 n ∧ 4*block12 n < block12 (m+1) ∧
  (block12 m = 4*block12 n → (n:ℕ)=3 ∧ m=4)

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

def cut12 (n : Fin 1049) : ℕ := table12.getD n 0

set_option maxRecDepth 4096 in
lemma certificate12 (n : Fin 1049) :
    block12 (cut12 n) ≤ 4*block12 n ∧
    4*block12 n < block12 (cut12 n+1) ∧
    (block12 (cut12 n) = 4*block12 n → (n:ℕ)=3 ∧ cut12 n=4) := by
  have hi : (n:ℕ) < table12.length := by change (n:ℕ) < 1049; exact n.isLt
  simpa [row12, cut12] using checkTable12_sound table12 0 table12_valid n hi

/-- Complete classification of the bounded candidates. -/
theorem finite_check12 (n m : ℕ) (hn : n ≤ 1048)
    (h : block12 m = 4*block12 n) : n=3 ∧ m=4 := by
  let i : Fin 1049 := ⟨n, by omega⟩
  obtain ⟨hlo,hhi,heq⟩ := certificate12 i
  change block12 (cut12 i) ≤ 4*block12 n at hlo
  change 4*block12 n < block12 (cut12 i+1) at hhi
  have hmle : m ≤ cut12 i := by
    by_contra hnot
    have hmono := block12_strictMono.monotone (show cut12 i+1 ≤ m by omega)
    omega
  have hmge : cut12 i ≤ m := by
    by_contra hnot
    have hmono := block12_strictMono (show m < cut12 i by omega)
    omega
  have hmc : m=cut12 i := by omega
  have hci : block12 (cut12 i) = 4*block12 i := by simpa [i, ← hmc] using h
  exact ⟨(heq hci).1, hmc.trans (heq hci).2⟩

/-- Equality forces the upper block to start no earlier than the lower block. -/
lemma solution12_monotone (m n : ℕ) (h : block12 m = 4*block12 n) : n ≤ m := by
  by_contra hn
  have hlt := block12_strictMono (show m < n by omega)
  have hp : 0 < block12 n := by dsimp [block12]; positivity
  omega

/-- Complete classification, including the single overlapping solution. -/
theorem length_twelve_classification (m n : ℕ) :
    block12 m = 4*block12 n ↔ n=3 ∧ m=4 := by
  constructor
  · intro h
    exact finite_check12 n m (bound12 n m (solution12_monotone m n h) h) h
  · rintro ⟨rfl,rfl⟩
    norm_num [block12]

/-- Ratio 4 is impossible for disjoint length-twelve blocks. -/
theorem length_twelve (m n : ℕ) (hmn : n+12 ≤ m) : block12 m ≠ 4*block12 n := by
  intro h
  have hf := finite_check12 n m (bound12 n m (by omega) h) h
  omega

/-- Direct use at the length-twelve rational-product obligation. -/
theorem no_ratio_twelve (m n : ℕ) (hmn : n+12 ≤ m) :
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 12, (m+i)) / (∏ i ∈ Finset.Icc 1 12, (n+i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*
    (n+7)*(n+8)*(n+9)*(n+10)*(n+11)*(n+12) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 4*block12 n = block12 m := by dsimp [block12]; exact_mod_cast hz
  exact length_twelve m n hmn hn.symm

end Contribution.Erdos686EightTwelveFour
