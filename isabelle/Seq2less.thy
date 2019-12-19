theory Seq2less
  imports Main
begin

(* Here we have basic definitions of 2-less relation and sequence *)

(* Base: Triple, lt, lt_all, is_less *)

type_synonym Tri = "nat \<times> nat \<times> nat"
(* PS: We could also use nat, but then complements get complicated. *)

fun lt :: "Tri \<Rightarrow> Tri \<Rightarrow> bool" (infixl "\<prec>" 70) where
  "lt (x1, x2, x3) (y1, y2, y3) =
    (x1 < y1 \<and> (x2 < y2 \<or> x3 < y3) \<or> (x2 < y2) \<and> (x3 < y3))"

primrec lt_all :: "Tri \<Rightarrow> Tri list \<Rightarrow> bool" where
  "lt_all x [] = True" |
  "lt_all x (h#t) = (x \<prec> h \<and> lt_all x t)"

primrec is_2less :: "Tri list \<Rightarrow> bool" where
  "is_2less [] = True" |
  "is_2less (h#t) = (lt_all h t \<and> is_2less t)"


(* Addon: gt_all, valid_candidate *)

primrec gt_all :: "Tri \<Rightarrow> Tri list \<Rightarrow> bool" where
  "gt_all x [] = True" |
  "gt_all x (h#t) = (h \<prec> x \<and> gt_all x t)"

lemma relate_gt_all_to_lt_all:
  "lt_all h t \<and> gt_all x (h#t) \<longrightarrow> lt_all h (t@[x])"
  apply (induction t arbitrary: x h)
  by auto

lemma valid_candidate:
  "is_2less s \<and> gt_all x s  \<longrightarrow> is_2less (s@[x])"
  apply (induction s arbitrary: x)
  apply simp
  using relate_gt_all_to_lt_all
  by auto


(* Some additional relations *)

fun lt3 :: "Tri \<Rightarrow> Tri \<Rightarrow> bool" where
  "lt3 (x1, x2, x3) (y1, y2, y3) =
    (x1 < y1 \<and> x2 < y2 \<and> x3 < y3)"

fun le3 :: "Tri \<Rightarrow> Tri \<Rightarrow> bool" where
  "le3 (a, b, c) (x, y, z) =
	  (a \<le> x \<and> b \<le> y \<and> c \<le> z)"

lemma lt3_implies_lt:
  "lt3 x y \<longrightarrow> lt x y"
  by (smt Pair_inject lt.elims(3) lt3.elims(2))

lemma lt3_implies_le3:
  "lt3 x y \<longrightarrow> le3 x y"
  by (smt Pair_inject le3.elims(3) less_le lt3.elims(2))

lemma transitive_le3_and_lt:
  "le3 x y \<and> y \<prec> z \<longrightarrow> x \<prec> z"
  by (smt Pair_inject le3.elims(2) le_less_trans lt.elims(2) lt.elims(3))

end
