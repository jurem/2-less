theory Subst
  imports Main Seq2less Subseq
begin

(* Substitutions of one element in a sequence *)

(* lt_all *)

lemma subst_lt_all:
  "le3 x y \<and> lt_all y t \<longrightarrow> lt_all x t"
  apply (induction t arbitrary: x y )
  apply simp
  by auto

lemma subst_first_lt_all:
  "le3 y x \<and> lt_all p (y#t) \<longrightarrow> lt_all p (x#t)"
  apply (induction t arbitrary: p x y )
  by auto

lemma subst_last_lt_all:
  "le3 y x \<and> lt_all p (s@[y]) \<longrightarrow> lt_all p (s@[x])"
  apply (induction s arbitrary: p x y )
  by auto

lemma subst_mid_lt_all:
  "le3 y x \<and> lt_all p (s@y#t) \<longrightarrow> lt_all p (s@x#t)"
  apply (induction s arbitrary: p x y )
  by auto

lemma subst_first_lt_all_1:
  "lt p x \<and> lt_all p (y#s) \<longrightarrow> lt_all p (x#s)"
  apply (induction s arbitrary: x y )
  by auto

lemma subst_last_lt_all_1:
  "lt p x \<and> lt_all p (s@[y]) \<longrightarrow> lt_all p (s@[x])"
  apply (induction s arbitrary: x y )
  by auto

lemma subst_mid_lt_all_1:
  "lt p x \<and> lt_all p (s@y#t) \<longrightarrow> lt_all p (s@x#t)"
  apply (induction s arbitrary: x y )
  by auto


(* is_2less *)

lemma subst_first_is_2less:
  "le3 x y \<and> is_2less (y#t) \<longrightarrow> is_2less (x#t)"
  apply (induction t arbitrary: x y )
  apply simp
  by auto

lemma subst_last_is_2less:
  "le3 y x \<and> is_2less (s@[y]) \<longrightarrow> is_2less (s@[x])"
  apply (induction s arbitrary: x y)
  apply simp
  using subseq_lt_all subst_last_lt_all
  by (metis append_Cons is_2less.simps(2))

lemma subst_mid_is_2less:
  "le3 x y \<and> gt_all x s \<and> is_2less (s@y#t) \<longrightarrow> is_2less (s@x#t)"
  apply (induction s arbitrary: x y)
  apply simp
  using subst_lt_all apply blast
  by (metis append_Cons gt_all.simps(2) is_2less.simps(2) subseq_remove_first subst_mid_lt_all_1)

lemma subst_first_is_2less_1:
  "lt_all x t \<and> is_2less (y#t) \<longrightarrow> is_2less (x#t)"
  apply (induction t arbitrary: x y )
  by auto

lemma subst_last_is_2less_1:
  "gt_all x s \<and> is_2less (s@[y]) \<longrightarrow> is_2less (s@[x])"
  apply (induction s arbitrary: x y)
  apply simp
  using subseq_prefix valid_candidate
  by blast

end
