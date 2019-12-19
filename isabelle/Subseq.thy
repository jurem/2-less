theory Subseq
  imports Main Seq2less
begin

(* Here we play with sub-sequences of 2-less sequences. *)

(* Removal of one element from a sequence. *)

(* lt_all: removal of one element (first,last,middle) preserves lt_all. *)

lemma subseq_lt_all_remove_first:
  "lt_all x (h#t) \<longrightarrow> lt_all x t"
  by simp

lemma subseq_lt_all_remove_last:
  "lt_all x (s@[l]) \<longrightarrow> lt_all x s"
  apply (induction s)
  by auto

lemma subseq_lt_all_remove_middle:
  "lt_all x (s@h#t) \<longrightarrow> lt_all x (s@t)"
  apply (induction s)
  by auto

(* lt_2less: removal of one element (first,last,middle) preserves is_2less. *)

lemma subseq_remove_first:
  "is_2less (h#t) \<longrightarrow> is_2less t"
  by auto

lemma subseq_remove_last:
  "is_2less (s@[x]) \<longrightarrow> is_2less s"
  apply (induction s arbitrary: x)
  apply simp
  using subseq_lt_all_remove_last
  by auto

lemma subseq_remove_middle:
  "is_2less (s@x#t) \<longrightarrow> is_2less (s@t)"
  apply (induction s arbitrary: t x)
  using subseq_remove_last
  apply simp
  using subseq_lt_all_remove_middle
  by (metis append_Cons is_2less.simps(2))

(* Removal of a subsequence from a sequence. *)

(* lt_all: removal of subsequence preserves lt_all *)

lemma subseq_lt_all_prefix:
  "lt_all a (s@t) \<longrightarrow> lt_all a s"
  apply (induction s)
  by auto

lemma subseq_lt_all_postfix:
  "lt_all a (s@t) \<longrightarrow> lt_all a t"
  apply (induction s)
  by auto

lemma subseq_lt_all:
  "lt_all a (s@t) \<longrightarrow> lt_all a s \<and> lt_all a t"
  using subseq_lt_all_prefix subseq_lt_all_postfix
  by blast

(* is_2less: removal of subsequence preserves is_2less *)

lemma subseq_postfix:
  "is_2less (s@t) \<longrightarrow> is_2less t"
  apply (induction s arbitrary: t)
  apply simp
  using subseq_remove_first
  by (metis append_Cons)

lemma subseq_prefix:
  "is_2less (s@t) \<longrightarrow> is_2less s"
  apply (induction t arbitrary: s)
  apply simp
  using subseq_remove_last subseq_lt_all_remove_last
  by (metis (no_types, hide_lams) Cons_eq_appendI append_eq_appendI self_append_conv2)

corollary subseq_split_2:
  "is_2less (s@t) \<longrightarrow> is_2less s \<and> is_2less t"
  using subseq_prefix subseq_postfix
  by blast

corollary subseq_split_3:
  "is_2less (p@s@t) \<longrightarrow> is_2less p \<and> is_2less s \<and> is_2less t"
  using subseq_prefix subseq_postfix
  by blast

lemma subseq_infix:
  "is_2less (p@s@t) \<longrightarrow> is_2less (p@t)"
  apply (induction s)
  apply simp
  using subseq_remove_middle
  by auto

end
