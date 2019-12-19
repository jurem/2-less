theory Prefixes
  imports Main Seq2less Subseq Subst Permute
begin

(* Begin with zero and other prefix substitutions *)

(* (0,0,0) ... *)

lemma begin_zero:
  "is_2less (h#t) \<longrightarrow> is_2less ((0,0,0)#t)"
  apply (induction t)
  apply simp
  using lt.elims(2)
  by fastforce

(* (0,0,0) (1,0,1) ... *)
(* possible minimal candidates: (1,0,1) (0,1,1) (1,1,0) *)

lemma begin_prefix_2a:
  "is_2less ((0,0,0)#(0,1,1)#t) \<longrightarrow> is_2less ((0,0,0)#(1,0,1)#(permute (perm Swap12) t))"
  apply (induction t)
  apply simp
  by (metis Perm.simps(21) perm.elims permute.simps(2) permutability_is_2less swap_12.simps)

lemma begin_prefix_2b:
  "is_2less ((0,0,0)#(1,1,0)#t) \<longrightarrow> is_2less ((0,0,0)#(1,0,1)#(permute (perm Swap23) t))"
  apply (induction t)
  apply simp
  by (metis Perm.simps(23) perm.simps permute.simps(2) permutability_is_2less swap_23.simps)

(* (0,0,0) (1,0,1) (0,1,2) ... *)
(* possible minimal candidates: (0,1,2) (2,1,0) (2,0,2) *)

lemma begin_prefix_3_lt_all_0:
  "lt_all (0,0,0) t \<longrightarrow> lt_all (0,0,0) (permute (perm Swap13) t)"
  apply (induction t)
  apply simp
  by auto

lemma begin_prefix_3_lt_all_1:
  "lt_all (1,0,1) t \<longrightarrow> lt_all (1,0,1) (permute (perm Swap13) t)"
  apply (induction t)
  apply simp
  by auto

lemma begin_prefix_3_lt_all_2:
  "lt_all (2,1,0) t \<longrightarrow> lt_all (0,1,2) (permute (perm Swap13) t)"
  apply (induction t)
  apply simp
  by auto

corollary begin_prefix:
  "is_2less ((0,0,0)#(1,0,1)#(2,1,0)#t) \<longrightarrow> is_2less ((0,0,0)#(1,0,1)#(0,1,2)#(permute (perm Swap13) t))"
  apply (induction t)
   apply simp
  using begin_prefix_3_lt_all_0 begin_prefix_3_lt_all_1 begin_prefix_3_lt_all_2
  by (meson is_2less.simps(2) lt_all.simps(2) permutability_is_2less)

(* TODO: (2,0,2) *)

end
