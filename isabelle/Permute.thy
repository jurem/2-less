theory Permute
  imports Main Seq2less
begin

(* Here we play with permutability of triplet components of 2-less sequences. *)

(* Permutations (redundant) of a triplet *)

fun swap_12 :: "Tri \<Rightarrow> Tri" where
  "swap_12 (x1, x2, x3) = (x2, x1, x3)"

fun swap_13 :: "Tri \<Rightarrow> Tri" where
  "swap_13 (x1, x2, x3) = (x3, x2, x1)"

fun swap_23 :: "Tri \<Rightarrow> Tri" where
  "swap_23 (x1, x2, x3) =  (x1, x3, x2)"

fun rot_r :: "Tri \<Rightarrow> Tri" where
  "rot_r (x1, x2, x3) =  (x3, x1, x2)"

fun rot_l :: "Tri \<Rightarrow> Tri" where
  "rot_l (x1, x2, x3) =  (x2, x3, x1)"

(* Function perm gathers all of the above transformations. *)

datatype Perm = Swap12 | Swap13 | Swap23 | RotR | RotL

fun perm :: "Perm \<Rightarrow> Tri \<Rightarrow> Tri" where
  "perm k t = (case k of
    Swap12 \<Rightarrow> swap_12 t |
    Swap13 \<Rightarrow> swap_13 t |
    Swap23 \<Rightarrow> swap_23 t |
    RotR \<Rightarrow> rot_r t |
    RotL \<Rightarrow> rot_l t)"

(* Given a pf transform a sequence by applying pf on each element. *)

primrec permute :: "(Tri \<Rightarrow> Tri) \<Rightarrow> Tri list \<Rightarrow> Tri list" where
  "permute pf [] = []" |
  "permute pf (h#t) = ((pf h)#(permute pf t))"


(* Lemmata *)

(* Transformation of triplets preserves 2-lessness (for \<prec>, lt_all, is_2less) *)

lemma permutability_lt:
  "(x \<prec> y) \<longrightarrow> (perm k x \<prec> perm k y)"
  apply (simp add: split_def)
  by (smt Perm.exhaust Perm.simps(21) Perm.simps(22) Perm.simps(23) Perm.simps(24) Perm.simps(25) lt.elims(2) lt.simps rot_l.simps rot_r.simps swap_12.simps swap_13.simps swap_23.simps)

lemma permutability_lt_all:
  "lt_all x t \<longrightarrow> lt_all (perm k x) (permute (perm k) t)"
  apply (induction t arbitrary: k)
  using permutability_lt
  by auto

theorem permutability_is_2less:
  "is_2less t \<longrightarrow> is_2less (permute (perm k) t)"
  apply (induction t arbitrary: k)
  using permutability_lt permutability_lt_all
  by auto

end
