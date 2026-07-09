From caesium Require Import base byte layout.

(** Representation of an integer type (size and signedness). *)

Definition signed := bool.

Record int_type :=
  IntType {
    it_byte_size_log : nat;
    it_signed : signed;
  }.

Global Instance int_type_dec : EqDecision int_type.
Proof. solve_decision. Defined.

Definition bytes_per_int (it : int_type) : nat :=
  2 ^ it.(it_byte_size_log).

Definition bits_per_int (it : int_type) : Z :=
  bytes_per_int it * bits_per_byte.

Definition int_modulus (it : int_type) : Z :=
  2 ^ bits_per_int it.

Definition int_half_modulus (it : int_type) : Z :=
  2 ^ (bits_per_int it - 1).

(* Minimal representable integer. *)
Definition min_int (it : int_type) : Z :=
  if it.(it_signed) then - int_half_modulus it else 0.

(* Maximal representable integer. *)
Definition max_int (it : int_type) : Z :=
  (if it.(it_signed) then int_half_modulus it else int_modulus it) - 1.

Global Instance int_elem_of_it : ElemOf Z int_type :=
  λ z it, min_int it ≤ z ≤ max_int it.

Global Instance int_elem_of_it_dec (z : Z) (it : int_type) : Decision (z ∈ it) := _.

Global Typeclasses Opaque int_elem_of_it.

Definition it_layout (it : int_type) :=
  Layout (bytes_per_int it) it.(it_byte_size_log).

Definition i8  := IntType 0 true.
Definition u8  := IntType 0 false.
Definition i16 := IntType 1 true.
Definition u16 := IntType 1 false.
Definition i32 := IntType 2 true.
Definition u32 := IntType 2 false.
Definition i64 := IntType 3 true.
Definition u64 := IntType 3 false.
(* TODO: We would like to enable the following to make it faster to match on
this in a typeclass search, but currently SimplBoth relies on being
able to unfold this. *)
(* Global Typeclasses Opaque i8 u8 i16 u16 i32 u32 i64 u64. *)

(* hardcoding 64bit pointers for now *)
Definition bytes_per_addr_log : nat := 3%nat.
Definition bytes_per_addr : nat := (2 ^ bytes_per_addr_log)%nat.

Definition void_ptr : layout := {| ly_size := bytes_per_addr; ly_align_log := bytes_per_addr_log |}.
Notation "'void*'" := (void_ptr).

Definition size_t  := IntType bytes_per_addr_log false.
Definition ssize_t := IntType bytes_per_addr_log true.
(* Global Typeclasses Opaque size_t ssize_t. *)

Notation intptr_t := ssize_t (only parsing).
Notation ptrdiff_t := ssize_t (only parsing).
Notation uintptr_t := size_t (only parsing).

Definition bool_layout : layout := {| ly_size := 1; ly_align_log := 0 |}.

(*** Lemmas about [int_type] *)

Lemma bytes_per_int_gt_0 it : bytes_per_int it > 0.
Proof.
  rewrite /bytes_per_int. move: it => [log ?] /=.
  rewrite Z2Nat.inj_pow. assert (0 < 2%nat ^ log); last lia.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma bits_per_int_gt_0 it : bits_per_int it > 0.
Proof.
  rewrite /bits_per_int /bits_per_byte.
  suff : (bytes_per_int it > 0) by lia.
  by apply: bytes_per_int_gt_0.
Qed.

Lemma int_modulus_twice_half_modulus (it : int_type) :
  int_modulus it = 2 * int_half_modulus it.
Proof.
  rewrite /int_modulus /int_half_modulus.
  rewrite -[X in X * _]Z.pow_1_r -Z.pow_add_r; try f_equal; try lia.
  rewrite /bits_per_int /bytes_per_int.
  apply Z.le_add_le_sub_l. rewrite Z.add_0_r.
  rewrite Z2Nat.inj_pow.
  assert (0 < 2%nat ^ it_byte_size_log it * bits_per_byte); last lia.
  apply Z.mul_pos_pos; last (rewrite /bits_per_byte; lia).
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma it_in_range_mod n it:
  n ∈ it → it_signed it = false →
  n `mod` int_modulus it = n.
Proof.
  move => [??] ?. rewrite Z.mod_small //.
  destruct it as [? []] => //. unfold min_int, max_int in *. simpl in *.
  lia.
Qed.

Lemma min_int_le_0 (it : int_type) : min_int it ≤ 0.
Proof.
  have ? := bytes_per_int_gt_0 it. rewrite /min_int /int_half_modulus.
  destruct (it_signed it) => //. trans (- 2 ^ 7) => //.
  rewrite -Z.opp_le_mono. apply Z.pow_le_mono_r => //.
  rewrite /bits_per_int /bits_per_byte. lia.
Qed.

Lemma max_int_ge_127 (it : int_type) : 127 ≤ max_int it.
Proof.
  have ? := bytes_per_int_gt_0 it.
  rewrite /max_int /int_modulus /int_half_modulus.
  rewrite /bits_per_int /bits_per_byte.
  have ->: (127 = 2 ^ 7 - 1) by []. apply Z.sub_le_mono => //.
  destruct (it_signed it); apply Z.pow_le_mono_r; lia.
Qed.

Lemma int_modulus_mod_in_range n it:
  it_signed it = false →
  (n `mod` int_modulus it) ∈ it.
Proof.
  move => ?.
  have [|??]:= Z.mod_pos_bound n (int_modulus it). {
    apply: Z.pow_pos_nonneg => //. rewrite /bits_per_int/bits_per_byte/=. lia.
  }
  destruct it as [? []] => //.
  split; unfold min_int, max_int => /=; lia.
Qed.

Lemma elem_of_int_type_0_to_127 (n : Z) (it : int_type):
  0 ≤ n ≤ 127 → n ∈ it.
Proof.
  move => [??]. rewrite /elem_of /int_elem_of_it.
  have ? := min_int_le_0 it.
  have ? := max_int_ge_127 it.
  lia.
Qed.

Lemma bool_to_Z_elem_of_int_type (b : bool) (it : int_type):
  bool_to_Z b ∈ it.
Proof.
  apply elem_of_int_type_0_to_127.
  destruct b => /=; lia.
Qed.
