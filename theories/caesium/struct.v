From stdpp Require Export strings.
From stdpp Require Import gmap list.
From caesium Require Export base layout int_type loc.
Set Default Proof Using "Type".

Definition var_name := string.

Definition field_list := list (option var_name * layout).

Definition field_members (s : field_list) : list (var_name * layout) :=
  (omap (λ '(n, ly), (λ n', (n', ly)) <$> n) s).
Definition field_names (s : field_list) : list var_name := omap fst s.
Definition offset_of_idx (s : field_list) (i : nat) : nat :=
  sum_list (take i (ly_size <$> s.*2)).
Definition index_of (s : field_list) (n : var_name) : option nat :=
  fst <$> list_find (λ x, x.1 = Some n) s.
Definition offset_of (s : field_list) (n : var_name) : option nat :=
  (λ idx, offset_of_idx s idx) <$> index_of s n.
Definition field_idx_of_idx (s : field_list) (i : nat) : nat :=
  length (field_names (take i s)).
Fixpoint field_index_of (s : field_list) (n : var_name) : option nat :=
  match s with
  | [] => None
  | (n', ly)::s' => if bool_decide (n' = Some n) then Some 0%nat else
                    (if n' is Some _ then S else id) <$> field_index_of s' n
  end.
Fixpoint pad_struct {A} (s : field_list) (l : list A) (f : layout → A) : list A :=
  match s with
  | [] => []
  | (n, ly)::s' => (if n is Some _ then default (f ly) (head l) else f ly)::pad_struct s' (if n is Some _ then tail l else l) f
  end.
Fixpoint check_fields_aligned (s : field_list) (pos : nat) : bool :=
  match s with
  | [] => true
  | (_,ly)::s' => bool_decide (pos `mod` ly_align ly = 0) && check_fields_aligned s' (pos + ly.(ly_size))
  end.

Record struct_layout := {
   sl_members : field_list;
   sl_nodup : bool_decide (NoDup (field_names sl_members));
   sl_size : sum_list (ly_size <$> sl_members.*2) < max_int size_t + 1;
   sl_fields_aligned : check_fields_aligned sl_members 0 = true;
}.

Definition layout_of (s : struct_layout) : layout := {|
  ly_size := sum_list (ly_size <$> s.(sl_members).*2);
  ly_align_log := max_list (ly_align_log <$> s.(sl_members).*2)
|}.

Coercion layout_of : struct_layout >-> layout.

Lemma struct_layout_eq sl1 sl2 :
  sl1.(sl_members) = sl2.(sl_members) →
  sl1 = sl2.
Proof. destruct sl1, sl2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma field_members_length s:
  length (field_members s) = length (field_names s).
Proof. apply: omap_length_eq => [?[[?|]?]] ?//. Qed.
Lemma field_members_idx_lookup s i n ly:
  s !! i = Some (Some n, ly) →
  field_members s !! field_idx_of_idx s i = Some (n, ly).
Proof. elim: s i => //= -[[?|] ?] s IH [|i] //= ?; simplify_eq => //; by apply: IH. Qed.
Lemma field_idx_of_idx_bound sl i n ly:
  sl_members sl !! i = Some (Some n, ly) →
  (field_idx_of_idx (sl_members sl) i < length (field_names (sl_members sl)))%nat.
Proof. move => /field_members_idx_lookup => /(lookup_lt_Some _ _ _). by rewrite field_members_length. Qed.

Lemma index_of_cons n n' ly s:
  index_of ((n',ly)::s) n = (if decide (n' = Some n) then Some 0%nat else S <$> index_of s n).
Proof. cbn. case_decide => //. rewrite /index_of -!option_fmap_compose. apply option_fmap_ext. by case. Qed.

Lemma field_index_of_leq s n i:
  field_index_of s n = Some i →
  (i < length (field_names s))%nat.
Proof.
  elim: s i => //= -[??]? IH i /= Hf. case_bool_decide; simplify_eq => //=; first lia.
  move: Hf => /fmap_Some[?[Hf ?]]; subst. case_match => /=; naive_solver lia.
Qed.

Lemma field_index_of_to_index_of n s i:
  field_index_of s n = Some i →
  is_Some (index_of s n).
Proof.
  rewrite /index_of.
  elim: s i => // -[n' ly] s IH i/=. case_decide; case_bool_decide => //=; eauto.
  destruct n' => /fmap_Some[x [? _]]; have [|? /fmap_Some[?[->?]]] := IH x; eauto.
Qed.

Lemma pad_struct_length {A} s (l : list A) f:
  length (pad_struct s l f) = length s.
Proof. elim: s l => //= -[[?|]?] s IH l/=; f_equal; done. Qed.
Lemma pad_struct_lookup_Some {A} s (l : list A) f k x:
  length l = length (field_names s) →
  pad_struct s l f !! k = Some x ↔
    ∃ n ly, s !! k = Some (n, ly) ∧ ((n ≠ None ∧ l !! field_idx_of_idx s k = Some x) ∨ (n = None ∧ x = f ly)).
Proof.
  elim: s k l. { move => ???/=. naive_solver. }
  move => [n ly] s IH k l/= Hl. destruct n => /=.
  - destruct l; simplify_eq/=. destruct k => /=; naive_solver.
  - destruct k => /=; naive_solver.
Qed.
Lemma pad_struct_lookup_field {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  l !! i = Some x →
  pad_struct s l f !! j = Some x.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j/= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst.
  by case_match; destruct l => //=; apply: IH.
Qed.

Lemma pad_struct_insert_field {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  (i < length l)%nat →
  <[j:=x]> (pad_struct s l f) = pad_struct s (<[i:=x]> l) f.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j /= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l; naive_solver lia.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst. destruct l; first by naive_solver lia.
  case_match => /=; f_equal; apply IH; naive_solver lia.
Qed.

Lemma pad_struct_snoc_Some {A} s n ly ls (l : A) f :
  length (field_names s) = length ls →
  pad_struct (s ++ [(Some n, ly)]) (ls ++ [l]) f = pad_struct s ls f ++ [l].
Proof.
  elim: s ls => /=. 1: by destruct ls.
  move => -[n' ly'] s IH ls /=. case_match.
  - destruct ls => //= -[?]. f_equal. by apply IH.
  - move => ?. f_equal. by apply IH.
Qed.

Lemma pad_struct_snoc_None {A} s ly (ls : list A) f :
  pad_struct (s ++ [(None, ly)]) ls f = pad_struct s ls f ++ [f ly].
Proof. elim: s ls => //=. move => -[n' ly'] s IH ls /=. f_equal. by apply IH. Qed.

Lemma offset_of_cons' n n' ly s:
  offset_of ((n', ly)::s) n = (if decide (n' = Some n) then Some 0 else (λ m, ly_size ly + m) <$> (offset_of s n))%nat.
Proof. rewrite /offset_of/= index_of_cons. case_decide => //=. destruct (index_of s n) eqn: Hfind => //=. Qed.

Lemma offset_of_cons n n' ly s:
  n' = Some n ∨ n ∈ field_names s →
  default 0%nat (offset_of ((n', ly)::s) n) = (if decide (n' = Some n) then 0 else ly_size ly + (default 0%nat (offset_of s n)))%nat.
Proof.
  rewrite /offset_of/= index_of_cons. case_decide => //= -[|/list_elem_of_omap[x Hin]]//.
  destruct (index_of s n) eqn: Hfind => //=.
  move: Hfind => /fmap_None/list_find_None /Forall_forall Hfind. set_solver.
Qed.

Lemma offset_of_from_in m s:
  Some m ∈ s.*1 → ∃ n, offset_of s m = Some n.
Proof.
  elim: s. 1: set_solver.
  move => [??]? IH. rewrite offset_of_cons'. csimpl => ?.
  case_decide => //; [ naive_solver |].
  have [|? ->] := IH. 1: by set_solver.
  naive_solver.
Qed.

Lemma offset_of_idx_le_size sl i:
  (offset_of_idx (sl_members sl) i ≤ ly_size sl)%nat.
Proof. apply: sum_list_with_take. Qed.

Lemma offset_of_bound i sl:
  offset_of_idx sl.(sl_members) i ≤ max_int size_t.
Proof.
  have ?:= sl_size sl.
  enough (offset_of_idx (sl_members sl) i ≤ sum_list (ly_size <$> (sl_members sl).*2)) by lia.
  by apply Nat2Z.inj_le, sum_list_with_take.
Qed.

Fixpoint check_fields_aligned_alt (s : field_list) (l : loc) : Prop :=
  match s with
  | [] => True
  | (_,ly)::s' => l `has_layout_loc` ly ∧ check_fields_aligned_alt s' (l +ₗ ly.(ly_size))
  end.

Lemma check_fields_aligned_alt_correct sl l:
  l `has_layout_loc` layout_of sl →
  check_fields_aligned_alt sl.(sl_members) l.
Proof.
  rewrite /layout_of.
  have := sl_fields_aligned sl. rewrite -{2}[l]shift_loc_0_nat. move: O => off.
  elim: (sl_members sl) off => // -[n ly] s IH; csimpl => off /andb_true_iff[/bool_decide_eq_true/Z.mod_divide Hdiv ?]?.
  split.
  - apply aligned_to_offset.
    + apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
    + apply Hdiv. have ->: 0 = O by []. move => /Nat2Z.inj/Nat.pow_nonzero. lia.
  - rewrite shift_loc_assoc_nat. apply IH => //. apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
Qed.

Definition GetMemberLoc (l : loc) (s : struct_layout) (m : var_name) : loc :=
  (l +ₗ Z.of_nat (default 0%nat (offset_of s.(sl_members) m))).
Notation "l 'at{' s '}ₗ' m" := (GetMemberLoc l s m) (at level 10, format "l  'at{' s '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberLoc.
Arguments GetMemberLoc : simpl never.

(** ** Unions *)
Record union_layout := {
   ul_members : list (var_name * layout);
   ul_nodup : bool_decide (NoDup ul_members.*1);
   ul_size : max_list (ly_size <$> ul_members.*2) < max_int size_t + 1;
}.

Definition ul_layout (ul : union_layout) : layout := {|
  ly_size := max_list (ly_size <$> ul.(ul_members).*2);
  ly_align_log := max_list (ly_align_log <$> ul.(ul_members).*2)
|}.
Coercion ul_layout : union_layout >-> layout.

Definition index_of_union (n : var_name) (ul : union_layout) : option nat :=
  fst <$> list_find (λ x, x.1 = n) ul.(ul_members).

Definition layout_of_union_member (n : var_name) (ul : union_layout) : option layout :=
  i ← index_of_union n ul; (snd <$> ul.(ul_members) !! i).

Lemma union_layout_eq ul1 ul2 :
  ul1.(ul_members) = ul2.(ul_members) →
  ul1 = ul2.
Proof. destruct ul1, ul2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma layout_of_union_member_in_ul n ul ly:
  layout_of_union_member n ul = Some ly →
  ly ∈ ul.(ul_members).*2.
Proof.
  rewrite /layout_of_union_member. destruct (index_of_union n ul) => //= Hin.
  apply: list_elem_of_lookup_2. by rewrite list_lookup_fmap.
Qed.

Lemma index_of_union_lookup ul i n ly:
  ul.(ul_members) !! i = Some (n, ly) →
  index_of_union n ul = Some i.
Proof.
  move => H1. apply fmap_Some. exists (i, (n, ly)). split => //.
  apply list_find_Some. split_and! => // j[??]H2? /=?. subst.
  suff : (i = j) by lia. apply: NoDup_lookup.
  { eapply bool_decide_spec. apply (ul_nodup ul). }
  all: rewrite list_lookup_fmap; apply fmap_Some; naive_solver.
Qed.

Definition GetMemberUnionLoc (l : loc) (ul : union_layout) (m : var_name) : loc := (l).
Notation "l 'at_union{' ul '}ₗ' m" := (GetMemberUnionLoc l ul m) (at level 10, format "l  'at_union{' ul '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberUnionLoc.
Arguments GetMemberUnionLoc : simpl never.

(** ** op_type *)
Inductive op_type : Set :=
| BoolOp
| IntOp (i : int_type)
| PtrOp
| StructOp (sl : struct_layout) (ots : list op_type)
| UntypedOp (ly : layout).

Definition ot_layout (ot : op_type) : layout :=
  match ot with
  | BoolOp => bool_layout
  | PtrOp => void*
  | IntOp it => it_layout it
  | StructOp sl ots => sl
  | UntypedOp ly => ly
  end.
