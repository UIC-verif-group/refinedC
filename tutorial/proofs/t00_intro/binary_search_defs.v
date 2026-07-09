From caesium Require Import base.

Definition must_be_in_range {A} (l : list A) (s e : nat) (x : A) : Prop :=
    ∀ i, l !! i = Some x → ∃ i', l !! i' = Some x ∧ (s ≤ i' < e)%nat.

Lemma must_be_in_range_full A (l : list A) x: must_be_in_range l 0%nat (length l) x.
Proof. move => ? Hs. move: (Hs) => /(lookup_lt_Some _ _ _). naive_solver lia. Qed.

Lemma must_be_in_range_not_in A (l : list A) s e x: must_be_in_range l s e x → (e ≤ s)%nat → x ∉ l.
Proof. unfold must_be_in_range. move => ?? /(list_elem_of_lookup_1 _ _)[? Hin]. naive_solver lia. Qed.

Lemma must_be_in_range_sorted_l {A} R (l : list A) x y s m e:
  StronglySorted R l → l !! m = Some y → ¬R y x → x ≠ y → must_be_in_range l s e x → must_be_in_range l s m x.
Proof.
  move => Hs Hl HR Hneq Hr i Hi. move: (Hr i Hi) => [i' [Hi' [??]]].
  exists i'. split_and! => //. by apply: StronglySorted_lookup_lt.
Qed.

Lemma must_be_in_range_sorted_r {A} R (l : list A) x y s m e m':
  StronglySorted R l → l !! m = Some y → m' = S m → ¬R x y → x ≠ y → must_be_in_range l s e x → must_be_in_range l m' e x.
Proof.
  move => Hs Hl -> HR Hneq Hr i Hi. move: (Hr i Hi) => [i' [Hi' [??]]].
  exists i'. split_and! => //. by apply: StronglySorted_lookup_lt.
Qed.

Global Typeclasses Opaque must_be_in_range.
Opaque must_be_in_range.
