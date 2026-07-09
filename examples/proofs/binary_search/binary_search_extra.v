From caesium Require Import base.

Lemma binary_search_cond_1 {A B} ya y R (l : list (A * B)) i j xa x z `{!Transitive R}:
  R y z → StronglySorted R l.*2 → l !! i = Some (xa, x) → l !! j = Some (ya, y) → (i ≤ j)%nat → R x z.
Proof.
  move => ?????.
  have [||||->|?]:= StronglySorted_lookup_le R l.*2 i j x y => //.
  1, 2: apply list_lookup_fmap_Some; eexists (_, _); naive_solver.
  by etrans.
Qed.

Lemma binary_search_cond_2 {A B} ya y R (l : list (A * B)) i j xa x z `{!Transitive R}:
  ¬ R y z → StronglySorted R l.*2 → l !! i = Some (xa, x) → l !! j = Some (ya, y) → (j ≤ i)%nat → ¬ R x z.
Proof.
  move => Hneg ????. have [||||<-|?]:= StronglySorted_lookup_le R l.*2 j i y x => //.
  1, 2: apply list_lookup_fmap_Some; eexists (_, _); naive_solver.
  contradict Hneg. by etrans.
Qed.
