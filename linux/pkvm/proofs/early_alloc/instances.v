From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

Lemma shift_12_eq_mul_4096 n :
  (n ≪ 12) = n * 4096.
Proof. by rewrite Z.shiftl_mul_pow2. Qed.
#[export] Hint Rewrite shift_12_eq_mul_4096 : lithium_rewrite.

Lemma ly_size_PAGES i : ly_size (PAGES i) = (i * Z.to_nat PAGE_SIZE)%nat.
Proof. by rewrite /PAGES /ly_with_align /ly_size. Qed.

Lemma ly_offset_PAGES n m:
  (ly_offset (PAGES n) (ly_size (PAGES m))) = PAGES (n - m).
Proof.
  rewrite ly_size_PAGES /ly_offset /PAGES /ly_with_align /ly_size.
  (* TODO: simpl on factor2 with constants is slow, figure out if
  there is a better solution *)
  cbn delta beta iota. change (factor2 (Z.to_nat 4096) 0) with (12%nat).
  f_equal; first lia. rewrite min_l // /factor2 /factor2' /=. case_match => //=.
  assert (p = Pos.of_nat m * (2 ^ 12))%positive as ->. { simpl. lia. }
  rewrite Pos_factor2_mult Pos_factor2_pow. lia.
Qed.

Global Instance simpl_ly_size_page_le i j:
  SimplBoth ((PAGES i).(ly_size) ≤ (PAGES j).(ly_size))%nat (i ≤ j)%nat.
Proof. rewrite /PAGES /ly_with_align /ly_size /=. split; lia. Qed.

Global Instance simpl_ly_size_page_eq i j:
  SimplBoth ((PAGES i).(ly_size) = (PAGES j).(ly_size)) (i = j).
Proof. rewrite !ly_size_PAGES. split; lia. Qed.

Lemma ly_size_ly_offset ly m:
  (ly_size (ly_offset ly m) = ly_size ly - m)%nat.
Proof. done. Qed.

Lemma ly_size_PAGES_sub n m:
  (ly_size (PAGES n) - ly_size (PAGES m) = ly_size (PAGES (n - m)))%nat.
Proof. rewrite !ly_size_PAGES. lia. Qed.

Global Typeclasses Opaque PAGES.
Global Opaque PAGES.

#[export] Hint Rewrite ly_size_ly_offset : lithium_rewrite.
#[export] Hint Rewrite ly_size_PAGES_sub : lithium_rewrite.
#[export] Hint Rewrite ly_size_PAGES : lithium_rewrite.
#[export] Hint Rewrite ly_offset_PAGES : lithium_rewrite.

#[export] Hint Rewrite ly_size_ly_offset : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite ly_size_PAGES_sub : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite ly_size_PAGES : refinedc_loc_eq_rewrite.
#[export] Hint Rewrite ly_offset_PAGES : refinedc_loc_eq_rewrite.
