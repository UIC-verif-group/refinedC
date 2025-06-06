From refinedc.typing Require Import typing.
From refinedc.examples.wrapping_add Require Export wrapping_def.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ}.

  Lemma macro_wrapping_add it1 it2 e1 e2 T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, v1 ◁ᵥ ty1 -∗ v2 ◁ᵥ ty2 -∗
      ∃ n1 n2, v1 ◁ᵥ n1 @ int it1 ∗ v2 ◁ᵥ n2 @ int it2 ∗ (
               (⌜n1 ∈ it1⌝ -∗ ⌜n2 ∈ it2⌝ -∗ ⌜it1 = it2⌝ ∗ ⌜it_signed it1 = false⌝ ∗ (
               ∀ v, T v (((n1 + n2) `mod` int_modulus it1) @ int it1))))))
    ⊢ typed_macro_expr (WrappingAdd it1 it2) [e1 ; e2] T.
  Proof.
    iIntros "HT". rewrite /typed_macro_expr/WrappingAdd. iApply type_bin_op.
    iIntros (Φ) "HΦ". iApply "HT". iIntros (v1 ty1) "Hty1 HT". iApply ("HΦ" with "Hty1"). clear.
    iIntros (Φ) "HΦ". iApply "HT". iIntros (v2 ty2) "Hty2 HT". iApply ("HΦ" with "Hty2"). clear.
    iIntros "Hty1 Hty2". iDestruct ("HT" with "Hty1 Hty2") as (n1 n2) "HT".
    unfold int; simpl_type. iDestruct "HT" as (Hv1 Hv2) "HT".
    iIntros (Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as (??) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    have /(val_of_Z_is_Some None)[v Hv] : ((n1 + n2) `mod` int_modulus it1) ∈ it1 by apply int_modulus_mod_in_range.
    subst it2.
    iApply (wp_binop_det_pure v). {
      move => ??. split.
      + inversion 1; simplify_eq/=.
        by destruct it1 as [? []]; simplify_eq/=.
      + move => ->. apply: ArithOpII => //.
          by destruct it1 as [? []]; simplify_eq/=.
    }
    iIntros "!>". iApply "HΦ"; last done. simpl_type. iPureIntro.
    by eapply val_to_of_Z.
  Qed.

  Definition macro_wrapping_add_inst := [instance macro_wrapping_add].
  Global Existing Instance macro_wrapping_add_inst.
End type.
