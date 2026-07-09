From lithium Require Import definitions simpl_classes proof_state.

Inductive LVAR_HINT {A} (name : string) (x : A) : Prop := { lvar_locked : locked True }.
Definition lvar (name : string) (A : Type) : Type := A.

Definition set_lvar {Σ A} (name : string) (x : A) : iProp Σ := True.
Global Typeclasses Opaque set_lvar.

Notation "'lvar' id : v" := (LVAR_HINT id v) (at level 200, only printing).

Lemma simplify_goal_set_lvar Σ M A (x : A) name (T : iProp Σ) :
  (⌜LVAR_HINT name x⌝ -∗ ‖M‖ T) ⊢ simplify_goal M (set_lvar name x) T.
Proof.
  iIntros "HT". rewrite /set_lvar. iMod ("HT" with "[%]") as "$"; [|by iModIntro].
  constructor. by unlock.
Qed.
Definition simplify_goal_set_lvar_inst := [instance simplify_goal_set_lvar with 0%N].
Global Existing Instance simplify_goal_set_lvar_inst.

Lemma simpl_exist_lvar Σ A (x : A) name :
  LVAR_HINT name x →
  @SimplExist Σ (lvar name A) (λ P, P x)%I.
Proof. move => ?. rewrite /SimplExist. iIntros (?) "?". iExists _. iFrame. Qed.
Global Hint Extern 2 (SimplExist (lvar ?i _) _) =>
         (notypeclasses refine (simpl_exist_lvar _ _ _ _ _); eassumption) : typeclass_instances.
