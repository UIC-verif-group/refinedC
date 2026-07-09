From iris.base_logic.lib Require Export iprop.
From iris.proofmode Require Export proofmode.
From iris.program_logic Require Import language weakestpre.
From lithium Require Export base pure_definitions.

(** Definitions that are used by the Lithium automation. *)


(** * [LiModality] *)
Structure limodal Σ := {
  li_modal : (iProp Σ → iProp Σ);
  li_modal_wand P Q : (P -∗ Q) ⊢ li_modal P -∗ li_modal Q;
  li_modal_intro P : P ⊢ li_modal P;
  li_modal_bind P Q :  (li_modal P) ∗ (P -∗ li_modal Q) ⊢ li_modal Q;
}.
Global Arguments li_modal {_} _.
Global Typeclasses Opaque li_modal.
Global Opaque li_modal.
Declare Scope li_mod_scope.
Delimit Scope li_mod_scope with LM.
Bind Scope li_mod_scope with limodal.

Notation "‖ M ‖ Q" := (li_modal M%_LM Q) (at level 99, M at level 200, Q at level 200, format "‖ M ‖  Q") : bi_scope.


Global Instance li_modal_proper_ent {Σ} (M : limodal Σ) :
  Proper ((⊢) ==> (⊢)) (li_modal M).
Proof.
  move => ???. apply bi.wand_entails'. etrans; [|by apply li_modal_wand].
  by apply bi.entails_wand'.
Qed.
Global Instance li_modal_proper_ent_flip {Σ} (M : limodal Σ) :
  Proper (flip (⊢) ==> flip (⊢)) (li_modal M).
Proof.
  move => ???. apply bi.wand_entails'. etrans; [|by apply li_modal_wand].
  by apply bi.entails_wand'.
Qed.

Global Instance li_modal_proper {Σ} (M : limodal Σ) :
  Proper ((⊣⊢) ==> (⊣⊢)) (li_modal M).
Proof.
  move => ?? /bi.equiv_entails [Hp1 Hp2].
  by apply (anti_symm (⊢)); [rewrite Hp1|rewrite Hp2].
Qed.

Global Instance from_modal_li_modal {Σ} M (P : iProp Σ) :
  FromModal True modality_id (‖M‖ P) (‖M‖ P) P.
Proof. by rewrite /FromModal /= -li_modal_intro. Qed.

Global Instance elim_modal_li_modal {Σ} (M : limodal Σ) p P Q :
  ElimModal True p false (‖M‖ P) P (‖M‖ Q) (‖M‖ Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= => _.
  apply li_modal_bind.
Qed.
Global Instance frame_li_modal {Σ} (M : limodal Σ) p R P Q :
  Frame p R P Q → Frame p R (‖M‖ P) (‖M‖ Q) | 2.
Proof. rewrite /Frame=><-. iIntros "[? >?]". iModIntro. iFrame. Qed.


Global Instance from_assumption_li_modal {Σ} (M : limodal Σ) p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (‖M‖ Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply li_modal_intro. Qed.
Global Instance from_pure_li_modal {Σ} (M : limodal Σ) a P φ :
  FromPure a P φ → FromPure a (‖M‖ P) φ.
Proof. rewrite /FromPure=> <-. apply li_modal_intro. Qed.
Global Instance into_wand_li_modal {Σ} (M : limodal Σ) p q R P Q :
  IntoWand false false R P Q → IntoWand p q (‖M‖ R) (‖M‖ P) (‖M‖ Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !bi.intuitionistically_if_elim HR.
  apply bi.wand_intro_l. iIntros "[>HP >HQ] !>". by iApply "HQ".
Qed.

(* from iris/proofmode/class_instances_updates.v *)
Global Instance into_wand_li_modal_persistent {Σ} (M : limodal Σ) p q R P Q :
  IntoWand false q R P Q → IntoWand p q (‖M‖ R) P (‖M‖ Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim HR.
  apply bi.wand_intro_l. iIntros "[HP >HQ] !>". by iApply "HQ".
Qed.
Global Instance into_wand_li_modal_args {Σ} (M : limodal Σ) p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (‖M‖ P) (‖M‖ Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply bi.wand_intro_l. rewrite bi.intuitionistically_if_elim.
  iIntros "[>HP HQ] !>". by iApply "HQ".
Qed.
Global Instance from_sep_li_modal {Σ} (M : limodal Σ) P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (‖M‖ P) (‖M‖ Q1) (‖M‖ Q2).
Proof. rewrite /FromSep=><-. by iIntros "[>$ >$]". Qed.
Global Instance from_or_li_modal {Σ} (M : limodal Σ) P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (‖M‖ P) (‖M‖ Q1) (‖M‖ Q2).
Proof. rewrite /FromOr=><-. by iIntros "[>$|>$]". Qed.
Global Instance into_and_li_modal {Σ} (M : limodal Σ) P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false (‖M‖ P) (‖M‖ Q1) (‖M‖ Q2).
Proof. rewrite /IntoAnd/==>->. by iIntros "HP"; iSplit; iMod "HP"; [iDestruct "HP" as "[$ _]"|iDestruct "HP" as "[_ $]"]. Qed.

Global Instance from_exist_li_modal {Σ} (M : limodal Σ) {A} P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (‖M‖ P) (λ a, ‖M‖ Φ a)%I.
Proof. rewrite /FromExist=><-. by iIntros "[%x >$]". Qed.

Global Instance into_forall_li_modal {Σ} (M : limodal Σ) {A} P (Φ : A → iProp Σ) :
  IntoForall P Φ → IntoForall (‖M‖ P) (λ a, ‖M‖ Φ a)%I.
Proof. rewrite /IntoForall=>->. iIntros "HP %"; iMod "HP"; iApply "HP". Qed.

Lemma li_modal_mono {Σ} M (P Q : iProp Σ) :
  (P ⊢ Q) → (‖M‖ P) ⊢ ‖M‖ Q.
Proof. by move => ->. Qed.


Program Definition lm_id {Σ} : limodal Σ := {|
  li_modal := id
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. move => ??? /=. apply bi.wand_elim_r. Qed.
Notation "-" := (lm_id) : li_mod_scope.

Lemma lm_id_eq {Σ} (P : iProp Σ) : (‖-‖ P)%I = P.
Proof. done. Qed.

Program Definition lm_fupd {Σ} `{!BiFUpd (iPropI Σ)} (E : coPset) : limodal Σ := {|
  li_modal := fupd E E
|}.
Next Obligation. move => ?????. iIntros "HP >?". by iDestruct ("HP" with "[$]") as "$". Qed.
Next Obligation. move => *. by iIntros "$". Qed.
Next Obligation. move => *. iIntros "[>HP HQ]". by iApply "HQ". Qed.
Notation "={ E }=" := (lm_fupd E) (at level 20) : li_mod_scope.

Lemma lm_fupd_eq {Σ} `{!BiFUpd (iPropI Σ)} E (P : iProp Σ) : (‖={E}=‖ P)%I = (|={E}=> P)%I.
Proof. done. Qed.

Global Instance elim_modal_fupd_fupd {Σ} `{!BiFUpd (iPropI Σ)} E E2 p (P : iProp Σ ) Q :
  ElimModal True p false (‖={E}=‖ P) P (|={E, E2}=> Q) (|={E, E2}=> Q).
Proof. rewrite lm_fupd_eq. apply _. Qed.
Global Instance elim_modal_fupd_wp hlc Λ Σ `{!irisGS_gen hlc Λ Σ} p s E (e : expr Λ) P Φ :
  ElimModal True p false (‖={E}=‖ P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
Proof. rewrite lm_fupd_eq. apply _. Qed.
Global Instance elim_fupd_li_modal {Σ} `{!BiFUpd (iPropI Σ)} E p (P : iProp Σ ) Q :
  ElimModal True p false (|={E}=> P) P (‖={E}=‖ Q) (‖={E}=‖ Q).
Proof. rewrite lm_fupd_eq. apply _. Qed.


(** * [iProp_to_Prop] *)
#[projections(primitive)]
Record iProp_to_Prop {Σ} (P : iProp Σ) : Type := i2p {
  i2p_P :> iProp Σ;
  i2p_proof : i2p_P ⊢ P;
}.
Arguments i2p {_ _ _} _.
Arguments i2p_P {_ _} _.
Arguments i2p_proof {_ _} _.

(** * Checking if a hyp in the context
  The implementation can be found in interpreter.v *)
Class CheckOwnInContext {Σ} (P : iProp Σ) : Prop := { check_own_in_context : True }.

(** * [find_in_context] *)
Record find_in_context_info {Σ} : Type := {
  fic_A : Type;
  fic_Prop : fic_A → iProp Σ;
}.
(* The nat n is necessary to allow different options, they are tried starting from 0. *)
Definition find_in_context {Σ} (fic : find_in_context_info) (T : fic.(fic_A) → iProp Σ) : iProp Σ :=
  (∃ b, fic.(fic_Prop) b ∗ T b).
Class FindInContext {Σ} (fic : find_in_context_info) (key : Set) : Type :=
  find_in_context_proof T: iProp_to_Prop (Σ:=Σ) (find_in_context fic T)
.
Global Hint Mode FindInContext + + - : typeclass_instances.
Inductive FICSyntactic : Set :=.

(** The instance for searching with [FindDirect] is in [instances.v].  *)
Definition FindDirect {Σ A} (P : A → iProp Σ) := {| fic_A := A; fic_Prop := P; |}.
Global Typeclasses Opaque FindDirect.

(** ** [FindHypEqual]  *)
(** [FindHypEqual] is called with find_in_context key [key], an
hypothesis [Q] and a desired pattern [P], and then the instance
(usually a tactic) should try to generate a new pattern [P'] equal to
[P] that can be later unified with [Q]. *)
Class FindHypEqual {Σ} (key : Type) (Q P P' : iProp Σ) := find_hyp_equal_equal: P = P'.
Global Hint Mode FindHypEqual + + + ! - : typeclass_instances.

(** * [RelatedTo] *)
Class RelatedTo {Σ A} (pat : A → iProp Σ) : Type := {
  rt_fic : find_in_context_info (Σ:=Σ);
}.
Global Hint Mode RelatedTo + + + : typeclass_instances.
Global Arguments rt_fic {_ _ _} _.

(** * [IntroPersistent] *)
(** ** Definition *)
Class IntroPersistent {Σ} (P P' : iProp Σ) := {
  ip_persistent : P ⊢ □ P'
}.
Global Hint Mode IntroPersistent + + - : typeclass_instances.
(** ** Instances *)
Global Instance intro_persistent_intuit Σ (P : iProp Σ) : IntroPersistent (□ P) P.
Proof. constructor. iIntros "$". Qed.

(** * Simplification *)
(* n:
   None: no simplification
   Some 0: simplification which is always safe
   Some n: lower n: should be done before higher n (when compared with simplifyGoal)   *)
Definition simplify_hyp {Σ} (P : iProp Σ) (M : limodal Σ) (T : iProp Σ) : iProp Σ :=
  P -∗ ‖M‖ T.
Class SimplifyHyp {Σ} (P : iProp Σ) (M : limodal Σ) (n : option N) : Type :=
  simplify_hyp_proof T : iProp_to_Prop (simplify_hyp P M T).

Definition simplify_goal {Σ} (M : limodal Σ) (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
  (‖M‖ P ∗ T).
Class SimplifyGoal {Σ} (M : limodal Σ) (P : iProp Σ) (n : option N) : Type :=
  simplify_goal_proof T : iProp_to_Prop (simplify_goal M P T).

Global Hint Mode SimplifyHyp + + + - : typeclass_instances.
Global Hint Mode SimplifyGoal + + ! - : typeclass_instances.

(** * Subsumption *)
Definition subsume {Σ A} (P1 : iProp Σ) (M : limodal Σ) (P2 T : A → iProp Σ) : iProp Σ :=
  P1 -∗ ‖M‖ (∃ x, P2 x ∗ T x)%I.
Class Subsume {Σ A} (P1 : iProp Σ) (M : limodal Σ) (P2 : A → iProp Σ) : Type :=
  subsume_proof T : iProp_to_Prop (subsume P1 M P2 T).
Global Hint Mode Subsume + + + + ! : typeclass_instances.

(** * case distinction *)
Definition case_if {Σ} (P : Prop) (T1 T2 : iProp Σ) : iProp Σ :=
  (⌜P⌝ -∗ T1) ∧ (⌜¬ P⌝ -∗ T2).

Definition case_destruct {Σ} {A} (a : A) (T : A → bool → iProp Σ) : iProp Σ :=
  ∃ b, T a b.

(** * [LiEntails] *)
Import environments.
Class LiEntails {Σ : gFunctors} (Δ : envs (iProp Σ)) (M : limodal Σ) (Q : iProp Σ) :=
  li_entails : envs_entails Δ (‖M‖ Q).
Global Typeclasses Opaque LiEntails.

Create HintDb li_entails discriminated.
Global Hint Constants Opaque : li_entails.
Global Hint Variables Opaque : li_entails.
Global Hint Projections Opaque : li_entails.

Definition LiEntailsShelved {Σ : gFunctors} (Δ : envs (iProp Σ)) (M : limodal Σ) (Q : iProp Σ) :=
  envs_entails Δ (‖M‖ Q).
Ltac unshelve_li_entails :=
  lazymatch goal with
  | |- LiEntailsShelved ?Δ ?M ?Q => change (envs_entails Δ (‖M‖ Q))
  | _ => shelve
  end.

Class LiEntailsShelve {Σ : gFunctors} (Δ : envs (iProp Σ)) (M : limodal Σ) (Q : iProp Σ) :=
  li_entails_shelve : LiEntails Δ M Q.
Global Typeclasses Opaque LiEntailsShelve.
Global Hint Extern 1 (LiEntailsShelve ?Σ ?Δ ?M ?Q) => (change (LiEntailsShelved Σ Δ M Q); shelve) : li_entails.

Lemma lemma_to_li_entails {Σ} (P Q : iProp Σ) :
  (P ⊢ Q) →
  ∀ Δ M,
  LiEntailsShelve Δ M P →
  LiEntails Δ M Q.
Proof. by rewrite /LiEntailsShelve/LiEntails => + ?? => ->. Qed.

(* The following can be used to test that the opaqueness is working.
There should not be a slowdown on coq-speed when uncommenting the
following instances. *)
(*
Definition TEST {Σ} (n : Z) : iProp Σ := True.
Lemma TEST_lem {Σ} n:
  True ⊢ @TEST Σ n.
Proof. done. Qed.

Definition TEST_lem1 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 1).
Definition TEST_lem2 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 2).
Definition TEST_lem3 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 3).
Definition TEST_lem4 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 4).
Definition TEST_lem5 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 5).
Definition TEST_lem6 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 6).
Definition TEST_lem7 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 7).
Definition TEST_lem8 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 8).
Definition TEST_lem9 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 9).
Definition TEST_lem10 Σ := lemma_to_li_entails _ _ (@TEST_lem Σ 10).

Global Hint Resolve TEST_lem1 TEST_lem2 TEST_lem3 TEST_lem4 TEST_lem5
  TEST_lem6 TEST_lem7 TEST_lem8 TEST_lem9 TEST_lem10 : li_entails.
*)

(* TODO: Try if there is a performance difference to the variant
with a TC goal typeclass, which has less parameters. *)
(* (** * TC goal *) *)
(* Definition TC_GOAL (P : Prop) := P. *)
(* Global Typeclasses Opaque TC_GOAL. *)

(* Ltac unshelve_tc_goal := *)
(*   lazymatch goal with *)
(*   | |- TC_GOAL ?P => change P *)
(*   | _ => shelve *)
(*   end. *)

(* Class TCGoal (P : Prop) := tc_goal : P. *)
(* Global Typeclasses Opaque TCGoal. *)
(* Hint Extern 1 (TCGoal ?P) => (change (TC_GOAL P); shelve) : typeclass_instances. *)

(** * [li_tactic] *)
Definition li_tactic {Σ A} (t : (A → iProp Σ) → iProp Σ) (T : A → iProp Σ) : iProp Σ :=
  t T.
Global Typeclasses Opaque li_tactic.
Arguments li_tactic : simpl never.

(** ** [li_vm_compute] *)
Definition li_vm_compute {Σ A B} (f : A → option B) (x : A) (T : B → iProp Σ) : iProp Σ :=
  ∃ y, ⌜f x = Some y⌝ ∗ T y.
Arguments li_vm_compute : simpl never.
Global Typeclasses Opaque li_vm_compute.

Lemma li_vm_compute_tac {Σ A B} Δ M (f : A → option B) x a (T : B → iProp Σ) :
  f a = Some x →
  LiEntailsShelved Δ M (T x) →
  LiEntails Δ M (li_tactic (li_vm_compute f a) T).
Proof.
  rewrite /LiEntails/LiEntailsShelved/li_tactic/li_vm_compute.
  move => ->. rewrite envs_entails_unseal => ->. apply li_modal_mono. by iIntros "$".
Qed.
Global Hint Extern 10 (LiEntails _ _ (li_tactic (li_vm_compute _ _) _)) =>
  eapply li_vm_compute_tac; [evar_safe_vm_compute|shelve] : li_entails.

(** * [accu] *)
Definition accu {Σ} (f : iProp Σ → iProp Σ) : iProp Σ :=
  ∃ P, P ∗ □ f P.
Arguments accu : simpl never.
Global Typeclasses Opaque accu.

(** * trace *)
Definition li_trace {Σ A} (t : A) (T : iProp Σ) : iProp Σ := T.

(** * [sep_list] *)
(** sep_list_id is a marker to link a sep_list in the goal to a
sep_list in the context. It also transfers the length between the two.
Values of type sep_list_id should always be opaque during the proof. *)
Record sep_list_id : Set := { sep_list_len : nat }.

(* TODO: use Z instead of nat for f such that one avoids adding a
Z.to_nat Z.of_nat roundtrip? It is a bit annoying since one needs to
introduce Z.of_nat for the list insert. *)
Definition sep_list {Σ} (id : sep_list_id) A (ig : list nat) (l : list A) (f : nat → A → iProp Σ) : iProp Σ :=
  ⌜length l = sep_list_len id⌝ ∗ ([∗ list] i↦x∈l, if bool_decide (i ∈ ig) then True%I else f i x).
Global Typeclasses Opaque sep_list.

Definition FindSepList {Σ} (id : sep_list_id) := {| fic_A := iProp Σ; fic_Prop P := P; |}.
Global Typeclasses Opaque FindSepList.
