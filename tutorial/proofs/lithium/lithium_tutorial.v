From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Import hooks.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import typing.
From refinedc.tutorial.lithium Require Import generated_code.
From refinedc.tutorial.lithium Require Import generated_spec.
Set Default Proof Using "Type".

(* Disable conversion to Lithium syntax in this file. *)
Local Ltac liToSyntax_hook ::= fail.

Axiom AddE : expr → expr → expr.
Notation "e1 + e2" := (AddE e1 e2) : expr_scope.
Axiom ValInt : Z → val.

Section lithium.
  Context `{!typeG Σ}.

  Axiom wp_add : ∀ n1 n2 Φ,
      Φ (ValInt $ n1 + n2)
      ⊢ WP ValInt n1 + ValInt n2 {{ Φ }}.

  Lemma ex1 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
     WP ValInt n + ValInt 1 {{ v,
       ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    (* Run Lithium. *)
    liEnsureInvariant.
    repeat liStep.
    liShow. iModIntro.
    (* Lithium stops at the WP. Let's apply our lemma. *)
    iApply wp_add.
    (* Run Lithium. *)
    liEnsureInvariant.
    repeat liStep.
    (* Lithium finished and left some sideconditions. *)
    Unshelve. all: unshelve_sidecond.
    (* Discharge the sidecondition. *)
    lia.
    (* Done! *)
  Qed.

  Lemma ex1' :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
     WP ValInt n + ValInt 1 {{ v,
       ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof. liEnsureInvariant. liShow.
    (* Introduce the universal quantifier. *)
    liStep.
    (* Introduce the pure assumption
       (in two steps for technical reasons).*)
    liStep. liStep.
    (* Lithium does not know how to handle this WP. *)
    Fail liStep.
    (* Let's apply our lemma. *)
    iModIntro.
    iApply wp_add.
    (* Turn the existential quantifer into a Lithium existential quantifer . *)
    liEnsureInvariant. liShow. liStep.
    (* Solve the sidecondition to instantiate the evar. *)
    liStep. liStep.
    (* Shelve the sidecondition. *)
    liStep.
    (* Solve True. *)
    liStep.
    (* Unshelve sideconditions. *)
    Unshelve. all: unshelve_sidecond.
    (* Discharge the sidecondition. *)
    lia.
    (* Done! *)
  Qed.

  (*
     Atom       A ::= v ◁ᵥ ty | ...
     Basic goal F ::= A1 <: A2 { G } | ...
     Goal       G ::= True | H ∗ G | H -∗ G
                       | G1 ∧ G2 | ∀ x, G(x)
                       | ∃ x, G(x) | F
     Left goal  H ::= ⌜φ⌝ | A | H ∗ H | ∃ x, H(x)
  *)

  (* Key takeaway: Lithium automates proofs by looking at the goal and
  applying the "obvious" rule. The technical term for this is
  goal-directed proof search and Lithium can be seen as a logic
  programming language for separation logic. For more information like
  the subset of separation logic supported by Lithium, see Section 5
  of the RefinedC paper. *)

  (* Let's automate the basic goal WP. *)
  Ltac liEExpr :=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add _ _ _) _)
        end
    end.

  (* Now we can define our own step tactic liEStep that combines
  liEExpr and liStep (and some boilerplate). *)
  Ltac liEStep :=
    liEnsureInvariant;
    first [
        liEExpr
      | liStep
    ]; liSimpl.

  Lemma ex2 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    (* Now the proof is automatic! *)
    repeat liEStep; liShow.
    Unshelve. all: unshelve_sidecond.
    lia.
  Qed.

  (* Let's add a sidecondition to wp_add. *)
  Axiom wp_add2 : ∀ n1 n2 Φ,
      ⌜n1 + n2 < 2 ^ 64⌝ ∗ Φ (ValInt $ n1 + n2)
      ⊢ WP ValInt n1 + ValInt n2 {{ Φ }}.

  (* We need to update liEExpr. *)
  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add2 _ _ _) _)
        end
    end.

  Lemma ex3 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
    Unshelve. all: unshelve_sidecond.
    all: try lia.
  Abort.


  (* Additional content. *)


  (* What about multiple additions ? *)
  Lemma ex4 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
    (* Here wp_add does not apply since the first argument of the
    addition is not a value. *)
  Abort.

  (* Let's define a more general version of wp_add that works for
  expressions, not just for values. *)
  Axiom wp_add3 : ∀ e1 e2 Φ,
    WP e1 {{ v1,
      WP e2 {{ v2, ∃ n1 n2,
        ⌜v1 = ValInt n1⌝ ∗ ⌜v2 = ValInt n2⌝ ∗ Φ (ValInt $ n1 + n2) }} }}
    ⊢ WP e1 + e2 {{ Φ }}.

  (* We need to update liEExpr. *)
  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add3 _ _ _) _)
        end
    end.

  (* Let's try... *)
  Lemma ex4 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
    (* Almost! The new wp_add was applied successfully, but now we get
    a WP for ValInt that the automation does not know how to
    handle. *)
  Abort.

  (* Let's add a wp rule for values. *)
  Axiom wp_val : ∀ v Φ,
      Φ v
      ⊢ WP Val v {{ Φ }}.

  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add3 _ _ _) _)
        | Val _ => notypeclasses refine (tac_li_apply (wp_val _ _) _)
        end
    end.

  Lemma ex5 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
    (* Success! *)
    Unshelve. all: unshelve_sidecond.
    lia.
    (* Also try changing the expression to include more or less
    additions. *)
  Qed.

  Axiom wp_add4 : ∀ e1 e2 Φ,
    WP e1 {{ v1,
      WP e2 {{ v2, ∃ n1 n2,
        ⌜v1 = ValInt n1⌝ ∗ ⌜v2 = ValInt n2⌝ ∗
        ⌜n1 + n2 < 2 ^ 64⌝ ∗
        Φ (ValInt $ n1 + n2) }} }}
    ⊢ WP e1 + e2 {{ Φ }}.

  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_fast_apply (wp_add4 _ _ _) _)
        | Val _ => notypeclasses refine (tac_fast_apply (wp_val _ _) _)
        end
    end.

  Lemma ex6 :
    ⊢ ∀ n, ⌜n > 0⌝ -∗
      WP ValInt n + ValInt 1 + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
    Unshelve. all: unshelve_sidecond.
    all: try lia.
  Abort.

  Axiom Load : expr → expr.
  Axiom ValLoc : loc → val.

  Axiom wp_load : ∀ e Φ,
    WP e {{ v, ∃ l,
     ⌜v = ValLoc l⌝ ∗ l ↦ ValInt 5 ∗ (l ↦ ValInt 5 -∗ Φ (ValInt 5)) }}
    ⊢ WP Load e {{ Φ }}.

  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add3 _ _ _) _)
        | Load _ => notypeclasses refine (tac_li_apply (wp_load _ _) _)
        | Val _ => notypeclasses refine (tac_li_apply (wp_val _ _) _)
        end
    end.

  Lemma ex7 :
    ⊢ ∀ l, l ↦ ValInt 5 -∗
      WP Load (ValLoc l) + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ l ↦ ValInt 5 ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
  Qed.

  Axiom wp_load2 : ∀ e Φ,
    WP e {{ v, ∃ l v',
     ⌜v = ValLoc l⌝ ∗ l ↦ v' ∗ (l ↦ v' -∗ Φ v') }}
    ⊢ WP Load e {{ Φ }}.

  Ltac liEExpr ::=
    match goal with
    | |- envs_entails _ (‖_‖ wp _ _ ?e _) =>
        match e with
        | AddE _ _ => notypeclasses refine (tac_li_apply (wp_add3 _ _ _) _)
        | Load _ => notypeclasses refine (tac_li_apply (wp_load2 _ _) _)
        | Val _ => notypeclasses refine (tac_li_apply (wp_val _ _) _)
        end
    end.

  Lemma ex8 :
    ⊢ ∀ l, l ↦ ValInt 5 -∗
      WP Load (ValLoc l) + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ l ↦ ValInt 5 ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
  Abort.

  Global Instance mapsto_related_to A l v : RelatedTo (λ x : A, l ↦ (v x))%I := {|
    rt_fic := FindDirect (λ v', l ↦ v')%I;
  |}.

  Lemma ex8 :
    ⊢ ∀ l, l ↦ ValInt 5 -∗
      WP Load (ValLoc l) + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ l ↦ ValInt 5 ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
  Abort.

  Lemma subsume_mapsto A M l v1 v2 G:
    (∃ x, ⌜v1 = v2 x⌝ ∗ G x)
    ⊢ subsume (l ↦ v1) M (λ x : A, l ↦ (v2 x)) G.
  Proof. iIntros "[% [-> ?]] ? !>". iExists _. iFrame. Qed.
  Definition subsume_mapsto_inst := [instance subsume_mapsto].
  Global Existing Instance subsume_mapsto_inst.

  Lemma ex8 :
    ⊢ ∀ l, l ↦ ValInt 5 -∗
      WP Load (ValLoc l) + ValInt 1 {{ v,
        ∃ n', ⌜v = ValInt n'⌝ ∗ ⌜n' > 0⌝ ∗ l ↦ ValInt 5 ∗ True }}.
  Proof.
    iStartProof.
    repeat liEStep; liShow.
  Qed.

  (*
    Predictable:
    - Easy to understand what the automation is doing
    - Allows integration with manual proof steps

    Efficient: pass over the goal without backtracking

    Extensible:
    - supports new rules for primitive constructs
    - supports different ownership assertions
 *)
End lithium.

(*** Alternative tutorial *)

(** This file contains a tutorial for Lithium, the underlying proof
automation of RefinedC. See also Section 5 of the RefinedC paper. *)

Section lithium.
  Context `{!typeG Σ}.

  (*** Proof search in Lithium *)

  (** Lithium is a logic programming language for separation logic for
      goals G given by the following grammar:

        Atom       A ::= l ◁ₗ ty | v ◁ᵥ ty | ...
        Basic goal F ::= subsume A1 A2 G | ...
        Goal       G ::= True | H ∗ G | H -∗ G | G1 ∧ G2 | ∀ x, G(x) | ∃ x, G(x) | F
        Left goal  H ::= ⌜φ⌝ | A | H ∗ H | ∃ x, H(x)

     We explain the different constructs of this grammar on the following example:
  *)
  Lemma lithium_example P Q v:
    P -∗
    (Q ∗ ∃ n, v ◁ᵥ n @ int i32 ∗ ⌜n > 0⌝) -∗
    (P ∗ Q) ∗ ∃ n, v ◁ᵥ n @ int i32 ∗ ⌜n ≠ 0⌝ ∗ (
      ∀ n', ⌜n' = n⌝ -∗ v ◁ᵥ n' @ int i32 -∗
      (v ◁ᵥ n' @ int i32 ∗ True) ∧ (v ◁ᵥ n @ int i32 ∗ True)
    ).
  Proof.
    iStartProof.

    (** First, it is easy to check that this separation logic
    assertion fits into the grammar G. So let's run the Lithium
    interpreter on it! The interpreter is implemented as a Coq tactic
    liRStep which does a single step. So we can run it to the end with
    [repeat liRStep]. For performance reasons, the interpreter
    introduces some let-bindings, which we unfold via [liShow] to make
    the goal readable. *)
    (** (Note: Technically, the actually Lithium interpreter is given
    by liStep. liRStep is a extended version of Lithium for the basic
    goals RefinedC. We ignore this distinction in this tutorial and
    just use liRStep. ) *)
    repeat liRStep; liShow.
    (** Lithium was able to solve this goal automatically (ignoring
    the shelved subgoal that we will come back to later)! *)
  Abort.

  (** Let's revert this and go over how Lithium solves this goal. *)
  Lemma lithium_example P Q v:
    P -∗
    (Q ∗ ∃ n, v ◁ᵥ n @ int i32 ∗ ⌜n > 0⌝) -∗
    (P ∗ Q) ∗ ∃ n, v ◁ᵥ n @ int i32 ∗ ⌜n ≠ 0⌝ ∗ (
      ∀ n', ⌜n' = n⌝ -∗ v ◁ᵥ n' @ int i32 -∗
      (v ◁ᵥ n' @ int i32 ∗ True) ∧ (v ◁ᵥ n @ int i32 ∗ True)
    ).
  Proof.
    iStartProof.

    (** At the high-level, the implementation of the Lithium
    interpreter is quite simple: It simply looks at the top-level
    connective of the goal and applies the corresponding introduction
    rule.

    In particular, for the first step, the top-level connective is a
    wand -∗ where the left hand side is an atom. Lithium treats all
    assertions on the left hand side of wand and start that are not
    syntactically left goals as atoms. Atoms are treated as opaque by
    Lithium, but can be manipulated via rules for basic goals as we
    will see later.

    To introduce this wand, Lithium introduces P into the context. (case 7.d.
    in Section 5 of the RefinedC paper) *)
    liRStep; liShow.

    (** Now the goal is a wand where the left hand side is a
    separating conjunction. Here, Lithium splits the separating
    conjunction. (7.a. in the RefinedC paper) *)
    liRStep; liShow.

    (** Now Lithium introduces Q like P above. *)
    liRStep; liShow.

    (** Now we have an existential quantifier on the left hand side of
    a wand. Lithium introduces this quantifier as well, adding n
    to the context. (7.b. in the RefinedC paper) *)
    liRStep; liShow.

    (** Splitting separating conjunction again. *)
    liRStep; liShow.

    (** Introducing atom again. *)
    liRStep; liShow.

    (** Now the goal is a wand with a pure proposition on the
    left-hand side. The interpreter introduces this proposition into
    the Coq context (7.c. in the RefinedC paper). This introduction
    happens in two steps for technical reasons. *)
    liRStep; liShow.
    liRStep; liShow.


    (** We are done with the wand. Now the top-level connective of the
    goal is a separating conjunction.

    Like for the wand, we look at the left hand side of the separating
    conjunction. Here it is another separating conjunction. The
    interpreter reassociates it such that it can analyze a smaller
    formula. (6.a. in the RefinedC paper) *)
    liRStep; liShow.

    (** Now the left hand side of the separating conjunction is an
    atom and the same atom appears in the context. In this case,
    Lithium cancels the two atoms. *)
    liRStep; liShow.

    (** Same for Q *)
    liRStep; liShow.

    (** Now the top-level connective is an existential quantifier. The
    interpreter turns it into a special Lithium existential quantifer
    that can then by instnatiated by the rest of the proof search.
    (This differs from the description in the RefinedC paper.) *)
    liRStep; liShow.

    (** Now the goal is a separating conjunction where the left hand
    side is an atom that does not directly appear in the context. In
    this case, Lithium searches for a "related" assertion in the
    context. In this case, it finds the type assignment [v ◁ᵥ ...] in
    the context since type assignments for the same value (and
    location) are related. After finding such a type assignment, one
    needs to prove a subsumption between the two atoms. This is
    encoded via the subsumption judgment [subsume A1 A2 G] which is
    defined as [A1 -∗ (A2 ∗ G)]. (6.d in the RefinedC paper) *)
    liRStep; liShow.

    (** The subsumption judgment is a basic goal F. These goals are
    solved by applying a user-defined rule that transforms the basic
    goal into a new Lithium goal (5. in the RefinedC paper).

    Here, Lithium finds the following rule:

                ⌜x = y⌝ ∗ G
    ------------------------------------∗
    subsume (v ◁ᵥ x @ ty) (v ◁ᵥ y @ ty) G
     *)
    (** We make make happens clearer by introducing a let-binding for the continuation: *)
    set G := (X in (subsume _ _ X)).
    liRStep; liShow.
    rewrite {}/G.

    (** Now the top-level connective of the goal is a separating
    conjunction where the left hand side is a pure sidecondition that
    contains an evar. Lithium solves this sidecondition via
    unification and instantiates the evar (see t02_evars.c for
    details). Similar to the wand, this happens in two steps. *)
    liRStep; liShow. liRStep; liShow.

    (** Now we have a pure sidecondition without evars. Such
    sideconditions are shelved to be solved later. (6.c. in the
    RefinedC paper) *)
    liRStep; liShow.

    (** Next, we have an universal quantifier at the top-level.
    Lithium introduces it. (3. in the RefinedC paper) *)
    liRStep; liShow.

    (** Now the top-level connective is again a magic wand with a pure
    sidecondition on the left-hand side. Lithium introduces it and
    directly substitutes the equality. *)
    liRStep; liShow.
    liRStep; liShow.

    (** Introducing an atom into the context. *)
    liRStep; liShow.

    (** Now the top-level connective is a non-separating conjunction
    ∧. Lithium introduces it by splitting the proof into two subgoals.
    Note that ∧ allows to keep the same (Iris) context in both subgoals. *)
    liRStep; liShow.

    (** The second goal is the same as the first so we just look at the first. *)
    2: repeat liRStep; liShow.

    (** Cancel atoms. *)
    liRStep; liShow.

    (** Now the top-level connective is True. This is solved trivially
    by Lithium and we are done with the separation logic part of this proof! *)
    liRStep; liShow.

    (** As a last step, we need to solve the pure sideconditions that were
    shelved during the separation logic proof. We first unshelve them all follows: *)
    Unshelve. all: unshelve_sidecond.

    (** Now we can solve this sidecondition with lia. *)
    lia.
  Qed.

  (*** Adding rules for basic goals *)

  (** The previous discussion showed Lithium automates separation
  logic reasoning. We have also seen that this proof search relies on
  user-defined rules for handling basic goals. Let's have a closer
  look how such rules can be defined. In particular, we will define a
  subsumption rule for a custom integer type [myint]. *)
  Axiom myint : Z → type.

  (** Let's try to solve the following goal using Lithium: *)
  Lemma myint_example l:
    l ◁ₗ myint 5 -∗ ∃ n', l ◁ₗ myint n' ∗ ⌜0 < n'⌝ ∗ True.
  Proof.
    iStartProof.
    repeat liRStep; liShow.
    (** The Lithium automation gets stuck when trying to prove a
    subsumption between two type assignments of myint since there is
    no applicable rule. So let's add a rule to solve this problem. *)
  Abort.

  (** First, we prove a lemma [subsume_myint] of the form [G -∗ F]
  where [F] is the basic goal we want to prove (here a subsumption
  between myint) and [G] is the Lithium goal that the subsumption
  should be transformed into (here we reduce proving the subsumption
  to proving equality between the numbers). *)
  Lemma subsume_myint A M l n n' G:
    (∃ x, ⌜n = n' x⌝ ∗ G x)
    ⊢ subsume (l ◁ₗ myint n) M (λ x : A, l ◁ₗ myint (n' x)) G.
  Proof. iIntros "[% [-> HG]]". iIntros "Hl !>". iExists _. by iFrame. Qed.

  (** The [subsume_myint] needs to be registered with the Lithium
  automation, which we do as follows: *)
  Definition subsume_myint_inst := [instance subsume_myint].
  Global Existing Instance subsume_myint_inst.

  (** Now we are ready to try again: *)
  Lemma myint_example l:
    l ◁ₗ myint 5 -∗ ∃ n', l ◁ₗ myint n' ∗ ⌜0 < n'⌝ ∗ True.
  Proof.
    iStartProof.
    repeat liRStep; liShow.
    (** Success! Lithium now automatically solves this goal. *)
  Qed.

  (*** More complicated subsumption rules *)

  (** We have seen a custom rule for a basic goal, but its premise was
  quite simple and did not really exploit the fact that one can use
  the full grammar of goals for the premise of rules for basic goals.
  Thus, let's look at a more interesting subsumption rule. *)

  (** For this subsumption rule, we assume an array type [myarray]
  that is parametrized by a list of types, representing the types of
  the array members. *)
  Axiom myarray : list type → type.
  (** We also assume that we can extract an member of the array and
  replace it with another type. (This is similar to [big_sepL_insert_acc]). *)
  Axiom myarray_access : ∀ tys (i : nat) ty l,
      tys !! i = Some ty →
      l ◁ₗ myarray tys -∗
      (l +ₗ i) ◁ₗ ty ∗ (∀ ty', (l +ₗ i) ◁ₗ ty' -∗ l ◁ₗ myarray (<[i := ty']>tys)).


  (** Now we can look at the goal we want to prove: *)
  Lemma my_array_example l i l' tys n:
    (** Assuming we have ownership of an array with types tys at
    location l where the ownership of element i has been taken out
    (the type [place l'] asserts that it is stored at location l, but
    it does not contain any ownership), *)
    l ◁ₗ myarray (<[i := place l']> tys) -∗
    (** Also assuming that we know that we l' has type [n @ int i32], *)
    l' ◁ₗ n @ int i32 -∗
    (** And assuming that the type at index i in tys is indeed [n @ int i32] *)
    ⌜tys !! i = Some (n @ int i32)⌝ -∗
    (** we can recombine the ownership of l and l' to conclude that l
    has type [myarray tys]. *)
    l ◁ₗ myarray tys ∗ True.
  Proof.
    iStartProof.
    repeat liRStep; liShow.
    (** However, Lithium does not know how to recombine this ownership
    and gets stuck on the subsumption rule between the two myarray. So
    we need to help Lithium by defining a suitable subsumption rule. *)
  Abort.

  (** To prove this subsumption, we reduce it to the following Lithium goal: *)
  Lemma subsume_myarray A M l ty (i : nat) tys G:
    (
      (** First, one has to prove that i actually is in the range of the list *)
      ⌜i < length tys⌝%nat ∗ (
        (** Then, one can assume that the location at the offset i has type ty *)
        (l +ₗ i) ◁ₗ ty -∗
        (** Then, one gets a type ty' ... *)
        ∀ ty',
        (** ... which is the type at index i of tys *)
        ⌜tys !! i = Some ty'⌝ -∗
        (** Finally, one has to prove that (l +ₗ i) has type ty' *)
        ‖M‖ (l +ₗ i) ◁ₗ ty' ∗
        (** and the continuation G. *)
        ∃ x, G x)
    )
    ⊢
    subsume (l ◁ₗ myarray (<[i:=ty]> tys)) M (λ x : A, l ◁ₗ myarray tys) G.
  Proof.
    (** This lemma is easy to prove using myarray_access. *)
    iIntros "[%Hlt HG] Harray".
    iDestruct (myarray_access with "Harray") as "[Hl Harray]". { by apply: list_lookup_insert_eq. }
    move: Hlt => /lookup_lt_is_Some [ty' ?].
    iMod ("HG" with "Hl [//]") as "[Hl [% ?]]". iModIntro. iFrame.
    iDestruct ("Harray" with "Hl") as "Harray".
    by rewrite list_insert_insert_eq list_insert_id.
  Qed.
  (** Again we register this rule. *)
  Definition subsume_myarray_inst := [instance subsume_myarray].
  Global Existing Instance subsume_myarray_inst.

  Lemma my_array_example l i l' tys n:
    ⌜tys !! i = Some (n @ int i32)⌝ -∗
    l' ◁ₗ (n @ int i32) -∗
    l ◁ₗ myarray (<[i := place l']> tys) -∗
    l ◁ₗ myarray tys ∗ True.
  Proof.
    iStartProof.
    repeat liRStep; liShow.
    (** Success! Lithium can automatically solve this goal now. *)
  Qed.

  (** Let's look at a more complicated version of the example that
  uses the typing rule from above. In particular, let us replace the
  True continuation with some code that reads from [l +ₗ i]. This is
  modelled by the basic goal [typed_val_expr] that represents a typing
  judgment of RefinedC. The crucial thing to notice here is that the
  ownership that is not necessary to prove [l ◁ₗ myarray tys] is
  automatically available to the continuation that contains the
  typed_val_expr. *)
  Lemma my_array_example_2 l (i : nat) tys n:
    ⌜tys !! i = Some (place (l +ₗ i))⌝ -∗
    l ◁ₗ myarray (<[i := (n @ int i32)]> tys) -∗
    l ◁ₗ myarray tys ∗
      typed_val_expr (use{IntOp i32} (l +ₗ i)) (λ v ty,
        subsume (v ◁ᵥ ty) (-) (λ _ : unit, v ◁ᵥ n @ int i32) (λ _, True)).
  Proof.
    iStartProof.
    (** The goal can be solved automatically:*)
    (* repeat liRStep; liShow. *)
    (** But let's step through this more carefully: First, we skip to
    the subsume: *)
    do 5 liRStep; liShow.
    (** Now we can step through how the rule from above is handled: *)
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    liRStep; liShow.
    (** We end up in a state where we need to prove the continuation
    and still have access to the left-over ownership from the
    subsumption rule. RefinedC can automatically solve the rest. *)
    repeat liRStep; liShow.
  Qed.
  (** Note that the example from above could come from the following C
   code (the code below does not work directly with RefinedC since it e.g.
   assumes that l, i and tys are globally known, but the point hopefully
   still comes across):

   [[rc::requires("own l : myarray tys")]]
   void require_array();

   [[rc::requires("{tys !! i = Some (place (l +ₗ i))}")]]
   [[rc::requires("own l : myarray (<[i := (n @ int i32)]> tys)")]]
   [[rc::ensures("n @ int i32")]]
   int example() {
      require_array();
      return *(l + i);
   }
*)

  (*** Exercises *)
  (** 1. Write some other goals that fall in the grammar of goals and run
   the Lithium interpreter on it until you have an intuition how
   Lithium works.

   2. Why can Lithium not solve the goal [P -∗ P]? How should it be
   modified such that Lithium can solve it?

   3. Try defining your own subsumption rules.
*)

End lithium.


(* Generated from [tutorial/lithium.c]. *)
Section proof_lithium_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [lithium_test]. *)
  Lemma type_lithium_test :
    ⊢ typed_function impl_lithium_test type_of_lithium_test.
  Proof.
    (** Boiler plate code at the start of a function, ignore this. *)
    Local Open Scope printing_sugar.
    start_function "lithium_test" (n) => arg_a.
    (** The following tactic gives the loop invariants for this
    function. In this case, there are none since the function does not
    contain loops. *)
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - (** We remove the location information for this proof to make
      the code more readable. *)
      unfold LocInfo in *.

      (** Now we can start the actual proof. We already have the
      ownership of the argument a in the context. *)
      (** First, we need to prove [typed_stmt (Goto "#0")], which is a
      basic goal that says that the the statement (Goto "#0") is
      well-typed. The corresponding rule replaces the goto with the
      statement of this block from the control-flow graph. *)
      liRStep; liShow.
      (** Now we need to show that the first if-statement is well-typed.
      For this, we first apply the structural rule [type_if], which says that to
      type-check an if, we first need to type-check the condition and
      then prove the specialized [typed_if] judgement. *)
      liRStep; liShow.
      (** We know see the another kind of basic goal: [typed_val_expr e G].
      It expresses, that the expression [e] is well-typed and it infers a type
      (and value) for this expression, which is passed to the continuation G.

      Here we need to type-check the != between the argument a and NULL
      Again, we apply a structural rule [type_bin_op]. Here, we
      first need to type-check the arguments and then prove a
      [typed_bin_op] for the types inferred for the arguments. *)
      liRStep; liShow.

      (** Let's skip over the type-checking of arguments. *)
      do 14 liRStep; liShow.

      (** Now we have inferred the types of the two sides of the !=
      and can apply a rule for type-checking comparison between
      optional and NULL. This is the first rule that results in an
      interesting goal. *)
      liRStep; liShow.

      (** The rule spawn three subgoals (all separated by ∧): *)
      liRStep; liShow.

      (** First, we need to check that the pointer we are comparing
      with NULL is in bounds of its allocation. This is a technical
      detail of C and we skip over this proof. *)
      { repeat liRStep; liShow. }

      liRStep; liShow.
      (** We also skip the last subgoal that corresponds to the else branch. *)
      2: { repeat liRStep; liShow. }

      (** We are now considering the case where the optional is not
      NULL (i.e. the then branch). Our goal is li_trace, which is
      a special instruction to Lithium that records the current branch
      in the context such that it can be displayed when showing error
      messages. It does not have an effect on the goal. *)
      liRStep; liShow.

      (** and we know that the value stored in a is actually an owned
      pointer.

      A refinement type (lie &own) without explicit refinement
      contains an implicit existential quantifier for the refinement.
      This quantifier is destructed automatically before introducing
      such a type into the context. This works via the SimplifyHyp
      typeclass, where one can register rules that should be used to
      simplify hypothesis. *)
      liRStep; liShow.
      liRStep; liShow.

      (** There is another SimplifyHyp rule for the value type
      assignment of owned pointers that simplifies it to a location
      type assignment. *)
      liRStep; liShow.
      liRStep; liShow.
      liRStep; liShow.
      liRStep; liShow.

      (** Now we need to prove a if on a boolean. Since the boolean is
      true, this rule automatically simplifies the goal to type-checking the
      first branch. *)
      liRStep; liShow.
      liRStep; liShow.

      (** We go to the body of the then branch. *)
      liRStep; liShow.
      (** Here we need to type-check the return. *)
      liRStep; liShow.
      (** For this we need to type-check the addition. *)
      liRStep; liShow.

      (** We skip over type-checking of the arguments to + *)
      do 32 liRStep; liShow.

      (** Now Lithium applies the typing rule for + *)
      liRStep; liShow.

      (** The rest of the proof is straightforward. *)
      repeat liRStep; liShow.
      all: print_typesystem_goal "lithium_test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "lithium_test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "lithium_test".
  Qed.
End proof_lithium_test.
