From iris.base_logic.lib Require Import iprop.
From lithium Require Export base.

(** This file provides the classes for the simplification
infrastructure for pure sideconditions. *)

(** * [SimplExist] and [SimplForall] *)
Class SimplExist {Σ} (A : Type) (Q : (A → iProp Σ) → iProp Σ) :=
  simpl_exist P : Q P ⊢ ∃ x : A, P x.
Global Hint Mode SimplExist + ! - : typeclass_instances.

(* TODO: refactor similar to SimplExist? *)
Class SimplForall (T : Type) (n : nat) (e : T → Prop) (Q: Prop) := simpl_forall_proof : Q → ∀ x, e x.

(** * [SimplImpl] and [SimplAnd] *)

(** ** [SimplAndImpl] *)
(** changed = false indicates that P should be introduced into the context in addition to Ps
    safe = true indicates that the simplification preserves provability *)
Class SimplAndImpl (impl : bool) (safe : bool) (changed : bool)
  (P Ps : Prop) := {
  simpl_and_impl :
    if safe then P ↔ Ps
    else if impl then P → Ps else Ps → P
}.
Global Hint Mode SimplAndImpl + - - ! - : typeclass_instances.

Notation SimplImplUnsafe := (SimplAndImpl true false).
Notation SimplAndUnsafe := (SimplAndImpl false false true).
Notation SimplImpl := (SimplAndImpl true true true).
Notation SimplAnd := (SimplAndImpl false true true).
Notation SimplBoth P Ps := (∀ b, SimplAndImpl b true true P Ps).

Lemma simpl_impl_unsafe_impl changed safe (P1 P2 T : Prop)
  `{!SimplAndImpl true safe changed P1 P2} :
  (if changed then (P2 → T) else (P1 → P2 → T)) → (P1 → T).
Proof. destruct SimplAndImpl0. destruct changed, safe; naive_solver. Qed.
Lemma simpl_and_unsafe safe (P1 P2 : Prop)
 `{!SimplAndImpl false safe true P1 P2} :
  P2 → P1.
Proof. destruct SimplAndImpl0, safe; naive_solver. Qed.
Lemma simpl_and_unsafe_and safe (P1 P2 T : Prop)
 `{!SimplAndImpl false safe true P1 P2} :
  P2 ∧ T → P1 ∧ T.
Proof. destruct SimplAndImpl0, safe; naive_solver. Qed.

Global Instance simpland_unsafe_not_neq {A} (x y : A) :
  SimplAndUnsafe (¬ (x ≠ y)) (x = y) | 1000.
Proof. constructor. move => ?. by eauto. Qed.

(** To build the symmetric version of a lemma, use the following
lemmas. See [simpl_instances.v] for an example. *)
Lemma simpl_and_impl_sym {A} (R : A → A → Prop) {a1 a2 Ps} {impl safe changed}
  `{!Symmetric R} :
  SimplAndImpl impl safe changed (R a1 a2) Ps →
  SimplAndImpl impl safe changed (R a2 a1) Ps.
Proof. move => [?]. constructor. destruct safe, impl;  naive_solver. Qed.

Lemma simpl_both_sym {A} (R : A → A → Prop) {a1 a2 Ps}
  `{!Symmetric R} :
  SimplBoth (R a1 a2) Ps →
  SimplBoth (R a2 a1) Ps.
Proof. move => ??. by apply simpl_and_impl_sym. Qed.


(* We could use the following Ltac to generate the symmetry instances,
but one cannot pass terms with holes (like [@eq _]) to notations, so
it is less useful than one might hope. Ideally, this would be an
attribute one could add, e.g. using elpi. *)
Ltac generate_simpl_and_impl_sym print R c :=
  let do_print t := tryif print then t else idtac in
  let type_c := type of c in
  let type_c := eval lazy zeta in type_c in
  do_print ltac:(idtac "current:" c);
  do_print ltac:(idtac "type:" type_c);
  lazymatch type_c with
  | ∀ (a : ?T), @?P a =>
    let a := fresh a in
    notypeclasses refine (λ a, _);
    let y := eval lazy beta zeta in (c a) in
    generate_simpl_and_impl_sym print R y
  | SimplAndImpl _ _ _ _ _ =>
    refine (simpl_and_impl_sym R c)
  end.

Notation "'[simplsym' R | x ]" :=
  ltac:(generate_simpl_and_impl_sym ltac:(fail) open_constr:(R) x) (only parsing).
