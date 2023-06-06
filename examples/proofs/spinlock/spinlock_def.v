From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import generated_code.
From refinedc.typing Require Import type_options.

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.

  Definition spinlock (γ : lock_id) : type :=
    struct struct_spinlock [atomic_bool u8 True (lock_token γ [])].

  Global Instance alloc_alive_spinlock γ β : AllocAlive (spinlock γ) β True.
  Proof. apply: _. Qed.

  Lemma spinlock_subsume γ1 γ2 l β T:
    ⌜γ1 = γ2⌝ ∗ T
    ⊢ subsume (l ◁ₗ{β} spinlock γ1) (l ◁ₗ{β} spinlock γ2) T.
  Proof. iIntros "[-> $] $". Qed.
  Definition spinlock_subsume_inst := [instance spinlock_subsume].
  Global Existing Instance spinlock_subsume_inst.

  Global Instance spinlock_with_lock_id γ : WithLockId (spinlock γ) γ := I.
End type.

Global Typeclasses Opaque spinlock.
