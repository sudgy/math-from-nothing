Require Import init.

Require Export category_base.

(* begin show *)
Set Universe Polymorphism.
(* end show *)

Definition initial {C : Category} (I : cat_U C)
    := ∀ A, Singleton (morphism I A).
Definition terminal {C : Category} (T : cat_U C)
    := ∀ A, Singleton (morphism A T).

Section InitTerm1.

Context {C : Category}.

Theorem initial_unique : ∀ I1 I2 : C, initial I1 → initial I2 → I1 ≅ I2.
Proof.
    intros I1 I2 I1_init I2_init.
    apply indefinite_description.
    pose proof (I1_init I1) as I11.
    pose proof (I2_init I2) as I22.
    pose proof (I1_init I2) as [[f f_uni]].
    pose proof (I2_init I1) as [[g g_uni]].
    split.
    exists f g.
    split; apply singleton_unique2.
Qed.

Theorem initial_dual_terminal :
    ∀ I : C, initial I → terminal (I : dual_category C).
Proof.
    intros I I_init.
    exact I_init.
Qed.

Theorem terminal_dual_initial :
    ∀ I : C, terminal I → initial (I : dual_category C).
Proof.
    intros I I_term.
    exact I_term.
Qed.

End InitTerm1.
Section InitTerm2.

Context {C : Category}.

Theorem terminal_unique : ∀ T1 T2 : C, terminal T1 → terminal T2 → T1 ≅ T2.
Proof.
    intros I1 I2 I1_term I2_term.
    apply dual_isomorphic2.
    apply initial_unique; assumption.
Qed.

End InitTerm2.

(* begin show *)
Unset Universe Polymorphism.
(* end show *)
