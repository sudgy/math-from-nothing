Require Import init.

Require Export category_base.

(* begin show *)
Set Universe Polymorphism.
(* end show *)

Definition initial `{C0 : Category} (I : cat_U C0)
    := ∀ A, Singleton (morphism I A).
Definition terminal `{C0 : Category} (T : cat_U C0)
    := ∀ A, Singleton (morphism A T).

(* begin hide *)
Section InitTerm1.

Context {C0 : Category}.

(* end hide *)
Theorem initial_unique : ∀ I1 I2 : C0, initial I1 → initial I2 → I1 ≅ I2.
Proof.
    intros I1 I2 I1_init I2_init.
    apply indefinite_description.
    pose proof (I1_init I1) as I11.
    pose proof (I1_init I2) as I12.
    pose proof (I2_init I1) as I21.
    pose proof (I2_init I2) as I22.
    destruct I12 as [[f f_uni]].
    destruct I21 as [[g g_uni]].
    split.
    exists f g.
    split; apply singleton_unique2.
Qed.

Theorem initial_iso_unique : ∀ I1 I2 : C0, initial I1 → initial I2 →
    ∀ f g : morphism I1 I2, f = g.
Proof.
    intros I1 I2 I1_init I2_init f g.
    specialize (I1_init I2).
    apply singleton_unique2.
Qed.

Theorem initial_dual_terminal :
    ∀ I : C0, initial I → terminal (C0:=dual_category C0) I.
Proof.
    intros I I_init.
    exact I_init.
Qed.

Theorem terminal_dual_initial :
    ∀ I : C0, terminal I → initial (C0:=dual_category C0) I.
Proof.
    intros I I_term.
    exact I_term.
Qed.

(* begin hide *)
End InitTerm1.
Section InitTerm2.

Context {C0 : Category}.

(* end hide *)
Theorem terminal_unique : ∀ T1 T2 : C0, terminal T1 → terminal T2 → T1 ≅ T2.
Proof.
    intros I1 I2 I1_term I2_term.
    apply indefinite_description.
    pose proof (I1_term I1) as I11.
    pose proof (I1_term I2) as I12.
    pose proof (I2_term I1) as I21.
    pose proof (I2_term I2) as I22.
    destruct I21 as [[f f_uni]].
    destruct I12 as [[g g_uni]].
    split.
    exists f g.
    split; apply singleton_unique2.
Qed.

Theorem terminal_iso_unique : ∀ T1 T2 : C0, terminal T1 → terminal T2 →
    ∀ f g : morphism T1 T2, f = g.
Proof.
    intros T1 T2 T1_term T2_term f g.
    specialize (T2_term T1).
    apply singleton_unique2.
Qed.

(* begin hide *)
End InitTerm2.

(* end hide *)
(* begin show *)
Unset Universe Polymorphism.
(* end show *)
