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

Context `{C0 : Category}.

(* end hide *)
Theorem initial_all_iso : ∀ I1 I2, initial I1 → initial I2 →
    ∀ f : morphism I1 I2, isomorphism f.
Proof.
    intros I1 I2 I1_init I2_init f.
    pose proof (I1_init I1) as I1_self.
    pose proof (I2_init I2) as I2_self.
    specialize (I2_init I1).
    destruct I2_init as [[g g_uni]].
    exists g.
    rewrite (singleton_unique2 (f ∘ g) 𝟙).
    rewrite (singleton_unique2 (g ∘ f) 𝟙).
    split; reflexivity.
Qed.

Theorem initial_unique : ∀ I1 I2, initial I1 → initial I2 → I1 ≅ I2.
Proof.
    intros I1 I2 I1_init I2_init.
    pose proof (I1_init I2) as I1_init'.
    destruct I1_init' as [[f f_uni]].
    exists f.
    apply initial_all_iso; assumption.
Qed.

Theorem initial_iso_unique : ∀ I1 I2, initial I1 → initial I2 →
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

Context `{C0 : Category}.

(* end hide *)
Theorem terminal_all_iso : ∀ T1 T2, terminal T1 → terminal T2 →
    ∀ f : morphism T1 T2, isomorphism f.
Proof.
    intros T1 T2 T1_term T2_term f.
    apply terminal_dual_initial in T1_term, T2_term.
    rewrite dual_isomorphism.
    exact (initial_all_iso _ _ T2_term T1_term f).
Qed.

Theorem terminal_unique : ∀ T1 T2, terminal T1 → terminal T2 → T1 ≅ T2.
Proof.
    intros T1 T2 T1_term T2_term.
    apply terminal_dual_initial in T1_term, T2_term.
    pose proof (initial_unique _ _ T2_term T1_term) as [f f_iso].
    exists f.
    rewrite dual_isomorphism.
    exact f_iso.
Qed.

Theorem terminal_iso_unique : ∀ T1 T2, terminal T1 → terminal T2 →
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
