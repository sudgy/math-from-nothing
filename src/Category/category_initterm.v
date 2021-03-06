Require Import init.
Require Import card.

Require Export category_base.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
(* begin show *)
Set Universe Polymorphism.
(* end show *)

Definition initial `{C0 : Category} (I : cat_U C0)
    := ∀ A, |cat_morphism C0 I A| = 1.
Definition terminal `{C0 : Category} (T : cat_U C0)
    := ∀ A, |cat_morphism C0 A T| = 1.

(* begin hide *)
Section InitTerm1.

Context `{C0 : Category}.

(* end hide *)
Theorem initial_all_iso : ∀ I1 I2, initial I1 → initial I2 →
        ∀ f : cat_morphism C0 I1 I2, isomorphism f.
    intros I1 I2 I1_init I2_init f.
    pose proof (I1_init I1) as I1_self.
    pose proof (I2_init I2) as I2_self.
    specialize (I2_init I1).
    apply card_one_ex in I2_init as g.
    exists g.
    rewrite (card_one_eq I2_self (f ∘ g) 𝟙).
    rewrite (card_one_eq I1_self (g ∘ f) 𝟙).
    split; reflexivity.
Qed.

Theorem initial_unique : ∀ I1 I2, initial I1 → initial I2 → I1 ≅ I2.
    intros I1 I2 I1_init I2_init.
    pose proof (I1_init I2) as I1_init'.
    apply card_one_ex in I1_init' as f.
    exists f.
    apply initial_all_iso; assumption.
Qed.

Theorem initial_iso_unique : ∀ I1 I2, initial I1 → initial I2 →
        ∀ f g : cat_morphism C0 I1 I2, f = g.
    intros I1 I2 I1_init I2_init f g.
    apply card_one_eq.
    exact (I1_init I2).
Qed.

Theorem initial_dual_terminal :
        ∀ I : cat_U C0, initial I → terminal (C0:=dual_category C0) I.
    intros I I_init.
    exact I_init.
Qed.

Theorem terminal_dual_initial :
        ∀ I : cat_U C0, terminal I → initial (C0:=dual_category C0) I.
    intros I I_term.
    exact I_term.
Qed.

(* begin hide *)
End InitTerm1.
Section InitTerm2.

Context `{C0 : Category}.

(* end hide *)
Theorem terminal_all_iso : ∀ T1 T2, terminal T1 → terminal T2 →
        ∀ f : cat_morphism C0 T1 T2, isomorphism f.
    intros T1 T2 T1_term T2_term f.
    apply terminal_dual_initial in T1_term, T2_term.
    rewrite dual_isomorphism.
    exact (initial_all_iso _ _ T2_term T1_term f).
Qed.

Theorem terminal_unique : ∀ T1 T2, terminal T1 → terminal T2 → T1 ≅ T2.
    intros T1 T2 T1_term T2_term.
    apply terminal_dual_initial in T1_term, T2_term.
    pose proof (initial_unique _ _ T2_term T1_term) as [f f_iso].
    exists f.
    rewrite dual_isomorphism.
    exact f_iso.
Qed.

Theorem terminal_iso_unique : ∀ T1 T2, terminal T1 → terminal T2 →
        ∀ f g : cat_morphism C0 T1 T2, f = g.
    intros T1 T2 T1_term T2_term f g.
    apply card_one_eq.
    exact (T2_term T1).
Qed.

(* begin hide *)
End InitTerm2.

(* end hide *)
(* begin show *)
Unset Universe Polymorphism.
(* end show *)
(* begin hide *)

Close Scope card_scope.
(* end hide *)
