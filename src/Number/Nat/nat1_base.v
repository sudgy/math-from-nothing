Require Import init.

Require Import nat0.
Declare Scope nat1_scope.
Delimit Scope nat1_scope with nat1.

Inductive nat1 : Set :=
    | nat1_one : nat1
    | nat1_suc : nat1 → nat1.
Bind Scope nat1_scope with nat1.

Fixpoint nat1_to_nat0 a := match a with
    | nat1_one => 1
    | nat1_suc a' => nat0_suc (nat1_to_nat0 a')
    end.

Theorem nat1_to_nat0_eq : ∀ a b, nat1_to_nat0 a = nat1_to_nat0 b → a = b.
    induction a.
    -   intros b eq.
        destruct b.
        +   reflexivity.
        +   cbn in eq.
            inversion eq as [eq2].
            destruct b; inversion eq2.
    -   intros b eq.
        destruct b.
        +   cbn in eq.
            inversion eq as [eq2].
            destruct a; inversion eq2.
        +   apply f_equal.
            apply IHa.
            cbn in eq.
            inversion eq.
            reflexivity.
Qed.

Theorem nat1_nz : ∀ n, 0 ≠ nat1_to_nat0 n.
    intros n eq.
    destruct n; inversion eq.
Qed.

Theorem nat1_to_nat0_ex : ∀ n, ∃ m, nat1_to_nat0 m = (nat0_suc n).
    intros n.
    nat0_induction n.
    -   exists nat1_one.
        reflexivity.
    -   destruct IHn as [m m_eq].
        exists (nat1_suc (m)).
        cbn.
        rewrite m_eq.
        reflexivity.
Qed.
