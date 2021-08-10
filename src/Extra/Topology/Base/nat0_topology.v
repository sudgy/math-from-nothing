Require Import init.

Require Import topology.

Lemma nat0_distinct : ∃ a b : nat0, a ≠ b.
    exists 0, 1.
    exact not_trivial.
Qed.

Definition nat0_order_topology := order_topology nat0_distinct.

Theorem nat0_order_discrete_topology :
        @basis_topology _ nat0_order_topology = discrete_topology.
    apply single_open_discrete.
    intros n.
    nat0_destruct n.
    -   apply basis_open.
        right; right.
        exists 0, 1.
        split.
        +   apply antisym.
            *   intros n n_eq.
                rewrite <- n_eq.
                split.
                --  apply refl.
                --  apply nat0_0_lt_1.
            *   intros n [n_ge n_lt].
                unfold one in n_lt; cbn in n_lt.
                rewrite nat0_lt_suc_le in n_lt.
                rewrite (antisym n_ge n_lt).
                reflexivity.
        +   exact nat0_le_zero.
    -   apply basis_open.
        left.
        exists n, (nat0_suc (nat0_suc n)).
        apply antisym.
        +   intros m m_eq.
            rewrite <- m_eq.
            split; apply nat0_lt_suc.
        +   intros m [m_lt1 m_lt2].
            rewrite <- nat0_sucs_lt in m_lt1.
            rewrite nat0_lt_suc_le in m_lt1.
            rewrite nat0_lt_suc_le in m_lt2.
            exact (antisym m_lt1 m_lt2).
Qed.
