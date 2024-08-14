Require Import init.

Require Export order_bounds.
Require Import set_base.
Require Import set_set.
Require Import set_order.

Module Zorn.
Section Zorn.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.
Local Instance zorn_order : Order U := {le := op}.

Definition f_domain (C : U → Prop) := well_orders le C ∧ ∃ x, ∀ a, C a → a < x.

Let f (C : set_type f_domain) := ex_val (rand [|C]).

Lemma f_lt : ∀ C : set_type f_domain, ∀ x, [C|] x → x < f C.
Proof.
    intros C.
    exact (ex_proof (rand [|C])).
Qed.

Let P (C : U → Prop) (x : U) := λ y, C y ∧ y < x.

Lemma P_wo_domain : ∀ (A : U → Prop) x, well_orders le A → f_domain (P A x).
Proof.
    intros A x A_wo.
    split.
    -   apply (well_orders_subset A A_wo).
        intros a Sa.
        apply Sa.
    -   exists x.
        intros a Pa.
        apply Pa.
Qed.

Let conforming (A : U → Prop) :=
    well_orders le A ⋏ λ H, (∀ x, A x → x = f [P A x|P_wo_domain A x H]).

Local Open Scope set_scope.

Lemma conforming_add_wo : ∀ A, conforming [A|] → well_orders le ([A|] ∪ ❴f A❵).
Proof.
    intros A A_conf S S_sub S_ex.
    classic_case (∃ y, S y ∧ f A ≠ y) as [[y [Sy y_neq]]|y_nex].
    -   pose proof (S_sub _ Sy) as [y_in|y_in]; [>|contradiction].
        pose proof (ldand A_conf ([A|] ∩ S)) as a_ex.
        prove_parts a_ex; [>apply inter_lsub|exists y; split; assumption|].
        destruct a_ex as [a [[a_in Sa] a_least]].
        exists a.
        split; [>exact Sa|].
        intros z Sz.
        pose proof (S_sub _ Sz) as [z_in|zx].
        +   apply a_least.
            split; assumption.
        +   rewrite singleton_eq in zx; subst z.
            apply (f_lt [_|[|A]] _ a_in).
    -   assert (∀ a, S a → f A = a) as S_eq.
        {
            intros a Sa.
            rewrite not_ex in y_nex.
            specialize (y_nex a).
            rewrite not_and_impl, not_not in y_nex.
            exact (y_nex Sa).
        }
        destruct S_ex as [y Sy].
        pose proof (S_eq _ Sy); subst y.
        exists (f A).
        split; [>exact Sy|].
        intros z Sz.
        apply S_eq in Sz; subst z.
        apply refl.
Qed.

Lemma conforming_add_conforming :
    ∀ A, conforming [A|] → conforming ([A|] ∪ ❴f A❵).
Proof.
    intros A A_conf.
    split with (conforming_add_wo A A_conf).
    intros y [y_in|y_eq].
    -   rewrite (rdand A_conf y y_in) at 1.
        apply f_equal.
        rewrite set_type_eq2.
        apply antisym.
        +   intros a [Aa a_lt].
            split; [>|exact a_lt].
            left; exact Aa.
        +   intros a [[a_in|a_eq] a_lt].
            *   split; assumption.
            *   rewrite singleton_eq in a_eq; subst a.
                assert (y < f A) as ltq by exact (f_lt [_|[|A]] _ y_in).
                contradiction (irrefl _ (trans a_lt ltq)).
    -   rewrite singleton_eq in y_eq; subst y.
        apply f_equal.
        apply set_type_eq; cbn.
        apply antisym.
        +   intros a a_in.
            split.
            *   left; exact a_in.
            *   exact (f_lt [_|[|A]] _ a_in).
        +   intros a [a_in a_lt].
            destruct a_in as [a_in|a_eq]; [>exact a_in|].
            rewrite singleton_eq in a_eq; subst a.
            contradiction (irrefl _ a_lt).
Qed.

Definition neq_set A B a := A a ∧ ∃ b, b ≤ a ∧ ¬(A b ↔ B b).

Lemma least_sub : ∀ A B, conforming A → conforming B →
    ∀ m n, is_least le (neq_set A B) m → is_least le (neq_set B A) n →
    P A m ⊆ P B n.
Proof.
    intros A B [A_wo A_conf] [B_wo B_conf].
    intros m n [[Am m_neq] m_least] [[Bn n_neq] n_least].
    intros a [Aa am].
    assert (∀ b, b ≤ a → A b ↔ B b) as a_eq.
    {
        intros b leq.
        classic_contradiction contr.
        specialize (m_least a (make_and Aa (ex_intro _ _ (make_and leq contr)))).
        contradiction (irrefl _ (lt_le_trans am m_least)).
    }
    assert (B a) as Ba by (apply a_eq; [>apply refl|exact Aa]).
    split; [>exact Ba|].
    destruct n_neq as [b [bn n_neq]].
    classic_contradiction contr.
    assert (n ≤ a) as leq.
    {
        pose proof (well_orders_chain _ B_wo a n Ba Bn) as [leq|leq].
        2: exact leq.
        classic_case (a = n) as [eq|neq].
        -   subst.
            apply refl.
        -   contradiction (contr (make_and leq neq)).
    }
    specialize (a_eq b (trans bn leq)).
    symmetry in a_eq.
    contradiction.
Qed.

Lemma neq_set_nex : ∀ A B, conforming A → conforming B →
    ¬((∃ m, neq_set A B m) ∧ (∃ n, neq_set B A n)).
Proof.
    intros A B A_conf B_conf.
    intros [m_ex n_ex].
    pose proof (ldand A_conf _ (inter_lsub _ _) m_ex) as [m m_least].
    pose proof (ldand B_conf _ (inter_lsub _ _) n_ex) as [n n_least].
    assert (P A m = P B n) as eq by(apply antisym; apply least_sub; assumption).
    destruct m_least as [[Am [a [am a_nin]]] m_least].
    destruct n_least as [[Bn [b [bn b_nin]]] n_least].
    assert (m = n) as eq2.
    {
        rewrite (rdand A_conf m Am).
        rewrite (rdand B_conf n Bn).
        apply f_equal.
        rewrite set_type_eq2.
        exact eq.
    }
    subst n.
    apply a_nin.
    split.
    -   intros Aa.
        specialize (m_least a).
        prove_parts m_least.
        {
            split; [>exact Aa|].
            exists a.
            split; [>apply refl|].
            exact a_nin.
        }
        pose proof (antisym am m_least); subst a.
        exact Bn.
    -   intros Ba.
        specialize (n_least a).
        prove_parts n_least.
        {
            split; [>exact Ba|].
            exists a.
            split; [>apply refl|].
            intros contr.
            symmetry in contr.
            contradiction.
        }
        pose proof (antisym am n_least); subst a.
        exact Am.
Qed.

Lemma initial1 : ∀ A B, conforming A → conforming B →
    ∀ x y, x ≤ y → A x → B y → B x.
Proof.
    intros A B A_conf B_conf x y xy Ax By.
    classic_contradiction Bx.
    apply (neq_set_nex A B A_conf B_conf).
    split.
    -   exists x.
        split; [>exact Ax|].
        exists x.
        split; [>apply refl|].
        intros contr.
        apply contr in Ax.
        contradiction.
    -   exists y.
        split; [>exact By|].
        exists x.
        split; [>exact xy|].
        intros contr.
        apply contr in Ax.
        contradiction.
Qed.

Lemma initial2 : ∀ A B, conforming A → conforming B →
    ∀ x y, A y → B x → ¬B y → x ≤ y.
Proof.
    intros A B A_conf B_conf x y Ay Bx By.
    classic_case (A x) as [Ax|Ax].
    -   pose proof (well_orders_chain A (ldand A_conf) x y Ax Ay) as [leq|leq].
        1: exact leq.
        pose proof (initial1 A B A_conf B_conf y x leq Ay Bx).
        contradiction.
    -   exfalso.
        apply (neq_set_nex A B A_conf B_conf).
        split.
        +   exists y.
            split; [>exact Ay|].
            exists y.
            split; [>apply refl|].
            intros contr.
            apply contr in Ay.
            contradiction.
        +   exists x.
            split; [>exact Bx|].
            exists x.
            split; [>apply refl|].
            intros contr.
            apply contr in Bx.
            contradiction.
Qed.

Lemma union_conf : conforming (⋃ conforming).
Proof.
    assert (well_orders le (⋃ conforming)) as conf_wo.
    {
        intros S S_sub [x Sx].
        pose proof (S_sub _ Sx) as [A [A_conf Ax]].
        pose proof (ldand A_conf (A ∩ S) (inter_lsub _ _)
            (ex_intro _ x (make_and Ax Sx))) as [a [[Aa Sa] a_le]].
        exists a.
        split; [>exact Sa|].
        intros y Sy.
        pose proof (S_sub _ Sy) as [B [B_conf By]].
        clear x Sx Ax.
        classic_case (A y) as [Ay|nAy].
        -   apply a_le.
            split; assumption.
        -   apply (initial2 B A B_conf A_conf _ _ By Aa nAy).
    }
    split with conf_wo.
    intros x [A [A_conf Ax]].
    rewrite (rdand A_conf x Ax) at 1.
    apply f_equal.
    rewrite set_type_eq2.
    apply antisym.
    -   intros c [Ac c_lt].
        split; [>|exact c_lt].
        exists A.
        split; assumption.
    -   intros c [[B [B_conf Bc]] c_lt].
        split; [>|exact c_lt].
        exact (initial1 B A B_conf A_conf _ _ (land c_lt) Bc Ax).
Qed.

Lemma union_no_sub : ∀ x, ¬(∀ a, (⋃ conforming) a → a < x).
Proof.
    intros x' x'_sub.
    assert (f_domain (⋃ conforming)) as union_f.
    {
        split.
        -   apply union_conf.
        -   exists x'.
            intros a a_in.
            apply x'_sub.
            exact a_in.
    }
    clear x' x'_sub.
    pose proof (conforming_add_conforming [_|union_f] union_conf)
        as conforming_union_x.
    pose (x := f [_|union_f]).
    assert ((⋃ conforming ∪ ❴x❵) x) as x_in1 by (right; reflexivity).
    assert ((⋃ conforming) x) as x_in2.
    {
        exists (⋃ conforming ∪ ❴x❵).
        split; [>exact conforming_union_x|exact x_in1].
    }
    pose proof (f_lt [_|union_f] _ x_in2) as ltq.
    contradiction (irrefl _ ltq).
Qed.

Theorem zorn : (∀ F : U → Prop, is_chain le F → has_upper_bound le F) →
    ∃ a : U, ∀ x : U, ¬ a < x.
Proof.
    intros ub_ex.
    specialize (ub_ex _ (well_orders_chain _ (ldand union_conf))) as [m m_ub].
    exists m.
    intros x x_gt.
    apply (union_no_sub x).
    intros a a_in.
    apply (le_lt_trans2 x_gt).
    apply m_ub.
    exact a_in.
Qed.

End Zorn.
End Zorn.

Export Zorn (zorn).
