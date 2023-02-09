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

Lemma initial1 : ∀ A B, conforming A → conforming B →
    ∀ x y, A y → B x → ¬B y → x < y.
Proof.
    intros A B [A_wo A_conf] [B_wo B_conf] a b Ab Ba Bb.
    pose proof (A_wo (A - B)) as AB_ex.
    prove_parts AB_ex; [>apply inter_lsub|exists b; split; assumption|].
    destruct AB_ex as [x [[Ax Bx] x_least]].
    apply (lt_le_trans2 (x_least b (make_and Ab Bb))).
    clear b Ab Bb.
    classic_contradiction contr.
    pose proof (B_wo (B - P A x) (inter_lsub _ _)) as BA_ex.
    prove_parts BA_ex;
        [>exists a; split; [>exact Ba|intros [C0 C1]; contradiction]|].
    destruct BA_ex as [y [[By PAy] y_least]].
    clear a Ba contr.
    pose proof (A_wo (A - P B y) (inter_lsub _ _)) as z_ex.
    prove_parts z_ex;
        [>exists x; split; [>exact Ax|intros [C0 C1]; contradiction]|].
    destruct z_ex as [z [[Az PBz] z_least]].
    assert (z ≤ x) as zx.
    {
        apply z_least.
        split.
        -   exact Ax.
        -   intros [C0 C1]; contradiction.
    }
    assert (P A z = P B y) as eq.
    {
        apply antisym.
        -   intros c [Ac c_lt].
            classic_contradiction PBc.
            specialize (z_least c (make_and Ac PBc)).
            contradiction (irrefl _ (le_lt_trans z_least c_lt)).
        -   intros u PBu.
            pose proof PBu as [Bu u_lt].
            assert (P A x u) as [Au u_lt2].
            {
                classic_contradiction Au.
                specialize (y_least u (make_and Bu Au)).
                contradiction (irrefl _ (lt_le_trans u_lt y_least)).
            }
            split; [>apply Au|].
            destruct (well_orders_chain A A_wo u z Au Az) as [uz|uz].
            +   split; [>exact uz|].
                intros contr; subst u.
                contradiction.
            +   exfalso; apply PBz.
                split; [>|exact (le_lt_trans uz u_lt)].
                classic_contradiction contr.
                specialize (x_least z (make_and Az contr)).
                pose proof (lt_le_trans (le_lt_trans uz u_lt2) x_least) as ltq.
                contradiction (irrefl _ ltq).
    }
    apply (set_type_eq (a := [_|P_wo_domain A z A_wo])
        (b := [_|P_wo_domain B y B_wo])) in eq.
    apply (f_equal f) in eq.
    rewrite <- (A_conf z Az), <- (B_conf y By) in eq.
    subst z.
    apply PAy.
    split; [>exact Az|].
    split; [>exact zx|].
    intro; subst y.
    contradiction.
Qed.

Lemma initial2 : ∀ A B, conforming A → conforming B →
    ∀ x y, x ≤ y → A x → B y → B x.
Proof.
    intros A B A_conf B_conf x y xy Ax By.
    classic_contradiction Bx.
    pose proof (initial1 A B A_conf B_conf y x Ax By Bx) as ltq.
    contradiction (irrefl _ (le_lt_trans xy ltq)).
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
        -   apply (initial1 B A B_conf A_conf _ _ By Aa nAy).
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
        exact (initial2 B A B_conf A_conf _ _ (land c_lt) Bc Ax).
Qed.

Theorem zorn : (∀ F : U → Prop, is_chain le F → has_upper_bound le F) →
    ∃ a : U, ∀ x : U, ¬ a < x.
Proof.
    intros ub_ex.
    specialize (ub_ex _ (well_orders_chain _ (ldand union_conf))) as [m m_ub].
    exists m.
    intros x' x'_gt.
    assert (f_domain (⋃ conforming)) as union_f.
    {
        split.
        -   apply union_conf.
        -   exists x'.
            intros a a_in.
            apply (le_lt_trans2 x'_gt).
            apply m_ub.
            exact a_in.
    }
    clear x' x'_gt m m_ub.
    pose (x := f [_|union_f]).
    assert (well_orders le (⋃ conforming ∪ ❴x❵)) as wo_union_x.
    {
        intros S S_sub S_ex.
        classic_case (∃ y, S y ∧ x ≠ y) as [[y [Sy y_neq]]|y_nex].
        -   pose proof (S_sub _ Sy) as [y_in|y_in]; [>|contradiction].
            pose proof (ldand union_conf (⋃ conforming ∩ S)) as a_ex.
            prove_parts a_ex; [>apply inter_lsub|exists y; split; assumption|].
            destruct a_ex as [a [[a_in Sa] a_least]].
            exists a.
            split; [>exact Sa|].
            intros z Sz.
            pose proof (S_sub _ Sz) as [z_in|zx].
            +   apply a_least.
                split; assumption.
            +   rewrite singleton_eq in zx; subst z.
                apply (f_lt [_|union_f] _ a_in).
        -   assert (∀ a, S a → x = a) as S_eq.
            {
                intros a Sa.
                rewrite not_ex in y_nex.
                specialize (y_nex a).
                rewrite not_and_impl, not_not in y_nex.
                exact (y_nex Sa).
            }
            destruct S_ex as [y Sy].
            pose proof (S_eq _ Sy); subst y.
            exists x.
            split; [>exact Sy|].
            intros z Sz.
            apply S_eq in Sz; subst z.
            apply refl.
    }
    assert (conforming (⋃ conforming ∪ ❴x❵)) as conforming_union_x.
    {
        split with wo_union_x.
        intros y [y_in|y_eq].
        -   rewrite (rdand union_conf y y_in) at 1.
            apply f_equal.
            rewrite set_type_eq2.
            apply antisym.
            +   intros a [Aa a_lt].
                split; [>|exact a_lt].
                left; exact Aa.
            +   intros a [[a_in|a_eq] a_lt].
                *   split; assumption.
                *   rewrite singleton_eq in a_eq; subst a.
                    assert (y < x) as ltq by exact (f_lt [_|union_f] _ y_in).
                    contradiction (irrefl _ (trans a_lt ltq)).
        -   rewrite singleton_eq in y_eq; subst y.
            apply f_equal.
            rewrite set_type_eq2.
            apply antisym.
            +   intros a a_in.
                split.
                *   left; exact a_in.
                *   exact (f_lt [_|union_f] _ a_in).
            +   intros a [a_in a_lt].
                destruct a_in as [a_in|a_eq]; [>exact a_in|].
                rewrite singleton_eq in a_eq; subst a.
                contradiction (irrefl _ a_lt).
    }
    assert ((⋃ conforming ∪ ❴x❵) x) as x_in1 by (right; reflexivity).
    assert ((⋃ conforming) x) as x_in2.
    {
        exists (⋃ conforming ∪ ❴x❵).
        split; [>exact conforming_union_x|exact x_in1].
    }
    pose proof (f_lt [_|union_f] _ x_in2) as ltq.
    contradiction (irrefl _ ltq).
Qed.

End Zorn.
End Zorn.

Export Zorn (zorn).
