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

Definition f_domain (C : U → Prop) := is_chain le C ∧ ∃ x, ∀ a, C a → a < x.

Let f (C : set_type f_domain) := ex_val (rand [|C]).

Lemma f_lt : ∀ C : set_type f_domain, ∀ x, [C|] x → x < f C.
Proof.
    intros C.
    exact (ex_proof (rand [|C])).
Qed.

Lemma f_eq : ∀ A B, [A|] = [B|] → f A = f B.
Proof.
    intros A B eq.
    apply f_equal.
    apply set_type_eq.
    exact eq.
Qed.

Let P (C : U → Prop) (x : U) := λ y, C y ∧ y < x.

Lemma P_wo_chain : ∀ (A : U → Prop) x, well_orders le A → f_domain (P A x).
Proof.
    intros A x A_wo.
    split.
    -   apply well_orders_chain in A_wo.
        apply (chain_subset A A_wo).
        intros a Pa.
        apply Pa.
    -   exists x.
        intros a Pa.
        apply Pa.
Qed.

Let conforming (A : U → Prop) :=
    well_orders le A ⋏
    λ H, (∀ x, A x → x = f [P A x|P_wo_chain A x H]).

Local Open Scope set_scope.

Lemma initial1 : ∀ A B, conforming A → conforming B →
    ∀ x y, A y → B x → ¬B y → x < y.
Proof.
    intros A B [A_wo A_conf] [B_wo B_conf] a b Ab Ba Bb.
    pose proof (A_wo (A - B)) as AB_ex.
    prove_parts AB_ex; [>apply inter_lsub|exists b; split; assumption|].
    destruct AB_ex as [x [[Ax Bx] x_least]].
    apply (lt_le_trans2 (x_least b (make_and Ab Bb))).
    classic_contradiction contr.
    pose proof (B_wo (B - P A x)) as BA_ex.
    prove_parts BA_ex; [>apply inter_lsub| |].
    {
        exists a.
        split; [>exact Ba|].
        unfold P.
        rewrite not_and.
        right; exact contr.
    }
    destruct BA_ex as [y [[By PAy] y_least]].
    clear a b Ba Ab Bb contr.
    pose proof (A_wo (A - P B y)) as z_ex.
    prove_parts z_ex; [>apply inter_lsub| |].
    {
        exists x.
        split; [>exact Ax|].
        unfold P.
        rewrite not_and.
        left; exact Bx.
    }
    destruct z_ex as [z [[Az PBz] z_least]].
    assert (z ≤ x) as zx.
    {
        apply z_least.
        split; [>exact Ax|].
        unfold P.
        rewrite not_and.
        left; exact Bx.
    }
    assert (P A z = P B y) as eq.
    {
        apply antisym.
        -   intros c [Ac c_lt].
            classic_contradiction PBc.
            specialize (z_least c (make_and Ac PBc)).
            destruct (le_lt_trans z_least c_lt); contradiction.
        -   intros u [Bu u_lt].
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
                apply PBz.
                split; assumption.
            +   exfalso; apply PBz.
                split; [>|exact (le_lt_trans uz u_lt)].
                assert (P A x z) as z_in.
                {
                    split; [>exact Az|].
                    exact (le_lt_trans uz u_lt2).
                }
                classic_contradiction contr.
                specialize (x_least z (make_and Az contr)).
                contradiction (irrefl _ (lt_le_trans (rand z_in) x_least)).
    }
    specialize (A_conf z Az).
    specialize (B_conf y By).
    pose proof (f_eq [_|P_wo_chain A z A_wo]
        [_|P_wo_chain B y B_wo] eq) as eq2.
    rewrite <- A_conf, <- B_conf in eq2.
    subst z.
    unfold P in PAy.
    rewrite not_and in PAy.
    destruct PAy as [Ay|yx]; [>contradiction|].
    apply yx.
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

Lemma conforming_union : conforming (⋃ conforming).
Proof.
    assert (well_orders le (⋃ conforming)) as conf_wo.
    {
        intros S S_sub [x Sx].
        pose proof Sx as Sx'.
        apply S_sub in Sx'.
        destruct Sx' as [A [A_conf Ax]].
        pose proof (ldand A_conf) as A_wo.
        specialize (A_wo (A ∩ S) (inter_lsub _ _)
            (ex_intro _ x (make_and Ax Sx))) as [a [[Aa Sa] a_le]].
        exists a.
        split; [>exact Sa|].
        intros y Sy.
        pose proof Sy as Sy'.
        apply S_sub in Sy'.
        destruct Sy' as [B [B_conf By]].
        clear x Sx Ax.
        classic_case (A y) as [Ay|nAy].
        -   apply a_le.
            split; assumption.
        -   apply (initial1 B A B_conf A_conf _ _ By Aa nAy).
    }
    split with conf_wo.
    intros x [A [A_conf Ax]].
    pose proof A_conf as [A_wo x_eq].
    specialize (x_eq x Ax).
    rewrite x_eq at 1; clear x_eq.
    apply f_eq; cbn.
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
    specialize (ub_ex _ (well_orders_chain _ (ldand conforming_union)))
        as [m m_ub].
    exists m.
    intros x' x'_gt.
    assert (f_domain (⋃ conforming)) as conforming_f.
    {
        split.
        -   apply well_orders_chain.
            apply conforming_union.
        -   exists x'.
            intros a a_in.
            apply (le_lt_trans2 x'_gt).
            apply m_ub.
            exact a_in.
    }
    pose (x := f [_|conforming_f]).
    clear x' x'_gt m m_ub.
    assert (well_orders le (⋃ conforming ∪ ❴x❵)) as wo_union_x.
    {
        intros S S_sub S_ex.
        classic_case (∃ y, S y ∧ x ≠ y) as [[y [Sy y_neq]]|y_nex].
        -   pose proof (S_sub _ Sy) as [y_in|y_in]; [>|contradiction].
            pose proof (ldand conforming_union (⋃ conforming ∩ S)) as a_ex.
            prove_parts a_ex; [>apply inter_lsub| |].
            +   exists y.
                split; assumption.
            +   destruct a_ex as [a [[a_in Sa] a_least]].
                exists a.
                split; [>exact Sa|].
                intros z Sz.
                pose proof (S_sub _ Sz) as [z_in|zx].
                *   apply a_least.
                    split; assumption.
                *   rewrite singleton_eq in zx; subst z.
                    apply f_lt.
                    exact a_in.
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
        -   pose proof (conforming_union) as [union_wo union_conf].
            rewrite (union_conf y y_in) at 1.
            apply f_eq.
            apply antisym.
            +   intros a [Aa a_lt].
                split; [>|exact a_lt].
                left.
                exact Aa.
            +   intros a [[a_in|a_eq] a_lt].
                *   split; assumption.
                *   rewrite singleton_eq in a_eq; subst a.
                    assert (y < x) as ltq
                        by exact (f_lt [_|conforming_f] _ y_in).
                    contradiction (irrefl _ (trans a_lt ltq)).
        -   rewrite singleton_eq in y_eq; subst y.
            unfold x at 1.
            apply f_eq.
            apply antisym.
            +   intros a a_in.
                split.
                *   left; exact a_in.
                *   exact (f_lt [_|conforming_f] _ a_in).
            +   intros a [a_in a_lt].
                destruct a_in as [a_in|a_eq].
                *   exact a_in.
                *   rewrite singleton_eq in a_eq; subst a.
                    contradiction (irrefl _ a_lt).
    }
    assert ((⋃ conforming ∪ ❴x❵) x) as x_in1 by (right; reflexivity).
    assert ((⋃ conforming) x) as x_in2.
    {
        exists (⋃ conforming ∪ ❴x❵).
        split; [>exact conforming_union_x|exact x_in1].
    }
    unfold x in x_in2.
    unfold f in x_in2.
    rewrite_ex_val x' x'_lt.
    specialize (x'_lt _ x_in2).
    contradiction (irrefl x' x'_lt).
Qed.

End Zorn.
End Zorn.

Export Zorn (zorn).
