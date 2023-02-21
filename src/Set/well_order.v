Require Import init.

Require Import zorn.
Require Import set.

Section WellOrder.

Context {U : Type}.

Record wo_func := make_wo_func {
    wo_domain : U → Prop;
    wo_f : U → U → Prop;
    wo_f_antisym : Antisymmetric (λ x y : set_type wo_domain, wo_f [x|] [y|]);
    wo_f_wo : WellOrdered (λ x y : set_type wo_domain, wo_f [x|] [y|]);
    wo_f_top : ∀ a b, ¬wo_domain a → wo_f a b ∧ wo_f b a;
}.

Theorem wo_func_eq : ∀ f g : wo_func, wo_domain f = wo_domain g →
    (∀ a b, wo_domain f a → wo_domain f b → wo_f f a b = wo_f g a b) →
    f = g.
Proof.
    intros [f_domain f_f f_antisym f_wo f_top]
           [g_domain g_f g_antisym g_wo g_top].
    cbn.
    intros eq bottom.
    subst g_domain.
    assert (f_f = g_f) as eq.
    {
        apply functional_ext.
        intros x.
        apply functional_ext.
        intros y.
        classic_case (f_domain x) as [x_in|x_nin].
        1: classic_case (f_domain y) as [y_in|y_nin].
        -   apply bottom; assumption.
        -   specialize (f_top y x y_nin) as [f_top1 f_top2].
            specialize (g_top y x y_nin) as [g_top1 g_top2].
            apply propositional_ext.
            split; intro; assumption.
        -   specialize (f_top x y x_nin) as [f_top1 f_top2].
            specialize (g_top x y x_nin) as [g_top1 g_top2].
            apply propositional_ext.
            split; intro; assumption.
    }
    subst g_f.
    rewrite (proof_irrelevance g_antisym f_antisym).
    rewrite (proof_irrelevance g_wo f_wo).
    rewrite (proof_irrelevance g_top f_top).
    reflexivity.
Qed.

Local Instance wo_func_order : Order wo_func := {
    le f g := (wo_domain f ⊆ wo_domain g) ∧
              (∀ a b, wo_domain f a → wo_domain f b → wo_f f a b → wo_f g a b) ∧
              (∀ a b, wo_domain f a → ¬wo_domain f b → wo_f g a b)
}.

Local Instance wo_func_order_refl : Reflexive le.
Proof.
    split.
    intros f.
    split; [>|split].
    -   apply refl.
    -   trivial.
    -   intros a b a_in b_nin.
        apply wo_f_top.
        exact b_nin.
Qed.

Local Instance wo_func_order_antisym : Antisymmetric le.
Proof.
    split.
    intros f g [fg_sub [fg_ext fg_bigger]] [gf_sub [gf_ext gf_bigger]].
    apply wo_func_eq.
    -   apply antisym; assumption.
    -   intros a b fa fb.
        apply propositional_ext.
        split.
        +   apply fg_ext; assumption.
        +   apply fg_sub in fa, fb.
            apply gf_ext; assumption.
Qed.

Local Instance wo_func_order_trans : Transitive le.
Proof.
    split.
    intros f g h [fg_sub [fg_ext fg_bigger]] [gh_sub [gh_ext gh_bigger]].
    split; [>|split].
    -   exact (trans fg_sub gh_sub).
    -   intros a b fa fb f_in.
        apply (gh_ext _ _ (fg_sub _ fa) (fg_sub _ fb)).
        apply (fg_ext _ _ fa fb).
        exact f_in.
    -   intros a b a_in b_nin.
        pose proof (fg_bigger _ _ a_in b_nin) as ab.
        apply fg_sub in a_in.
        classic_case (wo_domain g b) as [gb|gb].
        +   apply gh_ext; assumption.
        +   apply gh_bigger; assumption.
Qed.

Lemma wo_f_anti : ∀ {f a b}, wo_domain f a → wo_domain f b →
    wo_f f a b → wo_f f b a → a = b.
Proof.
    intros f a b fa fb ab ba.
    pose proof (wo_f_antisym f) as f_anti.
    change a with [[a|fa]|] in ab, ba.
    change b with [[b|fb]|] in ab, ba.
    pose proof (antisym (Antisymmetric := f_anti) ab ba) as eq.
    rewrite set_type_eq2 in eq.
    exact eq.
Qed.

Theorem wo_ex : ∃ F : wo_func, ∀ X, ¬F < X.
Proof.
    apply zorn.
    apply wo_func_order_refl.
    apply wo_func_order_antisym.
    apply wo_func_order_trans.
    intros F F_chain.
    pose (F_domain := ⋃image_under wo_domain F).
    pose (F_f a b :=
        IfH (∃ f, F f ∧ wo_domain f a ∧ wo_domain f b)
        then λ H, wo_f (ex_val H) a b
        else λ _, True
    ).
    assert (∀ f a b, wo_domain f a → wo_domain f b → F f → wo_f f a b → F_f a b)
        as F_f_lem.
    {
        intros f a b fa fb Ff ab.
        unfold F_f.
        destruct (sem _) as [g_ex|]; [>|exact true]; cbn.
        rewrite_ex_val g [Fg [ga gb]]; clear g_ex.
        specialize (F_chain f g Ff Fg) as [leq|leq].
        -   apply leq in ab; assumption.
        -   pose proof (wo_f_wo g) as g_wo.
            destruct (connex [a|ga] [b|gb]) as [ab'|ba]; [>exact ab'|].
            cbn in ba.
            apply leq in ba; [>|assumption|assumption].
            rewrite (wo_f_anti fa fb ab ba).
            exact (refl [b|gb]).
    }
    assert (Antisymmetric (λ x y : set_type F_domain, F_f [x|] [y|]))
        as F_f_antisym.
    {
        split.
        intros [a Fa] [b Fb]; cbn.
        unfold F_f.
        rewrite set_type_eq2.
        destruct (sem _) as [f_ex|f_nex]; cbn.
        all: destruct (sem _) as [g_ex|g_nex]; cbn.
        -   rewrite_ex_val f [Ff [fa fb]].
            rewrite_ex_val g [Fg [gb ga]].
            intros ab ba.
            specialize (F_chain f g Ff Fg) as [leq|leq].
            +   apply leq in ab; [>|assumption|assumption].
                exact (wo_f_anti ga gb ab ba).
            +   apply leq in ba; [>|assumption|assumption].
                exact (wo_f_anti fa fb ab ba).
        -   exfalso; apply g_nex.
            destruct f_ex as [f [Ff [fa fb]]].
            exists f.
            repeat split; assumption.
        -   exfalso; apply f_nex.
            destruct g_ex as [g [Fg [ga gb]]].
            exists g.
            repeat split; assumption.
        -   destruct Fa as [A [[f [Ff A_eq]] Aa]]; subst A.
            destruct Fb as [B [[g [Fg B_eq]] Bb]]; subst B.
            exfalso; apply f_nex.
            specialize (F_chain f g Ff Fg) as [leq|leq].
            +   apply leq in Aa.
                exists g.
                repeat split; assumption.
            +   apply leq in Bb.
                exists f.
                repeat split; assumption.
    }
    assert (WellOrdered (λ x y : set_type F_domain, F_f [x|] [y|])) as F_f_wo.
    {
        split.
        intros S [x Sx].
        destruct x as [x x_in].
        pose proof x_in as [A [[f [Ff A_eq]] Ax]]; subst A.
        assert (∀ a, wo_domain f a → F_domain a) as a_in.
        {
            intros a a_in.
            exists (wo_domain f).
            split; [>|exact a_in].
            exists f.
            split; trivial.
        }
        pose proof (wo_f_wo f) as f_wo.
        pose (S' (a : set_type (wo_domain f)) := S [[a|] | a_in [a|] [|a]]).
        pose proof (well_ordered S') as a_ex.
        prove_parts a_ex.
        {
            exists [x|Ax].
            unfold S'; cbn.
            applys_eq Sx.
            apply set_type_eq2.
            reflexivity.
        }
        destruct a_ex as [[a fa] [Sa a_least]].
        unfold S' in Sa; cbn in Sa.
        exists [a | a_in a fa].
        split; [>exact Sa|].
        cbn in *.
        intros [b b_in] Sb; cbn.
        assert (wo_domain f b → F_f a b) as lem.
        {
            intros fb.
            specialize (a_least [b|fb]).
            unfold S' in a_least; cbn in a_least.
            rewrite (proof_irrelevance _ b_in) in a_least.
            specialize (a_least Sb).
            apply (F_f_lem f); assumption.
        }
        classic_case (wo_domain f b) as [fb|fb]; [>exact (lem fb)|].
        pose proof b_in as [B [[g [Fg B_eq]] Bb]]; subst B.
        specialize (F_chain f g Ff Fg) as [leq|leq].
        -   destruct leq as [sub [ext bigger]].
            specialize (bigger _ _ fa fb).
            clear Sa.
            apply sub in fa.
            apply (F_f_lem g); assumption.
        -   apply leq in Bb.
            exact (lem Bb).
    }
    assert (∀ a b, ¬F_domain a → F_f a b ∧ F_f b a) as F_f_top.
    {
        intros a b Fa.
        unfold F_f.
        destruct (sem _) as [f_ex|f_nex]; cbn.
        1: {
            exfalso; apply Fa.
            destruct f_ex as [f [Ff [fa fb]]].
            exists (wo_domain f).
            split; [>|apply fa].
            exists f.
            split; trivial.
        }
        destruct (sem _) as [g_ex|g_nex]; cbn.
        1: {
            exfalso; apply Fa.
            destruct g_ex as [f [Ff [fb fa]]].
            exists (wo_domain f).
            split; [>|apply fa].
            exists f.
            split; trivial.
        }
        split; exact true.
    }
    exists (make_wo_func F_domain F_f F_f_antisym F_f_wo F_f_top).
    intros g Fg.
    split; [>|split]; cbn.
    -   intros a a_in.
        exists (wo_domain g).
        split; [>|exact a_in].
        exists g.
        split; trivial.
    -   intros a b ga gb ab.
        apply (F_f_lem g); assumption.
    -   intros a b ga gb.
        unfold F_f.
        destruct (sem _) as [h_ex|h_nex]; [>|exact true].
        rewrite_ex_val h [Fh [ha hb]]; clear h_ex.
        specialize (F_chain g h Fg Fh) as [gh|hg].
        +   destruct gh as [sub [ext bigger]].
            apply bigger; assumption.
        +   apply hg in hb.
            contradiction.
Qed.

Definition wo := ex_val wo_ex.

Lemma wo_all : ∀ x, wo_domain wo x.
Proof.
    intros x.
    classic_contradiction contr.
    pose (X_domain := wo_domain wo ∪ ❴x❵).
    pose (X_f a b :=
        If (wo_domain wo a)
        then If (wo_domain wo b)
             then wo_f wo a b
             else True
        else If (wo_domain wo b)
             then x ≠ a
             else True
    ).
    assert (Antisymmetric (λ x y : set_type X_domain, X_f [x|] [y|]))
        as X_anti.
    {
        split.
        intros a b ab ba.
        unfold X_f in ab, ba.
        destruct a as [a [wa|ax]]; destruct b as [b [wb|bx]]; cbn in *.
        all: rewrite set_type_eq2.
        all: case_if; case_if; try contradiction.
        -   exact (wo_f_anti wa wb ab ba).
        -   rewrite singleton_eq in bx; subst b.
            contradiction.
        -   rewrite singleton_eq in ax; subst a.
            contradiction.
        -   rewrite singleton_eq in bx; subst b.
            contradiction.
        -   rewrite singleton_eq in ax, bx.
            rewrite <- ax, <- bx.
            reflexivity.
    }
    assert (WellOrdered (λ x y : set_type X_domain, X_f [x|] [y|])) as X_wo.
    {
        split.
        intros S S_ex.
        pose proof (wo_f_wo wo) as wo_wo.
        classic_case (∃ y, S y ∧ wo_domain wo [y|]) as [y_ex|y_nex].
        -   destruct y_ex as [[y Xy] [Sy y_in]].
            pose proof (union_lsub (wo_domain wo) ❴x❵) as sub.
            pose (S' a := S [[a|] | sub [a|] [|a]]).
            pose proof (well_ordered S') as a_ex.
            prove_parts a_ex.
            {
                exists [y|y_in].
                unfold S'; cbn.
                applys_eq Sy.
                apply set_type_eq2; reflexivity.
            }
            destruct a_ex as [[a wa] [S'a a_min]].
            exists [a | sub a wa].
            split; [>exact S'a|].
            clear y y_in Xy Sy.
            intros [y y_in] Sy; cbn in *.
            unfold X_f.
            case_if; case_if; try contradiction.
            2: exact true.
            apply (a_min [y|w0]).
            unfold S'; cbn.
            applys_eq Sy.
            apply set_type_eq2; reflexivity.
        -   assert (∀ a, S a → [a|] = x) as x_eq.
            {
                intros a Sa.
                rewrite not_ex in y_nex.
                specialize (y_nex a).
                rewrite not_and_impl in y_nex.
                apply y_nex in Sa.
                destruct a as [a [a_in|ax]]; [>contradiction|].
                cbn in *.
                symmetry; exact ax.
            }
            destruct S_ex as [a Sa].
            exists a.
            split; [>exact Sa|].
            intros y Sy.
            rewrite (x_eq _ Sa).
            rewrite (x_eq _ Sy).
            unfold X_f.
            case_if; [>contradiction|].
            exact true.
    }
    assert (∀ a b, ¬X_domain a → X_f a b ∧ X_f b a) as X_top.
    {
        intros a b a_in.
        unfold X_f.
        unfold X_domain, union in a_in.
        rewrite not_or in a_in.
        destruct a_in as [a_nin a_neq].
        case_if; case_if; try contradiction.
        -   split; [>exact a_neq|exact true].
        -   split; exact true.
    }
    pose (X := make_wo_func X_domain X_f X_anti X_wo X_top).
    pose proof (ex_proof wo_ex) as ltq.
    cbn in ltq.
    change (ex_type_val (ex_to_type wo_ex)) with wo in ltq.
    specialize (ltq X).
    apply ltq.
    split.
    -   split; [>|split].
        +   apply union_lsub.
        +   intros a b wa wb ab.
            cbn.
            unfold X_f.
            case_if; case_if.
            2, 3, 4: contradiction.
            exact ab.
        +   intros a b a_in b_nin.
            cbn.
            unfold X_f.
            case_if; case_if.
            1, 3, 4: contradiction.
            exact true.
    -   intros eq'.
        apply contr.
        rewrite eq'.
        right.
        reflexivity.
Qed.

Local Instance wo_le : Order U := {
    le a b := wo_f wo a b
}.

Local Instance wo_antisym : Antisymmetric le.
Proof.
    split.
    intros a b ab ba.
    pose proof (wo_f_antisym wo) as wo_anti.
    change a with [[a|wo_all a]|] in ab, ba.
    change b with [[b|wo_all b]|] in ab, ba.
    pose proof (antisym (Antisymmetric := wo_anti) ab ba) as eq.
    rewrite set_type_eq2 in eq.
    exact eq.
Qed.

Local Instance wo_wo : WellOrdered le.
Proof.
    split.
    intros S [x Sx].
    pose proof (wo_f_wo wo) as wo_wo.
    pose proof (well_ordered (λ x, S [x|]) (ex_intro _ [x|wo_all x] Sx))
        as [[a a_in] [Sa a_least]].
    exists a.
    split; [>exact Sa|].
    intros y Sy.
    specialize (a_least [y|wo_all y] Sy).
    exact a_least.
Qed.

End WellOrder.
