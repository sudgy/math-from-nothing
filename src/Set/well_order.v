Require Import init.

Require Import zorn.
Require Import set.

Module WellOrderingTheorem.
Section WellOrder.

Context {U : Type}.

Record wo_func := make_wo_func {
    wo_domain : U → Prop;
    wo_f : U → U → Prop;
    wo_f_antisym : ∀ a b, wo_domain a → wo_domain b →
        wo_f a b → wo_f b a → a = b;
    wo_f_wo : well_orders wo_f wo_domain;
    wo_f_top : ∀ a b, ¬wo_domain a → wo_f a b ∧ wo_f b a;
}.

Lemma wo_f_connex : ∀ f a b, wo_domain f a → wo_domain f b →
    wo_f f a b ∨ wo_f f b a.
Proof.
    intros f a b.
    apply (well_orders_chain _ (wo_f_wo f)).
Qed.

Lemma wo_f_refl : ∀ f a, wo_f f a a.
Proof.
    intros f a.
    classic_case (wo_domain f a) as [fa|fa].
    -   destruct (wo_f_connex f a a fa fa); assumption.
    -   apply (wo_f_top f a a fa).
Qed.

Lemma wo_func_eq : ∀ f g : wo_func, wo_domain f = wo_domain g →
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
        apply functional_ext2.
        intros x y.
        classic_case (f_domain x) as [x_in|x_nin].
        1: classic_case (f_domain y) as [y_in|y_nin].
        -   exact (bottom x y x_in y_in).
        -   apply propositional_ext; split; intros H.
            +   apply (g_top y x y_nin).
            +   apply (f_top y x y_nin).
        -   apply propositional_ext; split; intros H.
            +   apply (g_top x y x_nin).
            +   apply (f_top x y x_nin).
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
        apply (wo_f_top f b a b_nin).
Qed.

Local Instance wo_func_order_antisym : Antisymmetric le.
Proof.
    split.
    intros f g [fg_sub [fg_ext fg_bigger]] [gf_sub [gf_ext gf_bigger]].
    apply wo_func_eq.
    -   exact (antisym fg_sub gf_sub).
    -   intros a b fa fb.
        apply propositional_ext; split.
        +   exact (fg_ext a b fa fb).
        +   apply fg_sub in fa, fb.
            exact (gf_ext a b fa fb).
Qed.

Local Instance wo_func_order_trans : Transitive le.
Proof.
    split.
    intros f g h [fg_sub [fg_ext fg_bigger]] [gh_sub [gh_ext gh_bigger]].
    split; [>|split].
    -   exact (trans fg_sub gh_sub).
    -   intros a b fa fb f_in.
        apply (gh_ext a b (fg_sub a fa) (fg_sub b fb)).
        exact (fg_ext a b fa fb f_in).
    -   intros a b a_in b_nin.
        pose proof (fg_bigger a b a_in b_nin) as ab.
        apply fg_sub in a_in.
        classic_case (wo_domain g b) as [gb|gb].
        +   exact (gh_ext a b a_in gb ab).
        +   exact (gh_bigger a b a_in gb).
Qed.

Section Chain.

Variable F : wo_func → Prop.
Hypothesis F_chain : is_chain le F.

Let F_domain := ⋃ image_under wo_domain F.
Let F_f a b := (∃ f, F f ∧ wo_domain f a ∧ wo_domain f b ∧ wo_f f a b) ∨
               ¬(∃ f, F f ∧ wo_domain f a ∧ wo_domain f b).

Lemma F_f_in : ∀ {f a}, F f → wo_domain f a → F_domain a.
Proof.
    intros f a Ff fa.
    exists (wo_domain f).
    split; [>|exact fa].
    exact (image_under_in Ff).
Qed.

Lemma F_f_part : ∀ f a b, wo_domain f a → wo_domain f b → F f →
    wo_f f a b → F_f a b.
Proof.
    intros f a b fa fb Ff ab.
    unfold F_f.
    left.
    exists f.
    repeat split; assumption.
Qed.

Lemma F_f_antisym : ∀ a b, F_domain a → F_domain b → F_f a b → F_f b a → a = b.
Proof.
    intros a b Fa Fb.
    unfold F_f.
    intros [f_ex|f_nex] [g_ex|g_nex].
    -   destruct f_ex as [f [Ff [fa [fb ab]]]].
        destruct g_ex as [g [Fg [gb [ga ba]]]].
        specialize (F_chain f g Ff Fg) as [leq|leq].
        all: destruct leq as [sub [ext bigger]].
        +   apply (ext a b fa fb) in ab.
            exact (wo_f_antisym _ _ _ ga gb ab ba).
        +   apply (ext b a gb ga) in ba.
            exact (wo_f_antisym _ _ _  fa fb ab ba).
    -   exfalso; apply g_nex.
        destruct f_ex as [f [Ff [fa [fb]]]].
        exists f.
        split; [>|split]; assumption.
    -   exfalso; apply f_nex.
        destruct g_ex as [g [Fg [ga [gb]]]].
        exists g.
        split; [>|split]; assumption.
    -   exfalso; apply f_nex.
        destruct Fa as [A [[f [Ff A_eq]] Aa]]; subst A.
        destruct Fb as [B [[g [Fg B_eq]] Bb]]; subst B.
        specialize (F_chain f g Ff Fg) as [leq|leq].
        all: destruct leq as [sub [ext bigger]].
        +   apply sub in Aa.
            exists g.
            split; [>|split]; assumption.
        +   apply sub in Bb.
            exists f.
            split; [>|split]; assumption.
Qed.

Lemma F_f_wo : well_orders F_f F_domain.
Proof.
    intros S S_sub [x Sx].
    pose proof (S_sub x Sx) as [A [[f [Ff A_eq]] Ax]]; subst A.
    pose proof (wo_f_wo f _ (inter_rsub _ _) (ex_intro _ _ (make_and Sx Ax)))
        as [a [[Sa fa] a_least]].
    exists a.
    split; [>exact Sa|].
    intros b Sb.
    assert (wo_domain f b → F_f a b) as lem.
    {
        intros fb.
        specialize (a_least b (make_and Sb fb)).
        exact (F_f_part f a b fa fb Ff a_least).
    }
    classic_case (wo_domain f b) as [fb|fb]; [>exact (lem fb)|].
    pose proof (S_sub b Sb) as [B [[g [Fg B_eq]] Bb]]; subst B.
    pose proof (F_chain f g Ff Fg) as [leq|leq].
    all: destruct leq as [sub [ext bigger]].
    -   specialize (bigger _ _ fa fb).
        apply sub in fa.
        exact (F_f_part g a b fa Bb Fg bigger).
    -   exact (lem (sub _ Bb)).
Qed.

Lemma F_f_top : ∀ a b, ¬F_domain a → F_f a b ∧ F_f b a.
    intros a b Fa.
    unfold F_f.
    assert (∀ f, F f → wo_domain f a → False) as wlog.
    {
        intros f Ff fa.
        apply Fa.
        exact (F_f_in Ff fa).
    }
    split.
    -   right.
        intros [f [Ff [fa fb]]].
        exact (wlog f Ff fa).
    -   right.
        intros [f [Ff [fb fa]]].
        exact (wlog f Ff fa).
Qed.

Lemma F_upper : has_upper_bound le F.
Proof.
    exists (make_wo_func F_domain F_f F_f_antisym F_f_wo F_f_top).
    intros g Fg.
    split; [>|split]; cbn.
    -   intros a.
        exact (F_f_in Fg).
    -   intros a b ga gb ab.
        apply (F_f_part g); assumption.
    -   intros a b ga gb.
        unfold F_f.
        apply or_left.
        rewrite not_not.
        intros [h [Fh [ha hb]]].
        specialize (F_chain g h Fg Fh) as [leq|leq].
        all: destruct leq as [sub [ext bigger]].
        +   exists h.
            specialize (bigger a b ga gb).
            repeat split; assumption.
        +   apply sub in hb.
            contradiction (gb hb).
Qed.

End Chain.

Definition wo := ex_val (zorn le F_upper).
Definition wo_max := ex_proof (zorn le F_upper) : ∀ X, ¬wo < X.

Section All.

Variable x : U.
Hypothesis contr : ¬wo_domain wo x.

Let X_domain := wo_domain wo ∪ ❴x❵.
Let X_f a b :=
    If (wo_domain wo a)
    then If (wo_domain wo b)
         then wo_f wo a b
         else True
    else If (wo_domain wo b)
         then x ≠ a
         else True.

Lemma X_anti : ∀ a b, X_domain a → X_domain b → X_f a b → X_f b a → a = b.
Proof.
    intros a b a_in b_in ab ba.
    unfold X_f in ab, ba.
    destruct a_in as [wa|ax]; destruct b_in as [wb|bx].
    all: case_if; case_if; try contradiction.
    -   exact (wo_f_antisym wo a b wa wb ab ba).
    -   rewrite singleton_eq in bx; subst b.
        contradiction.
    -   rewrite singleton_eq in ax; subst a.
        contradiction.
    -   rewrite singleton_eq in bx; subst b.
        contradiction.
    -   rewrite singleton_eq in ax, bx.
        rewrite <- ax, <- bx.
        reflexivity.
Qed.

Lemma X_wo : well_orders X_f X_domain.
Proof.
    intros S S_sub S_ex.
    classic_case (∃ y, S y ∧ wo_domain wo y) as [y_ex|y_nex].
    -   destruct y_ex as [y [Sy y_in]].
        pose proof (wo_f_wo wo _ (inter_rsub _ _)
            (ex_intro _ _ (make_and Sy y_in))) as [a [[Sa wa] a_min]].
        exists a.
        split; [>exact Sa|].
        intros b Sb.
        unfold X_f.
        case_if; [>|contradiction]; case_if.
        +   apply (a_min b).
            split; assumption.
        +   exact true.
    -   assert (∀ a, S a → a = x) as x_eq.
        {
            intros a Sa.
            rewrite not_ex in y_nex.
            specialize (y_nex a).
            rewrite not_and_impl in y_nex.
            specialize (y_nex Sa).
            apply S_sub in Sa as [a_in|ax]; [>contradiction|].
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
Qed.

Lemma X_top : ∀ a b, ¬X_domain a → X_f a b ∧ X_f b a.
Proof.
    intros a b a_in.
    unfold X_f.
    unfold X_domain, union in a_in.
    rewrite not_or in a_in.
    destruct a_in as [a_nin a_neq].
    case_if; [>contradiction|]; case_if.
    -   split; [>exact a_neq|exact true].
    -   split; exact true.
Qed.

Definition X := make_wo_func X_domain X_f X_anti X_wo X_top.

Lemma X_gt : wo < X.
Proof.
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

End All.

Lemma wo_all : ∀ x, wo_domain wo x.
Proof.
    intros x.
    classic_contradiction contr.
    exact (wo_max (X x contr) (X_gt x contr)).
Qed.

Local Instance wo_le : Order U := {
    le a b := wo_f wo a b
}.

Local Instance wo_antisym : Antisymmetric le.
Proof.
    split.
    intros a b ab ba.
    exact (wo_f_antisym wo a b (wo_all a) (wo_all b) ab ba).
Qed.

Local Instance wo_wo : WellOrdered le.
Proof.
    split.
    intros S S_ex.
    exact (wo_f_wo wo S (λ x _, wo_all x) S_ex).
Qed.

End WellOrder.
End WellOrderingTheorem.

Export WellOrderingTheorem (wo_le).
Export WellOrderingTheorem (wo_antisym).
Export WellOrderingTheorem (wo_wo).
