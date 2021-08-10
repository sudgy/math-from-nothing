Require Import init.

Require Export geometric_construction1.

Require Import list.
Require Import set.

Section GA2.

Local Open Scope ga_scope.

Context {V : Type}.
Variable metric : ga_metric V.
Let basis_t := (ga1 V).

Definition ga_equiv1 (b1 b2 : basis_t) :=
    ∃ (l1 l2 : list V) (e : V),
        snd b1 = l1 ++ e :: e :: l2 ∧
        snd b2 = l1 ++ l2 ∧
        fst b2 = ga_sign_mult (fst b1) (metric e).

Definition ga_equiv2 (b1 b2 : basis_t) :=
    ∃ (l1 l2 : list V) (e f : V),
        e ≠ f ∧
        snd b1 = l1 ++ e :: f :: l2 ∧
        snd b2 = l1 ++ f :: e :: l2 ∧
        fst b2 = ga_sign_mult (fst b1) ga_neg.

Definition ga_equiv3 b1 b2 :=
    b1 = b2 ∨
    ((ga_equiv1 b1 b2 ∨ ga_equiv1 b2 b1) ∨ (ga_equiv2 b1 b2 ∨ ga_equiv2 b2 b1)).

Definition ga_single_equiv (a : basis_t) (l : list basis_t) :=
    match l with
    | list_end => True
    | b :: _ => ga_equiv3 a b
    end.

Fixpoint ga_all_equiv (l : list basis_t) :=
    match l with
    | list_end => True
    | b :: c => ga_single_equiv b c ∧ ga_all_equiv c
    end.

Definition ga_equiv0 b1 b2 :=
    b1 = b2 ∨
    ∃ l : list basis_t,
        (∃ l1, b1 :: l1 = l) ∧
        (∃ l2, l2 ++ b2 :: list_end = l) ∧
        ga_all_equiv l.

Lemma all_equiv_conc : ∀ l1 b l2,
        ga_all_equiv l1 → ga_all_equiv (l1 ++ (b :: list_end)) →
        ga_all_equiv (b :: l2) → ga_all_equiv (l1 ++ (b :: l2)).
    intros l1 b l2 l1_equiv l1_equiv2 l2_equiv.
    induction l1.
    -   exact l2_equiv.
    -   split.
        +   destruct l1.
            *   cbn.
                cbn in l1_equiv2.
                apply l1_equiv2.
            *   cbn.
                cbn in l1_equiv.
                apply l1_equiv.
        +   apply IHl1.
            *   cbn in l1_equiv.
                apply l1_equiv.
            *   cbn in l1_equiv2.
                apply l1_equiv2.
Qed.

Lemma all_equiv_lconc : ∀ l1 l2, ga_all_equiv (l1 ++ l2) → ga_all_equiv l1.
    intros l1 l2 l_equiv.
    induction l1.
    -   cbn.
        exact true.
    -   cbn in *.
        destruct l_equiv as [a_equiv l_equiv].
        split.
        +   destruct l1.
            *   cbn.
                exact true.
            *   cbn in *.
                exact a_equiv.
        +   exact (IHl1 l_equiv).
Qed.

Local Notation "a ~ b" := (ga_equiv0 a b) : algebra_scope.
Local Open Scope algebra_scope.
Local Open Scope ga_scope.

Lemma ga_eq_reflexive : ∀ a, a ~ a.
    intros a.
    left.
    reflexivity.
Qed.
Instance ga_eq_reflexive_class : Reflexive _ := {
    refl := ga_eq_reflexive
}.

Lemma ga_eq_symmetric : ∀ a b, a ~ b → b ~ a.
    intros a b [ab|ab].
    1: left; symmetry; exact ab.
    destruct ab as [l [[l1 l1_eq] [[l2 l2_eq] l_equiv]]].
    right.
    exists (list_reverse l).
    repeat split.
    -   exists (list_reverse l2).
        rewrite <- l2_eq.
        rewrite list_reverse_conc.
        cbn.
        reflexivity.
    -   exists (list_reverse l1).
        rewrite <- l1_eq.
        cbn.
        reflexivity.
    -   clear l1 l1_eq l2 l2_eq.
        induction l; trivial.
        cbn.
        cbn in l_equiv.
        destruct l_equiv as [s_equiv l_equiv].
        specialize (IHl l_equiv).
        destruct l.
        +   cbn.
            split; exact true.
        +   cbn in s_equiv.
            cbn.
            rewrite <- list_conc_assoc.
            apply all_equiv_conc.
            *   cbn in IHl.
                apply all_equiv_lconc in IHl.
                exact IHl.
            *   cbn in IHl.
                exact IHl.
            *   cbn.
                repeat split; try exact true.
                destruct s_equiv as [eq|[[e|e]|[e|e]]].
                --  left; symmetry; exact eq.
                --  right; left; right; exact e.
                --  right; left; left; exact e.
                --  right; right; right; exact e.
                --  right; right; left; exact e.
Qed.
Instance ga_eq_symmetric_class : Symmetric _ := {
    sym := ga_eq_symmetric
}.

Lemma ga_eq_transitive : ∀ a b c, a ~ b → b ~ c → a ~ c.
    intros a b c ab bc.
    destruct ab as [ab|ab].
    1: subst; exact bc.
    destruct bc as [bc|bc].
    1: subst; right; exact ab.
    destruct ab as [abl [[abl1 abl1_eq] [[abl2 abl2_eq] abl_equiv]]].
    destruct bc as [bcl [[bcl1 bcl1_eq] [[bcl2 bcl2_eq] bcl_equiv]]].
    right.
    exists (abl ++ bcl).
    repeat split.
    -   exists (abl1 ++ bcl).
        rewrite <- abl1_eq.
        cbn.
        reflexivity.
    -   exists (abl ++ bcl2).
        rewrite <- bcl2_eq.
        rewrite list_conc_assoc.
        reflexivity.
    -   clear abl1 abl1_eq bcl2 bcl2_eq.
        rewrite <- bcl1_eq.
        apply all_equiv_conc; try assumption.
        2: rewrite bcl1_eq; exact bcl_equiv.
        rewrite <- abl2_eq.
        rewrite <- list_conc_assoc.
        apply all_equiv_conc.
        +   rewrite <- abl2_eq in abl_equiv.
            apply all_equiv_lconc in abl_equiv.
            exact abl_equiv.
        +   rewrite abl2_eq.
            exact abl_equiv.
        +   cbn.
            repeat split; try exact true.
            left.
            reflexivity.
Qed.
Instance ga_eq_transitive_class : Transitive _ := {
    trans := ga_eq_transitive
}.

Definition ga_equiv := make_equiv _
    ga_eq_reflexive_class ga_eq_symmetric_class ga_eq_transitive_class.
Notation "a ~ b" := (ga_equiv0 a b) : ga_scope.
Definition ga2 := (equiv_type ga_equiv).

Definition ga12 b := to_equiv_type ga_equiv b.

Lemma ga_all_equiv_wd_lmult : ∀ l a, ga_all_equiv l →
        ga_all_equiv (list_image l (ga1_mult a)).
    intros l a l_equiv.
    induction l; try exact true.
    cbn.
    destruct l_equiv as [a_equiv l_equiv].
    split; try exact (IHl l_equiv).
    clear IHl.
    destruct l; try exact true.
    cbn.
    cbn in a_equiv.
    destruct a_equiv as [eq|[[e|e]|[e|e]]].
    *   rewrite eq.
        left; reflexivity.
    *   right; left; left.
        destruct e as [l1 [l2 [e [eq1 [eq2 s_eq]]]]].
        exists (snd a ++ l1), l2.
        exists e.
        unfold ga1_mult; cbn.
        repeat split.
        --  rewrite eq1.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            rewrite ga_sign_mult_assoc.
            reflexivity.
    *   right; left; right.
        destruct e as [l1 [l2 [e [eq1 [eq2 s_eq]]]]].
        exists (snd a ++ l1), l2.
        unfold ga1_mult; cbn.
        exists e.
        repeat split.
        --  rewrite eq1.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            rewrite ga_sign_mult_assoc.
            reflexivity.
    *   right; right; left.
        destruct e as [l1 [l2 [e [f [e_neq [eq1 [eq2 s_eq]]]]]]].
        exists (snd a ++ l1), l2.
        exists e, f.
        unfold ga1_mult; cbn.
        repeat split.
        --  exact e_neq.
        --  rewrite eq1.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            rewrite ga_sign_mult_assoc.
            reflexivity.
    *   right; right; right.
        destruct e as [l1 [l2 [e [f [e_neq [eq1 [eq2 s_eq]]]]]]].
        exists (snd a ++ l1), l2.
        exists e, f.
        unfold ga1_mult; cbn.
        repeat split.
        --  exact e_neq.
        --  rewrite eq1.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            rewrite ga_sign_mult_assoc.
            reflexivity.
Qed.

Lemma ga_all_equiv_wd_rmult_single : ∀ a b c,
        ga_equiv3 a b → ga_equiv3 (ga1_mult a c) (ga1_mult b c).
    intros a b c equiv.
    destruct equiv as [eq|[[e|e]|[e|e]]].
    *   rewrite eq.
        left; reflexivity.
    *   right; left; left.
        destruct e as [l1 [l2 [e [eq1 [eq2 s_eq]]]]].
        exists l1, (l2 ++ snd c).
        exists e.
        unfold ga1_mult; cbn.
        repeat split.
        --  rewrite eq1.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            do 2 rewrite <- ga_sign_mult_assoc.
            rewrite (ga_sign_mult_comm (fst c)).
            reflexivity.
    *   right; left; right.
        destruct e as [l1 [l2 [e [eq1 [eq2 s_eq]]]]].
        exists l1, (l2 ++ snd c).
        unfold ga1_mult; cbn.
        exists e.
        repeat split.
        --  rewrite eq1.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            do 2 rewrite <- ga_sign_mult_assoc.
            rewrite (ga_sign_mult_comm (fst c)).
            reflexivity.
    *   right; right; left.
        destruct e as [l1 [l2 [e [f [e_neq [eq1 [eq2 s_eq]]]]]]].
        exists l1, (l2 ++ snd c).
        exists e, f.
        unfold ga1_mult; cbn.
        repeat split.
        --  exact e_neq.
        --  rewrite eq1.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            do 2 rewrite <- ga_sign_mult_assoc.
            rewrite (ga_sign_mult_comm (fst c)).
            reflexivity.
    *   right; right; right.
        destruct e as [l1 [l2 [e [f [e_neq [eq1 [eq2 s_eq]]]]]]].
        exists l1, (l2 ++ snd c).
        exists e, f.
        unfold ga1_mult; cbn.
        repeat split.
        --  exact e_neq.
        --  rewrite eq1.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite eq2.
            do 2 rewrite list_conc_add_assoc.
            rewrite list_conc_assoc.
            reflexivity.
        --  rewrite s_eq.
            do 2 rewrite <- ga_sign_mult_assoc.
            rewrite (ga_sign_mult_comm (fst c)).
            reflexivity.
Qed.

Lemma ga_all_equiv_wd_rmult : ∀ l a, ga_all_equiv l →
        ga_all_equiv (list_image l (λ x, ga1_mult x a)).
    intros l c l_equiv.
    induction l; try exact true.
    cbn.
    destruct l_equiv as [a_equiv l_equiv].
    split; try exact (IHl l_equiv).
    clear IHl.
    destruct l; try exact true.
    cbn.
    cbn in a_equiv.
    exact (ga_all_equiv_wd_rmult_single _ _ _ a_equiv).
Qed.

Lemma ga1_mult_wd1 :
        ∀ a b c, a ~ b → ga1_mult a c ~ ga1_mult b c.
    intros a b c ab.
    destruct ab as [ab|ab].
    1: subst; apply refl.
    destruct ab as [l [[l1 l1_eq] [[l2 l2_eq] l_equiv]]].
    right.
    pose (l' := list_image l (λ x, ga1_mult x c)).
    exists l'.
    repeat split.
    -   exists (list_image l1 (λ x, ga1_mult x c)).
        unfold l'.
        rewrite <- l1_eq.
        cbn.
        reflexivity.
    -   exists (list_image l2 (λ x, ga1_mult x c)).
        unfold l'.
        rewrite <- l2_eq.
        rewrite list_image_conc.
        cbn.
        reflexivity.
    -   unfold l'.
        exact (ga_all_equiv_wd_rmult _ _ l_equiv).
Qed.

Lemma ga1_mult_wd2 :
        ∀ a c d, c ~ d → ga1_mult a c ~ ga1_mult a d.
    intros a c d cd.
    destruct cd as [cd|cd].
    1: subst; apply refl.
    destruct cd as [l [[l1 l1_eq] [[l2 l2_eq] l_equiv]]].
    right.
    pose (l' := list_image l (ga1_mult a)).
    exists l'.
    repeat split.
    -   exists (list_image l1 (ga1_mult a)).
        unfold l'.
        rewrite <- l1_eq.
        cbn.
        reflexivity.
    -   exists (list_image l2 (ga1_mult a)).
        unfold l'.
        rewrite <- l2_eq.
        rewrite list_image_conc.
        cbn.
        reflexivity.
    -   exact (ga_all_equiv_wd_lmult _ _ l_equiv).
Qed.

Lemma ga1_mult_wd :
        ∀ a b c d, eq_equal ga_equiv a b → eq_equal ga_equiv c d →
        eq_equal ga_equiv (ga1_mult a c) (ga1_mult b d).
    intros a b c d ab cd.
    pose proof (ga1_mult_wd1 a b c ab) as eq1.
    pose proof (ga1_mult_wd2 b c d cd) as eq2.
    exact (trans eq1 eq2).
Qed.

Definition ga2_mult := binary_self_op ga1_mult_wd.

End GA2.
