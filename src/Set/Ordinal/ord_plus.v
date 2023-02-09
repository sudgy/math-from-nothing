Require Import init.

Require Export ord_order.
Require Import set.
Require Import function.
Require Export plus_group.
Require Import nat.

Definition ord_plus_le (A B : ord_type) (a b : ord_U A + ord_U B) :=
    match a, b with
    | inl a', inl b' => ord_le A a' b'
    | inl a', inr b' => True
    | inr a', inl b' => False
    | inr a', inr b' => ord_le B a' b'
    end.

Lemma ord_plus_antisym : ∀ A B, Antisymmetric (ord_plus_le A B).
Proof.
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    split.
    intros [x|x] [y|y] xy yx; cbn in *.
    -   apply f_equal.
        exact (antisym xy yx).
    -   contradiction.
    -   contradiction.
    -   apply f_equal.
        exact (antisym xy yx).
Qed.

Lemma ord_plus_wo : ∀ A B, WellOrdered (ord_plus_le A B).
Proof.
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    split.
    assert (∀ S, (∃ x, S (inl x)) → ∃ x, is_least (ord_plus_le A B) S x)
        as lemma.
    {
        intros S [x Sx].
        pose (S' x := (S (inl x))).
        pose proof (well_ordered S' (ex_intro _ _ Sx)) as [a [S'a a_min]].
        exists (inl a).
        split; try exact S'a.
        intros [y|y] Sy; cbn in *; [>|exact true].
        apply (a_min y); assumption.
    }
    intros S [[x|x] Sx]; try (apply lemma; exists x; exact Sx).
    classic_case (∃ x, S (inl x)) as [A_ex|A_nex].
    -   apply lemma.
        exact A_ex.
    -   pose (S' x := (S (inr x))).
        pose proof (well_ordered S' (ex_intro _ _ Sx)) as [a [S'a a_min]].
        exists (inr a).
        split; try exact S'a.
        intros [y|y] Sy; cbn in *.
        +   rewrite not_ex in A_nex.
            specialize (A_nex y).
            contradiction.
        +   apply (a_min y); assumption.
Qed.

Notation "A ⊕ B" :=
    (make_ord_type (ord_U A + ord_U B) (ord_plus_le A B)
    (ord_plus_antisym A B) (ord_plus_wo A B))
    : ord_scope.

(* begin hide *)
Section OrdPlus.

Local Open Scope ord_scope.

Lemma ord_plus_wd : ∀ A B C D, A ~ B → C ~ D → A ⊕ C ~ B ⊕ D.
Proof.
    intros A B C D [f [f_bij f_iso]] [g [g_bij g_iso]].
    pose (h x := match x with
                 | inl a => inl (f a)
                 | inr b => inr (g b)
                 end).
    exists h.
    split.
    1: split; split.
    -   intros [x|x] [y|y] eq; unfold h in eq.
        all: inversion eq as [eq2].
        +   apply f_bij in eq2.
            rewrite eq2; reflexivity.
        +   apply g_bij in eq2.
            rewrite eq2; reflexivity.
    -   intros [y|y].
        +   pose proof (sur f y) as [x x_eq].
            exists (inl x).
            unfold h.
            rewrite x_eq; reflexivity.
        +   pose proof (sur g y) as [x x_eq].
            exists (inr x).
            unfold h.
            rewrite x_eq; reflexivity.
    -   intros [x|x] [y|y]; unfold h; cbn; try reflexivity.
        +   apply f_iso.
        +   apply g_iso.
Qed.

End OrdPlus.

Open Scope ord_scope.

Global Instance ord_plus_class : Plus ord := {
    plus := binary_op (binary_self_wd ord_plus_wd)
}.

Lemma ord_plus_assoc : ∀ α β γ, α + (β + γ) = (α + β) + γ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    exists (λ (x : ord_U A + (ord_U B + ord_U C)),
        match x with
        | inl a => inl (inl a)
        | inr x' => match x' with
                    | inl b => inl (inr b)
                    | inr c => inr c
                    end
        end).
    split.
    1: split; split.
    -   intros [x|[x|x]] [y|[y|y]] eq.
        all: inversion eq as [eq2].
        all: reflexivity.
    -   intros [[y|y]|y].
        +   exists (inl y).
            reflexivity.
        +   exists (inr (inl y)).
            reflexivity.
        +   exists (inr (inr y)).
            reflexivity.
    -   intros [x|[x|x]] [y|[y|y]]; cbn.
        all: reflexivity.
Qed.
Global Instance ord_plus_assoc_class : PlusAssoc ord := {
    plus_assoc := ord_plus_assoc
}.

Global Instance ord_zero : Zero ord := {
    zero := nat_to_ord 0
}.

Lemma ord_plus_lid : ∀ α, 0 + α = α.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold plus, zero; cbn.
    unfold nat_to_ord; equiv_simpl.
    exists (λ x, inr x).
    split.
    1: split; split.
    -   intros x y eq.
        inversion eq.
        reflexivity.
    -   intros [[x x_lt]|x].
        +   exfalso.
            rewrite <- nle_lt in x_lt.
            apply x_lt.
            apply nat_pos.
        +   exists x; reflexivity.
    -   intros a b.
        reflexivity.
Qed.
Global Instance ord_plus_lid_class : PlusLid ord := {
    plus_lid := ord_plus_lid
}.

Lemma ord_plus_rid : ∀ α, α + 0 = α.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold plus, zero; cbn.
    unfold nat_to_ord; equiv_simpl.
    exists (λ x, inl x).
    split.
    1: split; split.
    -   intros x y eq.
        inversion eq.
        reflexivity.
    -   intros [x|[x x_lt]].
        +   exists x; reflexivity.
        +   exfalso.
            rewrite <- nle_lt in x_lt.
            apply x_lt.
            apply nat_pos.
    -   intros a b.
        reflexivity.
Qed.
Global Instance ord_plus_rid_class : PlusRid ord := {
    plus_rid := ord_plus_rid
}.
(* end hide *)

Theorem ord_lt_lplus : ∀ {α β} γ, α < β → γ + α < γ + β.
Proof.
    intros A B C AB.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    rewrite ord_lt_initial in *.
    destruct AB as [x [f [f_bij f_iso]]].
    exists (inr x).
    pose (g (x : ord_U (C ⊕ A)) := match x with
                 | inl c => inl c
                 | inr a => inr [f a|]
                 end).
    assert (∀ y, initial_segment_set (C ⊕ B) (inr x) (g y)) as all_in.
    {
        intros [y|y]; unfold initial_segment_set; cbn.
        -   split; try exact true.
            intros contr; inversion contr.
        -   pose proof [|f y] as [leq neq].
            split; try exact leq.
            intro contr; inversion contr; contradiction.
    }
    exists (λ x, [_|all_in x]).
    split.
    1: split; split.
    -   intros [a|a] [b|b] eq; cbn in *.
        all: inversion eq as [eq2].
        +   reflexivity.
        +   apply set_type_eq in eq2.
            apply f_bij in eq2.
            rewrite eq2; reflexivity.
    -   intros [[b|b] b_lt].
        +   exists (inl b).
            unfold g.
            apply set_type_eq; reflexivity.
        +   assert (initial_segment_set B x b) as b_lt2.
            {
                unfold initial_segment_set in *; cbn in *.
                destruct b_lt as [b_le b_neq].
                split; try assumption.
                intro contr; subst; contradiction.
            }
            pose proof (sur f [_|b_lt2]) as [a a_eq].
            exists (inr a).
            unfold g; cbn.
            apply set_type_eq; cbn.
            rewrite a_eq.
            reflexivity.
    -   intros [a|a] [b|b]; cbn.
        all: try reflexivity.
        rewrite f_iso.
        reflexivity.
Qed.

Lemma ord_plus_lcancel : ∀ α β γ, γ + α = γ + β → α = β.
Proof.
    intros α β γ eq.
    destruct (trichotomy α β) as [[leq|H]|leq]; try assumption.
    exfalso.
    apply ord_lt_lplus with γ in leq.
    destruct leq; contradiction.
    symmetry in eq.
    apply ord_lt_lplus with γ in leq.
    destruct leq; contradiction.
Qed.
(* begin hide *)
Global Instance ord_plus_lcancel_class : PlusLcancel ord := {
    plus_lcancel := ord_plus_lcancel
}.
(* end hide *)

Theorem ord_lt_ex : ∀ α β, α < β → ∃ γ, 0 ≠ γ ∧ α + γ = β.
Proof.
    intros A B AB.
    equiv_get_value A B.
    get_ord_wo B.
    rewrite ord_lt_initial in AB.
    destruct AB as [x ABx].
    pose (C_set y := ord_le B x y).
    pose (C_le (a b : set_type C_set) := ord_le B [a|] [b|]).
    assert (Antisymmetric C_le) as C_antisym.
    {
        split; unfold C_le.
        intros a b ab ba.
        pose proof (antisym ab ba).
        apply set_type_eq; assumption.
    }
    assert (WellOrdered C_le) as C_wo.
    {
        split; unfold C_le.
        intros S S_ex.
        pose (S' x := ∃ y, S y ∧ [y|] = x).
        assert (∃ x, S' x) as S'_nempty.
        {
            destruct S_ex as [a Sa].
            exists [a|].
            exists a.
            split; try exact Sa; reflexivity.
        }
        pose proof (well_ordered S' S'_nempty) as [a [S'a a_min]].
        destruct S'a as [a' [Sa' a'_eq]].
        exists a'.
        split; try assumption.
        intros y Sy.
        specialize (a_min [y|]).
        prove_parts a_min.
        {
            exists y.
            split; try exact Sy; reflexivity.
        }
        rewrite a'_eq.
        exact a_min.
    }
    pose (C := make_ord_type _ _ C_antisym C_wo).
    exists (to_equiv ord_equiv C).
    split.
    -   intro contr.
        unfold zero in contr; cbn in contr; unfold nat_to_ord in contr.
        equiv_simpl in contr.
        destruct contr as [f [[C0 f_sur] C1]]; clear C0 C1.
        assert (C_set x) as Cx.
        {
            destruct (connex x x); assumption.
        }
        pose proof (sur f [_|Cx]) as [[y y_lt] C0]; clear C0.
        apply nat_neg2 in y_lt.
        exact y_lt.
    -   unfold plus; equiv_simpl.
        destruct ABx as [f [f_bij f_iso]].
        cbn in *.
        unfold initial_segment_set, initial_segment_le in *.
        exists (λ y, match y with
                     | inl a => [f a|]
                     | inr c => [c|]
                     end).
        split.
        split; split.
        +   intros [a|a] [b|b] eq.
            *   apply set_type_eq in eq.
                apply f_bij in eq.
                rewrite eq; reflexivity.
            *   destruct (f a) as [fa fa_lt]; cbn in *.
                destruct b as [b b_lt]; cbn in *.
                unfold C_set in b_lt.
                subst fa.
                destruct fa_lt as [b_le b_neq].
                pose proof (antisym b_le b_lt).
                contradiction.
            *   destruct a as [a a_lt].
                destruct (f b) as [fb fb_lt]; cbn in *.
                subst fb.
                destruct fb_lt as [a_le a_neq].
                pose proof (antisym a_le a_lt).
                contradiction.
            *   apply set_type_eq in eq.
                rewrite eq; reflexivity.
        +   intros b.
            classic_case (ord_le B x b) as [b_le|b_le].
            *   exists (inr [b|b_le]).
                reflexivity.
            *   destruct (connex x b) as [xb|xb]; try contradiction.
                assert (b ≠ x) as b_neq by (intro; subst b; contradiction).
                specialize (sur f [b|make_and xb b_neq]) as [a a_eq].
                exists (inl a).
                rewrite a_eq.
                reflexivity.
        +   intros [a|a] [b|b].
            *   apply f_iso.
            *   unfold C; cbn.
                split; try trivial.
                intro C0; clear C0.
                destruct (f a) as [fa fa_lt].
                destruct b as [b b_lt]; cbn.
                exact (trans (land fa_lt) b_lt).
            *   unfold C; cbn.
                split; try contradiction.
                intros leq.
                destruct a as [a a_lt].
                destruct (f b) as [fb fb_lt]; cbn in leq.
                pose proof (trans a_lt leq) as leq2.
                pose proof (antisym (land fb_lt) leq2).
                destruct fb_lt; contradiction.
            *   unfold C; cbn.
                unfold C_le.
                reflexivity.
Qed.
Theorem ord_le_ex : ∀ α β, α ≤ β → ∃ γ, α + γ = β.
Proof.
    intros α β leq.
    classic_case (α = β) as [eq|neq].
    -   subst.
        exists 0.
        apply plus_rid.
    -   pose proof (ord_lt_ex _ _ (make_and leq neq)) as [γ γ_eq].
        exists γ.
        apply γ_eq.
Qed.

Theorem ord_lt_zero : ∀ α, 0 ≠ α → 0 < α.
Proof.
    intros A A_nz.
    equiv_get_value A.
    unfold zero; cbn.
    unfold nat_to_ord.
    rewrite ord_lt_initial.
    assert (∀ m : nat, m < 0 → False) as no_m.
    {
        intros m mlt.
        rewrite <- nle_lt in mlt.
        apply mlt.
        apply nat_pos.
    }
    assert (∃ x, @all (ord_U A) x) as ex.
    {
        classic_contradiction contr.
        rewrite not_ex in contr.
        unfold all in contr.
        apply A_nz; clear A_nz.
        unfold zero; cbn.
        unfold nat_to_ord.
        equiv_simpl.
        exists (λ x, False_rect _ (no_m [x|] [|x])).
        split.
        split; split.
        -   intros a b eq.
            contradiction (no_m [a|] [|a]).
        -   intros y.
            exfalso.
            apply (contr y).
            exact true.
        -   intros a b.
            contradiction (no_m [a|] [|a]).
    }
    get_ord_wo A.
    pose proof (well_ordered _ ex) as [x [Sx x_min]]; clear Sx.
    exists x.
    exists (λ x, False_rect _ (no_m [x|] [|x])).
    split.
    split; split.
    -   intros a b.
        contradiction (no_m [a|] [|a]).
    -   intros [y [y_le y_neq]].
        specialize (x_min y true).
        pose proof (antisym y_le x_min).
        contradiction.
    -   intros a b.
        contradiction (no_m [a|] [|a]).
Qed.

Theorem ord_le_zero : ∀ α, 0 ≤ α.
Proof.
    intros α.
    classic_case (0 = α) as [eq|neq].
    -   rewrite eq.
        apply refl.
    -   apply ord_lt_zero.
        exact neq.
Qed.

Theorem ord_lt_plus_lcancel : ∀ {α β} γ, γ + α < γ + β → α < β.
Proof.
    intros α β γ leq.
    apply ord_lt_ex in leq as [δ [δ_nz eq]].
    rewrite <- plus_assoc in eq.
    apply plus_lcancel in eq; clear γ.
    rewrite <- eq; clear β eq.
    rewrite <- plus_rid at 1.
    apply ord_lt_lplus.
    apply ord_lt_zero.
    exact δ_nz.
Qed.

Lemma ord_le_lplus : ∀ α β γ, α ≤ β → γ + α ≤ γ + β.
Proof.
    intros α β γ leq.
    classic_case (α = β) as [eq|neq].
    -   subst.
        apply refl.
    -   pose proof (make_and leq neq) as ltq.
        apply ord_lt_lplus with γ in ltq.
        apply ltq.
Qed.
(* begin hide *)
Global Instance ord_le_lplus_class : OrderLplus ord := {
    le_lplus := ord_le_lplus
}.
(* end hide *)
Lemma ord_le_plus_lcancel : ∀ α β γ, γ + α ≤ γ + β → α ≤ β.
Proof.
    intros α β γ leq.
    classic_case (γ + α = γ + β) as [eq|neq].
    -   apply plus_lcancel in eq.
        subst.
        apply refl.
    -   pose proof (make_and leq neq) as ltq.
        apply ord_lt_plus_lcancel in ltq.
        apply ltq.
Qed.
(* begin hide *)
Global Instance ord_le_plus_lcancel_class : OrderPlusLcancel ord := {
    le_plus_lcancel := ord_le_plus_lcancel
}.
(* end hide *)

Theorem ord_le_self_rplus : ∀ α β, α ≤ α + β.
Proof.
    intros α β.
    rewrite <- plus_rid at 1.
    apply le_lplus.
    apply ord_le_zero.
Qed.

Theorem ord_le_self_lplus : ∀ α β, α ≤ β + α.
Proof.
    intros α β.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    rename α into A.
    rename β into B.
    equiv_get_value A B.
    unfold plus in ltq; equiv_simpl in ltq.
    rewrite ord_lt_initial in ltq.
    destruct ltq as [x [f [f_bij f_iso]]].
    pose (f' a := [f (inr a)|]).
    assert (Injective f') as f'_inj.
    {
        split.
        intros a b eq.
        apply set_type_eq in eq.
        apply f_bij in eq.
        inversion eq.
        reflexivity.
    }
    assert (∀ a b, ord_le A a b ↔ ord_le A (f' a) (f' b)) as f'_iso.
    {
        intros a b.
        specialize (f_iso (inr a) (inr b)).
        exact f_iso.
    }
    pose proof (ord_iso_le A f' f'_inj f'_iso x) as leq.
    unfold f' in leq.
    destruct [|f (inr x)] as [fx_leq fx_neq].
    get_ord_wo A.
    pose proof (antisym fx_leq leq).
    contradiction.
Qed.

Theorem ord_lt_rplus : ∀ {α β} γ, α < β → α + γ ≤ β + γ.
Proof.
    intros α β γ eq.
    apply ord_lt_ex in eq as [δ [δ_nz δ_eq]].
    rewrite <- δ_eq.
    rewrite <- plus_assoc.
    apply le_lplus.
    apply ord_le_self_lplus.
Qed.
Theorem ord_lt_plus_rcancel : ∀ {α β} γ, α + γ < β + γ → α < β.
Proof.
    intros α β γ eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    classic_case (β = α) as [eq2|neq].
    -   subst.
        destruct eq; contradiction.
    -   pose proof (make_and contr neq) as ltq.
        apply ord_lt_rplus with γ in ltq.
        pose proof (lt_le_trans eq ltq).
        destruct H; contradiction.
Qed.

Lemma ord_le_rplus : ∀ α β γ, α ≤ β → α + γ ≤ β + γ.
Proof.
    intros α β γ leq.
    classic_case (α = β) as [eq|neq].
    -   subst.
        apply refl.
    -   apply ord_lt_rplus.
        split; assumption.
Qed.
(* begin hide *)
Global Instance ord_le_rplus_class : OrderRplus ord := {
    le_rplus := ord_le_rplus
}.
(* end hide *)

Theorem nat_to_ord_plus : ∀ a b,
    nat_to_ord a + nat_to_ord b = nat_to_ord (a + b).
Proof.
    intros a b.
    unfold nat_to_ord, plus at 1; equiv_simpl.
    pose (dom := sum (set_type (λ m, m < a)) (set_type (λ m, m < b))).
    fold dom.
    pose (f (x : dom) := match x with
                         | inl a' => [a'|]
                         | inr b' => a + [b'|]
                         end).
    assert (∀ x, f x < a + b) as f_in.
    {
        intros [[x x_lt]|[x x_lt]]; unfold f; cbn.
        -   pose proof (nat_pos b) as eq.
            apply le_lplus with a in eq.
            rewrite plus_rid in eq.
            exact (lt_le_trans x_lt eq).
        -   apply lt_lplus.
            exact x_lt.
    }
    exists (λ x, [f x|f_in x]).
    split.
    split; split.
    -   intros [m|m] [n|n] eq.
        all: inversion eq as [eq2]; clear eq.
        +   apply set_type_eq in eq2.
            rewrite eq2; reflexivity.
        +   exfalso.
            destruct m as [m m_eq].
            cbn in eq2.
            rewrite eq2 in m_eq.
            rewrite <- (plus_rid a) in m_eq at 2.
            apply lt_plus_lcancel in m_eq.
            exact (nat_neg2 m_eq).
        +   exfalso.
            destruct n as [n n_eq].
            cbn in eq2.
            rewrite <- eq2 in n_eq.
            rewrite <- (plus_rid a) in n_eq at 2.
            apply lt_plus_lcancel in n_eq.
            exact (nat_neg2 n_eq).
        +   apply plus_lcancel in eq2.
            apply set_type_eq in eq2.
            rewrite eq2; reflexivity.
    -   intros [n n_eq].
        classic_case (n < a) as [n_lt|n_nlt].
        +   exists (inl [n|n_lt]).
            apply set_type_eq; cbn.
            reflexivity.
        +   rewrite nlt_le in n_nlt.
            apply nat_le_ex in n_nlt as [c c_eq].
            pose proof n_eq as c_lt.
            rewrite <- c_eq in c_lt.
            apply lt_plus_lcancel in c_lt.
            exists (inr [c|c_lt]).
            apply set_type_eq; cbn.
            exact c_eq.
    -   intros [[x x_lt]|[x x_lt]] [[y y_lt]|[y y_lt]].
        all: cbn.
        all: unfold le; cbn.
        +   reflexivity.
        +   split; try trivial.
            intros C0; clear C0.
            pose proof (nat_pos y) as eq.
            apply le_lplus with a in eq.
            rewrite plus_rid in eq.
            apply (lt_le_trans x_lt eq).
        +   split; try contradiction.
            intros eq.
            pose proof (le_lt_trans eq y_lt) as contr.
            rewrite <- (plus_rid a) in contr at 2.
            apply lt_plus_lcancel in contr.
            exact (nat_neg2 contr).
        +   split.
            *   apply le_lplus.
            *   apply le_plus_lcancel.
Qed.

Theorem ord_lt_self_rplus : ∀ α β, 0 ≠ β → α < α + β.
Proof.
    intros A B B_nz.
    equiv_get_value A B.
    assert (ord_U B) as b.
    {
        classic_contradiction contr.
        apply B_nz.
        symmetry.
        unfold zero; cbn.
        unfold nat_to_ord; equiv_simpl.
        exists (λ x, False_rect _ (contr x)).
        split.
        split; split.
        -   intros a; contradiction (contr a).
        -   intros [a a_lt].
            exfalso.
            apply nat_neg2 in a_lt.
            exact a_lt.
        -   intros a; contradiction (contr a).
    }
    clear B_nz.
    unfold plus; equiv_simpl.
    rewrite ord_lt_initial.
    get_ord_wo B.
    pose proof (well_ordered _ (ex_intro _ b true)) as [x [Sx x_min]]; clear Sx.
    clear b.
    exists (inr x).
    cbn.
    assert (∀ a, initial_segment_set (A ⊕ B) (inr x) (inl a)) as a_in.
    {
        intros a.
        split.
        -   exact true.
        -   intros contr; inversion contr.
    }
    exists (λ a, [_|a_in a]).
    split.
    split; split.
    -   intros a b eq.
        inversion eq.
        reflexivity.
    -   intros [[a|b] eq].
        +   exists a.
            apply set_type_eq; reflexivity.
        +   destruct eq.
            cbn in o.
            exfalso.
            specialize (x_min b true).
            rewrite (antisym o x_min) in n.
            contradiction.
    -   cbn.
        reflexivity.
Qed.

Theorem ord_false_0 : ∀ A, (ord_U A → False) → 0 = to_equiv ord_equiv A.
Proof.
    intros A A_false.
    symmetry.
    unfold zero; cbn.
    unfold nat_to_ord; equiv_simpl.
    exists (λ x, False_rect _ (A_false x)).
    split.
    1: split; split.
    -   intros a.
        contradiction (A_false a).
    -   intros x.
        contradiction (nat_lt_0_false x).
    -   intros a.
        contradiction (A_false a).
Qed.
(* begin hide *)
Close Scope ord_scope.
(* end hide *)
