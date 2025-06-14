Require Import init.

Require Export ord_order.
Require Import ord_plus.
Require Import set.
Require Import function.
Require Export mult_ring.
Require Import nat.

Definition ord_mult_le (A B : ord_type) (a b : ord_U A * ord_U B) :=
    match a, b with
    | (a1, b1), (a2, b2) =>
        (ord_le B b1 b2 ∧ b1 ≠ b2) ∨ (ord_le A a1 a2 ∧ b1 = b2)
    end.

Lemma ord_mult_antisym : ∀ A B, Antisymmetric (ord_mult_le A B).
Proof.
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    split.
    intros [a1 b1] [a2 b2]
           [[b_eq1 b_neq1]|[a_eq1 b_eq1]] [[b_eq2 b_neq2]|[a_eq2 b_eq2]].
    -   pose proof (antisym b_eq1 b_eq2).
        contradiction.
    -   symmetry in b_eq2.
        contradiction.
    -   symmetry in b_eq1.
        contradiction.
    -   apply f_equal2; try exact b_eq1.
        apply antisym; assumption.
Qed.

Lemma ord_mult_wo : ∀ A B, WellOrdered (ord_mult_le A B).
Proof.
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    split.
    intros S [[xa xb] Sx].
    pose (SB b := ∃ a, S (a, b)).
    assert (∃ x, SB x) as SB_nempty.
    {
        exists xb.
        exists xa.
        exact Sx.
    }
    pose proof (well_ordered SB SB_nempty) as [yb [SBy yb_min]].
    pose (SA a := S (a, yb)).
    assert (∃ x, SA x) as SA_nempty by exact SBy.
    pose proof (well_ordered SA SA_nempty) as [ya [SAy ya_min]].
    exists (ya, yb).
    split; try assumption.
    intros [a b] Sab.
    cbn.
    classic_case (yb = b) as [eq|neq].
    -   subst yb.
        right.
        split; [>|reflexivity].
        apply ya_min.
        unfold SA.
        exact Sab.
    -   left.
        split; [>|exact neq].
        apply yb_min.
        unfold SB.
        exists a.
        exact Sab.
Qed.

Notation "A ⊗ B" :=
    (make_ord_type (ord_U A * ord_U B) (ord_mult_le A B)
    (ord_mult_antisym A B) (ord_mult_wo A B))
    : ord_scope.

Section OrdMult.

Local Open Scope ord_scope.

Lemma ord_mult_wd : ∀ A B C D, A ~ B → C ~ D → A ⊗ C ~ B ⊗ D.
Proof.
    intros A B C D [f [f_bij f_iso]] [g [g_bij g_iso]].
    exists (λ x, (f (fst x), g (snd x))).
    split.
    split; split.
    -   intros [a1 c1] [a2 c2] eq.
        inversion eq as [eq1]; rename H into eq2.
        apply f_bij in eq1.
        apply g_bij in eq2.
        subst.
        reflexivity.
    -   intros [b d].
        pose proof (sur f b) as [a a_eq].
        pose proof (sur g d) as [c c_eq].
        exists (a, c); cbn.
        rewrite a_eq, c_eq.
        reflexivity.
    -   intros [a1 c1] [a2 c2]; cbn.
        rewrite f_iso.
        rewrite g_iso.
        assert ((c1 ≠ c2) = (g c1 ≠ g c2)) as eq1.
        {
            apply propositional_ext; split.
            -   intros neq eq.
                apply g_bij in eq.
                contradiction.
            -   intros neq eq.
                subst.
                contradiction.
        }
        assert ((c1 = c2) = (g c1 = g c2)) as eq2.
        {
            apply propositional_ext; split.
            -   intros eq.
                subst.
                reflexivity.
            -   intros eq.
                apply g_bij in eq.
                exact eq.
        }
        rewrite eq1, eq2.
        reflexivity.
Qed.

End OrdMult.

Open Scope ord_scope.

Global Instance ord_mult_class : Mult ord := {
    mult := binary_op (binary_self_wd ord_mult_wd)
}.

Lemma ord_ldist : ∀ α β γ, α * (β + γ) = α * β + α * γ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult; equiv_simpl.
    exists (λ x, match (snd x) with
                 | inl b => inl (fst x, b)
                 | inr c => inr (fst x, c)
                 end).
    split.
    split; split.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]] eq; cbn in *.
        all: inversion eq.
        all: reflexivity.
    -   intros [[a b]|[a c]].
        +   exists (a, inl b); cbn.
            reflexivity.
        +   exists (a, inr c); cbn.
            reflexivity.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]]; cbn.
        +   rewrite inl_neq.
            rewrite inl_eq2.
            reflexivity.
        +   split; try trivial.
            intros C0; clear C0.
            left.
            split; try trivial.
            intro eq; inversion eq.
        +   split; try contradiction.
            intros [[a b]|[c d]]; try contradiction.
            inversion d.
        +   rewrite inr_neq.
            rewrite inr_eq2.
            reflexivity.
Qed.
Global Instance ord_ldist_class : Ldist ord := {
    ldist := ord_ldist
}.

Lemma ord_mult_assoc : ∀ α β γ, α * (β * γ) = (α * β) * γ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult; equiv_simpl.
    exists (λ x, ((fst x, fst (snd x)), snd (snd x))).
    split.
    split; split.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] eq; cbn in *.
        inversion eq.
        reflexivity.
    -   intros [[a b] c].
        exists (a, (b, c)).
        cbn.
        reflexivity.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]].
        cbn.
        split.
        +   intros H.
            repeat destruct H.
            *   left; split; assumption.
            *   right; split; try assumption.
                left; split; try assumption.
                intro contr; subst; contradiction.
            *   inversion H0.
                right.
                split; try trivial.
                right; split; try assumption.
                reflexivity.
        +   intros H.
            repeat destruct H.
            *   left.
                split.
                --  left; split; assumption.
                --  intro contr; inversion contr; contradiction.
            *   left.
                split.
                --  right; split; assumption.
                --  intro contr; inversion contr; contradiction.
            *   right.
                split; try assumption.
                apply f_equal2; assumption.
Qed.
Global Instance ord_mult_assoc_class : MultAssoc ord := {
    mult_assoc := ord_mult_assoc
}.

Lemma ord_mult_lanni : ∀ α, 0 * α = 0.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold zero; cbn; unfold nat_to_ord, mult; equiv_simpl.
    assert (∀ m : set_type (λ m : nat, m < 0), False) as none.
    {
        intros [m m_lt].
        exact (nat_neg2 m_lt).
    }
    exists (λ x, False_rect _ (none x)).
    split.
    split; split.
    -   intros a.
        exfalso.
        apply none in a.
        contradiction.
    -   intros [a b].
        exfalso.
        apply none in a.
        contradiction.
    -   intros a.
        exfalso.
        apply none in a.
        contradiction.
Qed.
Global Instance ord_mult_lanni_class : MultLanni ord := {
    mult_lanni := ord_mult_lanni
}.

Lemma ord_mult_ranni : ∀ α, α * 0 = 0.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold zero; cbn; unfold nat_to_ord, mult; equiv_simpl.
    assert (∀ m : set_type (λ m : nat, m < 0), False) as none.
    {
        intros [m m_lt].
        exact (nat_neg2 m_lt).
    }
    exists (λ x, False_rect _ (none x)).
    split.
    split; split.
    -   intros a.
        exfalso.
        apply none in a.
        contradiction.
    -   intros [a b].
        exfalso.
        apply none in b.
        contradiction.
    -   intros a.
        exfalso.
        apply none in a.
        contradiction.
Qed.
Global Instance ord_mult_ranni_class : MultRanni ord := {
    mult_ranni := ord_mult_ranni
}.

Global Instance ord_one : One ord := {
    one := nat_to_ord 1
}.

Lemma ord_mult_lid : ∀ α, 1 * α = α.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold one; cbn; unfold nat_to_ord, mult; equiv_simpl.
    assert (zero (U := nat)  < 1) as z_lt.
    {
        split; try apply nat_pos.
        intro contr; inversion contr.
    }
    exists (λ x, ([0|z_lt], x)).
    split.
    split; split.
    -   intros a b eq.
        inversion eq.
        reflexivity.
    -   intros [a b].
        exists b.
        apply f_equal2; try reflexivity.
        destruct a as [a a_lt].
        apply set_type_eq; cbn.
        unfold one in a_lt; cbn in a_lt.
        rewrite nat_lt_suc_le in a_lt.
        apply nat_neg_eq.
        exact a_lt.
    -   intros a b.
        cbn.
        split.
        +   intros ab.
            classic_case (a = b) as [eq|neq].
            *   right.
                split; trivial.
                apply refl.
            *   left.
                split; assumption.
        +   intros [[c d]|[e f]].
            *   exact c.
            *   rewrite f.
                get_ord_wo A.
                destruct (connex b b); assumption.
Qed.
Global Instance ord_mult_lid_class : MultLid ord := {
    mult_lid := ord_mult_lid
}.

Lemma ord_mult_rid : ∀ α, α * 1 = α.
Proof.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold one; cbn; unfold nat_to_ord, mult; equiv_simpl.
    assert (zero (U := nat)  < 1) as z_lt.
    {
        split; try apply nat_pos.
        intro contr; inversion contr.
    }
    exists (λ x, (x, [0|z_lt])).
    split.
    split; split.
    -   intros a b eq.
        inversion eq.
        reflexivity.
    -   intros [a b].
        exists a.
        apply f_equal2; try reflexivity.
        destruct b as [b b_lt].
        apply set_type_eq; cbn.
        unfold one in b_lt; cbn in b_lt.
        rewrite nat_lt_suc_le in b_lt.
        apply nat_neg_eq.
        exact b_lt.
    -   intros a b.
        cbn.
        split.
        +   intros ab.
            classic_case (a = b) as [eq|neq].
            *   right.
                split; trivial.
            *   right.
                split; trivial.
        +   intros [[c d]|[e f]].
            *   contradiction.
            *   exact e.
Qed.
Global Instance ord_mult_rid_class : MultRid ord := {
    mult_rid := ord_mult_rid
}.

Lemma ord_le_mult : ∀ α β, 0 ≤ α → 0 ≤ β → 0 ≤ α * β.
Proof.
    intros α β a b.
    apply ord_le_zero.
Qed.
Global Instance ord_le_mult_class : OrderMult ord := {
    le_mult := ord_le_mult
}.

Theorem ord_lt_lmult : ∀ {α β} γ, zero ≠ γ → α < β → γ * α < γ * β.
Proof.
    intros A B C C_neq lt.
    equiv_get_value A B C.
    get_ord_wo B.
    get_ord_wo C.
    unfold mult; equiv_simpl.
    rewrite ord_lt_initial in *.
    destruct lt as [x [f [f_bij f_iso]]].
    assert (∃ x : ord_U C, True) as C_nempty.
    {
        classic_contradiction contr.
        apply C_neq.
        symmetry.
        rewrite not_ex in contr.
        rewrite not_true in contr.
        unfold zero; cbn.
        unfold nat_to_ord; equiv_simpl.
        exists (λ x, False_rect _ (contr x)).
        split.
        split; split.
        -   intros a.
            contradiction (contr a).
        -   intros [b b_eq].
            contradiction (nat_neg2 b_eq).
        -   intros a.
            contradiction (contr a).
    }
    pose proof (well_ordered _ C_nempty) as [y [C0 y_min']]; clear C0.
    assert (∀ c : ord_U C, ord_le C y c) as y_min.
    {
        intros c.
        apply y_min'.
        exact true.
    }
    clear y_min'.
    exists (y, x).
    pose (g (ca : ord_U (C ⊗ A)) := (fst ca, [f (snd ca)|])).
    assert (∀ ca, initial_segment_set (C ⊗ B) (y, x) (g ca)) as g_in.
    {
        intros [c a].
        unfold g; cbn.
        destruct (f a) as [fa fa_lt]; cbn.
        split; cbn.
        -   left.
            exact fa_lt.
        -   intro contr; inversion contr.
            subst x.
            destruct fa_lt; contradiction.
    }
    exists (λ ca, [g ca|g_in ca]).
    split.
    split; split.
    -   intros [c1 a1] [c2 a2] eq.
        unfold g in eq; cbn in eq.
        inversion eq as [[eq1 eq2]].
        apply set_type_eq in eq2.
        apply f_bij in eq2.
        rewrite eq2; reflexivity.
    -   intros [[c b] cb_lt].
        assert (initial_segment_set B x b) as b_lt.
        {
            destruct cb_lt as [[leq|leq] neq].
            -   exact leq.
            -   destruct leq as [leq eq].
                subst b.
                specialize (y_min c).
                pose proof (antisym y_min leq).
                subst c.
                contradiction.
        }
        pose proof (sur f [b|b_lt]) as [a a_eq].
        exists (c, a).
        apply set_type_eq; cbn.
        unfold g; cbn.
        apply f_equal2; try reflexivity.
        rewrite a_eq.
        reflexivity.
    -   intros [c1 a1] [c2 a2].
        cbn.
        rewrite f_iso; cbn.
        unfold initial_segment_le.
        assert ((a1 ≠ a2) = ([f a1|] ≠ [f a2|])) as eq1.
        {
            apply propositional_ext; split; intros neq eq.
            -   apply set_type_eq in eq.
                apply f_bij in eq.
                contradiction.
            -   subst; contradiction.
        }
        assert ((a1 = a2) = ([f a1|] = [f a2|])) as eq2.
        {
            apply propositional_ext; split; intros eq.
            -   rewrite eq; reflexivity.
            -   apply set_type_eq in eq.
                apply f_bij in eq.
                exact eq.
        }
        rewrite eq1, eq2.
        reflexivity.
Qed.

Theorem ord_le_lmult : ∀ {α β} γ, α ≤ β → γ * α ≤ γ * β.
Proof.
    intros α β γ leq.
    classic_case (0 = γ) as [γ_eq|γ_neq].
    -   rewrite <- γ_eq.
        do 2 rewrite mult_lanni.
        apply refl.
    -   classic_case (α = β) as [eq|neq].
        +   rewrite eq.
            apply refl.
        +   apply ord_lt_lmult; try split; assumption.
Qed.
Lemma ord_le_lmult_pos : ∀ α β γ, 0 ≤ γ → α ≤ β → γ * α ≤ γ * β.
Proof.
    intros α β γ z leq.
    apply ord_le_lmult.
    exact leq.
Qed.
Global Instance ord_le_lmult_class : OrderLmult ord := {
    le_lmult_pos := ord_le_lmult_pos
}.

Theorem ord_lt_rmult : ∀ {α β} γ, α < β → α * γ ≤ β * γ.
Proof.
    intros A B C eq.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    equiv_get_value A B C.
    get_ord_wo B.
    get_ord_wo C.
    unfold mult in contr; equiv_simpl in contr.
    rewrite ord_lt_initial in eq, contr.
    destruct eq as [b [f [f_bij f_iso]]].
    destruct contr as [[a c] [g [g_bij g_iso]]].
    pose (h x := ([f (fst [g x|])|], snd [g x|])).
    assert (Injective h) as h_inj.
    {
        split.
        intros [b1 c1] [b2 c2] eq.
        unfold h in eq.
        inversion eq as [[eq1 eq2]].
        apply set_type_eq in eq1.
        apply f_bij in eq1.
        clear eq.
        pose proof (prod_combine _ _ eq1 eq2) as eq; clear eq1 eq2.
        apply set_type_eq in eq.
        apply g_bij in eq.
        exact eq.
    }
    assert (∀ a b, ord_le (B ⊗ C) a b ↔ ord_le (B ⊗ C) (h a) (h b)) as h_iso.
    {
        intros [b1 c1] [b2 c2].
        rewrite g_iso.
        cbn.
        destruct (g (b1, c1)) as [[gbc1_a gbc1_c] gbc1_lt]; cbn.
        destruct (g (b2, c2)) as [[gbc2_a gbc2_c] gbc2_lt]; cbn.
        rewrite f_iso.
        cbn.
        unfold initial_segment_le.
        reflexivity.
    }
    pose proof (ord_iso_le _ h h_inj h_iso (b, c)) as leq.
    unfold h in leq.
    destruct (g (b, c)) as [[gbc_a gbc_c] gbc_lt].
    cbn in leq.
    destruct (f gbc_a) as [fgbc fgbc_lt].
    unfold initial_segment_set in *.
    cbn in gbc_lt, leq.
    destruct gbc_lt as [gbc_lt gbc_neq].
    destruct fgbc_lt as [fgbc_lt fgbc_neq].
    destruct gbc_lt as [gbc_lt|gbc_lt], leq as [leq|leq].
    -   destruct gbc_lt as [gbc_lt gbc_neq2], leq as [leq_lt leq_neq].
        pose proof (antisym gbc_lt leq_lt).
        contradiction.
    -   destruct leq as [leq_lt leq_eq].
        symmetry in leq_eq.
        destruct gbc_lt; contradiction.
    -   destruct gbc_lt as [gbc_lt gbc_eq].
        symmetry in gbc_eq.
        destruct leq; contradiction.
    -   destruct leq as [leq_leq leq_eq].
        pose proof (antisym fgbc_lt leq_leq).
        contradiction.
Qed.

Theorem ord_le_rmult : ∀ {α β} γ, α ≤ β → α * γ ≤ β * γ.
Proof.
    intros α β γ leq.
    classic_case (0 = γ) as [γ_eq|γ_neq].
    -   rewrite <- γ_eq.
        do 2 rewrite mult_ranni.
        apply refl.
    -   classic_case (α = β) as [eq|neq].
        +   rewrite eq.
            apply refl.
        +   apply ord_lt_rmult; try split; assumption.
Qed.
Lemma ord_le_rmult_pos : ∀ α β γ, 0 ≤ γ → α ≤ β → α * γ ≤ β * γ.
Proof.
    intros α β γ z leq.
    apply ord_le_rmult.
    exact leq.
Qed.
Global Instance ord_le_rmult_class : OrderRmult ord := {
    le_rmult_pos := ord_le_rmult_pos
}.

Lemma ord_mult_lcancel : ∀ α β γ, 0 ≠ γ → γ * α = γ * β → α = β.
Proof.
    intros α β γ γ_nz eq.
    destruct (trichotomy α β) as [[leq|H]|leq]; try assumption.
    -   apply ord_lt_lmult with γ in leq; try exact γ_nz.
        destruct leq; contradiction.
    -   symmetry in eq.
        apply ord_lt_lmult with γ in leq; try exact γ_nz.
        destruct leq; contradiction.
Qed.
Global Instance ord_mult_lcancel_class : MultLcancel ord := {
    mult_lcancel := ord_mult_lcancel
}.

Theorem ord_lt_mult_lcancel : ∀ {α β} γ, γ * α < γ * β → α < β.
Proof.
    intros α β γ eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply ord_le_lmult with γ in contr.
    rewrite <- nlt_le in contr.
    contradiction.
Qed.

Theorem ord_le_mult_lcancel : ∀ {α β} γ, 0 ≠ γ → γ * α ≤ γ * β → α ≤ β.
Proof.
    intros α β γ γ_nz leq.
    classic_case (α = β) as [eq|neq].
    -   rewrite <- eq.
        apply refl.
    -   apply ord_lt_mult_lcancel with γ.
        split; try exact leq.
        intro contr.
        apply mult_lcancel in contr; try exact γ_nz.
        contradiction.
Qed.
Lemma ord_le_mult_lcancel_pos : ∀ α β γ, 0 < γ → γ * α ≤ γ * β → α ≤ β.
Proof.
    intros α β γ [γ_leq γ_nz] leq.
    apply ord_le_mult_lcancel with γ; assumption.
Qed.
Global Instance ord_le_mult_lcancel_pos_class : OrderMultLcancel ord := {
    le_mult_lcancel_pos := ord_le_mult_lcancel_pos
}.

Theorem ord_lt_mult_rcancel : ∀ {α β} γ, α * γ < β * γ → α < β.
Proof.
    intros α β γ eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply ord_le_rmult with γ in contr.
    rewrite <- nlt_le in contr.
    contradiction.
Qed.

Theorem ord_mult_zero_is_zero : ∀ α β, 0 = α * β → {0 = α} + {0 = β}.
Proof.
    intros α β eq.
    classic_case (0 = α) as [α_z|α_nz].
    -   left; exact α_z.
    -   right.
        rewrite neq_sym in α_nz.
        rename α into A.
        rename β into B.
        rename α_nz into A_nz.
        equiv_get_value A B.
        unfold zero in *; cbn in *.
        unfold nat_to_ord, mult in *; equiv_simpl.
        equiv_simpl in eq.
        equiv_simpl in A_nz.
        destruct eq as [f [f_bij f_iso]].
        assert (∀ m : set_type (λ n : nat, n < 0), False) as m_empty.
        {
            intros [m m_lt].
            apply nat_neg2 in m_lt.
            contradiction.
        }
        assert (ord_U A) as a.
        {
            clear B f f_bij f_iso.
            assert (∃ a : ord_U A, True).
            {
                classic_contradiction contr.
                apply A_nz.
                rewrite not_ex in contr.
                rewrite not_true in contr.
                exists (λ x, False_rect _ (contr x)).
                split.
                split; split.
                +   intros m.
                    exfalso.
                    contradiction (contr m).
                +   intros m.
                    contradiction (m_empty m).
                +   intros m.
                    exfalso.
                    contradiction (contr m).
            }
            destruct (ex_to_type H).
            assumption.
        }
        exists (λ m, False_rect _ (m_empty m)).
        split.
        split; split.
        +   intros m.
            exfalso.
            contradiction (m_empty m).
        +   intros b.
            pose proof (sur f (a, b)) as [m m_eq].
            contradiction (m_empty m).
        +   intros m.
            exfalso.
            contradiction (m_empty m).
Qed.

Theorem ord_le_one : ∀ α, α < 1 → 0 = α.
Proof.
    intros A eq.
    equiv_get_value A.
    unfold zero, one in *; cbn in *.
    unfold nat_to_ord in *.
    equiv_simpl.
    rewrite ord_lt_initial in eq.
    destruct eq as [[x x_lt] [f [f_bij f_iso]]].
    cbn in *.
    assert (ord_U A → False) as a_empty.
    {
        intros a.
        pose proof (f a) as [[b b_lt] b_eq].
        destruct b_eq as [b_leq b_neq].
        cbn in b_leq.
        unfold one in x_lt; cbn in x_lt.
        pose proof x_lt as x_lt2.
        rewrite nat_lt_suc_le in x_lt2.
        apply nat_neg_eq in x_lt2.
        subst x.
        unfold le in b_leq; cbn in b_leq.
        apply nat_neg_eq in b_leq.
        subst.
        contradiction b_neq.
        apply set_type_eq; reflexivity.
    }
    assert (∀ m : set_type (λ n : nat, n < 0), False) as m_empty.
    {
        intros [m m_lt].
        apply nat_neg2 in m_lt.
        contradiction.
    }
    exists (λ m, False_rect _ (m_empty m)).
    split.
    split; split.
    +   intros m.
        exfalso.
        contradiction (m_empty m).
    +   intros a.
        contradiction (a_empty a).
    +   intros m.
        exfalso.
        contradiction (m_empty m).
Qed.

Theorem ord_le_self_lmult : ∀ α β, 0 ≠ β → α ≤ β * α.
Proof.
    intros α β β_nz.
    rewrite <- (mult_lid α) at 1.
    apply ord_le_rmult.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply ord_le_one in contr.
    contradiction.
Qed.

Theorem ord_le_self_rmult : ∀ α β, 0 ≠ β → α ≤ α * β.
Proof.
    intros α β β_nz.
    rewrite <- (mult_rid α) at 1.
    apply ord_le_lmult.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply ord_le_one in contr.
    contradiction.
Qed.

Theorem nat_to_ord_mult : ∀ a b,
    nat_to_ord a * nat_to_ord b = nat_to_ord (a * b).
Proof.
    intros a b.
    unfold nat_to_ord, mult at 1; equiv_simpl.
    pose (dom := prod_type (set_type (λ m, m < a)) (set_type (λ m, m < b))).
    pose (f (n : dom) := [fst n|] * b + [snd n|]).
    assert (∀ n : dom, f n < a * b) as f_in.
    {
        intros [[m m_lt] [n n_lt]].
        unfold f; cbn.
        clear dom f.
        destruct a.
        -   apply nat_neg2 in m_lt.
            contradiction.
        -   rewrite nat_mult_lsuc.
            rewrite nat_lt_suc_le in m_lt.
            apply nat_le_rmult with b in m_lt.
            apply le_rplus with n in m_lt.
            apply lt_lplus with (a * b) in n_lt.
            rewrite (plus_comm b).
            exact (le_lt_trans m_lt n_lt).
    }
    exists (λ x, [f x|f_in x]).
    split.
    split; split.
    -   intros [[m1 m1_lt] [n1 n1_lt]] [[m2 m2_lt] [n2 n2_lt]] eq.
        inversion eq as [eq2]; clear eq.
        unfold f in eq2; cbn in eq2.
        destruct (trichotomy m1 m2) as [[leq|eq]|leq].
        +   exfalso.
            apply nat_lt_ex in leq as [c c_eq].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- plus_assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite eq2 in n1_lt.
            rewrite nat_mult_lsuc in n1_lt.
            rewrite <- plus_assoc in n1_lt.
            rewrite <- (plus_rid b) in n1_lt at 3.
            apply lt_plus_lcancel in n1_lt.
            contradiction (nat_neg2 n1_lt).
        +   subst.
            apply plus_lcancel in eq2.
            subst.
            apply f_equal2; apply set_type_eq; reflexivity.
        +   exfalso.
            apply nat_lt_ex in leq as [c c_eq].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- plus_assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite <- eq2 in n2_lt.
            rewrite nat_mult_lsuc in n2_lt.
            rewrite <- plus_assoc in n2_lt.
            rewrite <- (plus_rid b) in n2_lt at 3.
            apply lt_plus_lcancel in n2_lt.
            contradiction (nat_neg2 n2_lt).
    -   intros [n n_lt].
        (* TODO: Finish this proof once you have Euclidean division *)
Abort.

Theorem ord_not_trivial : 0 ≠ 1.
Proof.
    intros contr.
    symmetry in contr.
    unfold one, zero in contr; cbn in contr.
    unfold nat_to_ord in contr; equiv_simpl in contr.
    destruct contr as [f].
    pose proof (nat_lt_suc 0) as z_lt.
    contradiction (nat_lt_0_false (f [0|z_lt])).
Qed.

Theorem ord_lt_1 : ∀ α, α < 1 → 0 = α.
Proof.
    intros A A_lt.
    equiv_get_value A.
    unfold one, zero in *; cbn in *.
    unfold nat_to_ord in *.
    equiv_simpl.
    rewrite ord_lt_initial in A_lt.
    destruct A_lt as [[z z_lt] [f [f_bij f_iso]]].
    pose proof (nat_lt_one_eq z z_lt); subst z.
    exists (λ x, False_rect _ (nat_lt_0_false x)).
    split.
    1: split; split.
    -   intros a.
        contradiction (nat_lt_0_false a).
    -   intros a.
        exfalso.
        destruct (f a) as [[x x_lt'] x_lt]; cbn in *.
        unfold initial_segment_set in x_lt; cbn in x_lt.
        destruct x_lt as [leq neq].
        apply neq.
        apply antisym; try exact leq.
        unfold le; cbn.
        apply nat_pos.
    -   intros a.
        contradiction (nat_lt_0_false a).
Qed.
Close Scope ord_scope.
