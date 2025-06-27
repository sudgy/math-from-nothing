Require Import init.

Require Export card2_nat.
Require Import nat.
Require Export ord2_nat.

Open Scope card_scope.

Definition finite κ := κ < |nat|.
Definition infinite κ := |nat| ≤ κ.

Theorem nfin_inf : ∀ κ, ¬finite κ ↔ infinite κ.
Proof.
    intros κ.
    apply nlt_le.
Qed.

Theorem ninf_fin : ∀ κ, ¬infinite κ ↔ finite κ.
Proof.
    intros κ.
    apply nle_lt.
Qed.

Theorem aleph_infinite : ∀ α, infinite (aleph α).
Proof.
    intros α.
    unfold infinite.
    rewrite <- aleph_0.
    apply homo_le.
    apply all_pos.
Qed.

Theorem nat_is_finite : ∀ n, finite (from_nat n).
Proof.
    exact nat_lt_card.
Qed.

Theorem fin_nat_ex : ∀ κ, finite κ → ∃ n, from_nat n = κ.
Proof.
    intros κ κ_fin.
    apply card_lt_nat in κ_fin as [n eq].
    exists n; symmetry; exact eq.
Qed.

Theorem greater_all_nat_inf : ∀ κ, (∀ a, from_nat a < κ) → infinite κ.
Proof.
    intros κ κ_gt.
    unfold infinite.
    order_contradiction ltq.
    apply fin_nat_ex in ltq as [n eq]; subst.
    contradiction (irrefl _ (κ_gt n)).
Qed.

Theorem inf_not_nat : ∀ κ, infinite κ → ∀ n, from_nat n ≠ κ.
Proof.
    intros κ κ_inf n contr.
    subst.
    contradiction (irrefl _ (le_lt_trans κ_inf (nat_is_finite n))).
Qed.

Theorem simple_finite_finite : ∀ U, simple_finite U ↔ finite (|U|).
Proof.
    intros U.
    split.
    -   intros U_fin.
        unfold finite.
        destruct U_fin as [n fin].
        apply (le_lt_trans2 (nat_is_finite n)).
        rewrite from_nat_card.
        unfold le; equiv_simpl.
        exact fin.
    -   intros U_fin.
        apply fin_nat_ex in U_fin as [n eq].
        exists n.
        symmetry in eq.
        rewrite from_nat_card in eq.
        equiv_simpl in eq.
        destruct eq as [f [f_inj]].
        exists f.
        exact f_inj.
Qed.

Theorem finite_sum : ∀ U V, finite (|U|) → finite (|V|) → finite (|U + V|)%type.
Proof.
    intros U V.
    do 3 rewrite <- simple_finite_finite.
    apply simple_finite_sum.
Qed.

Theorem finite_prod : ∀ U V, finite (|U|) → finite (|V|) → finite (|U*V|)%type.
Proof.
    intros U V.
    do 3 rewrite <- simple_finite_finite.
    apply simple_finite_prod.
Qed.

Theorem finite_union {U} : ∀ S T : U → Prop,
    finite (|set_type S|) → finite (|set_type T|) → finite (|set_type (S ∪ T)|).
Proof.
    intros S T.
    do 3 rewrite <- simple_finite_finite.
    apply simple_finite_union.
Qed.

Theorem empty_finite : finite (|empty_type|).
Proof.
    rewrite <- simple_finite_finite.
    apply empty_simple_finite.
Qed.

Theorem singleton_finite : finite (|singleton_type|).
Proof.
    rewrite <- simple_finite_finite.
    apply singleton_simple_finite.
Qed.

Theorem infinite_nz : ∀ {κ}, infinite κ → 0 ≠ κ.
Proof.
    intros κ κ_inf.
    rewrite <- (homo_zero (f := from_nat)).
    apply (inf_not_nat _ κ_inf).
Qed.

Theorem infinite_ex {U} : infinite (|U|) → U.
Proof.
    intros U_inf.
    apply card_nz_ex.
    apply infinite_nz.
    exact U_inf.
Qed.

Section Order.

Context {U} `{TotalOrder U}.

Theorem finite_min : finite (|U|) → U → ∃ m, ∀ a, m ≤ a.
Proof.
    intros U_fin.
    rewrite <- simple_finite_finite in U_fin.
    apply (simple_finite_min U_fin).
Qed.

Theorem finite_max : finite (|U|) → U → ∃ m, ∀ a, a ≤ m.
Proof.
    intros U_fin.
    rewrite <- simple_finite_finite in U_fin.
    apply (simple_finite_max U_fin).
Qed.

Theorem all_greater_inf : U → (∀ a, ∃ b, a < b) → infinite (|U|).
Proof.
    intros a gt_ex.
    unfold infinite, le; equiv_simpl.
    pose (f := fix get n :=
        match n with
        | nat_zero => a
        | nat_suc n' => ex_val (gt_ex (get n'))
        end).
    assert (∀ n, f n < f (nat_suc n)) as f_lt_suc.
    {
        intros n.
        cbn.
        exact (ex_proof (gt_ex (f n))).
    }
    assert (∀ m n, m < n → f m < f n) as f_lt.
    {
        intros m n ltq.
        apply nat_lt_ex in ltq as [c c_eq]; subst n.
        nat_induction c.
        -   rewrite plus_comm.
            apply f_lt_suc.
        -   apply (trans IHc).
            rewrite (nat_plus_rsuc m (nat_suc c)).
            apply f_lt_suc.
    }
    exists f.
    split.
    intros m n eq.
    destruct (trichotomy m n) as [[ltq|eq']|ltq].
    -   apply f_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply f_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

End Order.

Close Scope card_scope.
