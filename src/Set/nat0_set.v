Require Import init.

Require Export nat0.
Require Export set_type.

Definition nat0_to_set n := λ x, x < n.
Definition nat0_to_set_type n := set_type (nat0_to_set n).

Definition sequence (U : Type) := nat0 → U.
Definition subsequence_seq (f : sequence nat0) := ∀ n, f n < f (nat0_suc n).
Definition subsequence {U} (a b : sequence U) :=
    ∃ f : sequence nat0,
        subsequence_seq f ∧
        (∀ n, a (f n) = b n).

Theorem nat0_lt_0_false : nat0_to_set_type 0 → False.
    intros [x x_lt].
    contradiction (nat0_lt_zero x x_lt).
Qed.

Theorem subsequence_seq_leq : ∀ f, subsequence_seq f → ∀ n, n <= f n.
    intros f f_sub.
    unfold subsequence_seq in f_sub.
    intros n.
    nat0_induction n.
    -   apply nat0_le_zero.
    -   rewrite <- nat0_lt_suc_le.
        rewrite nat0_sucs_lt.
        exact (le_lt_trans IHn (f_sub n)).
Qed.

#[universes(template)]
Record nat0_strong_recursion_domain B := make_nat0_srd {
    nat0_sr_p : nat0;
    nat0_sr_f : nat0_to_set_type (nat0_suc nat0_sr_p) → B;
}.

(* begin hide *)
Module StrongRecursion.
Section StrongRecursion.

Variable B : Type.
Variable c : B.
Variable h : nat0_strong_recursion_domain B → B.

Lemma nat0_sucs_lt_impl : ∀ {a b}, a < b → nat0_suc a < nat0_suc b.
    intros a b eq.
    rewrite nat0_sucs_lt.
    exact eq.
Qed.
Lemma nat0_lt_suc_trans : ∀ {a b c}, a < nat0_suc b → b < c → a < nat0_suc c.
    clear.
    intros a b c eq1 eq2.
    rewrite nat0_lt_suc_le in eq1.
    pose proof (le_lt_trans eq1 eq2) as eq3.
    apply (trans eq3).
    apply nat0_lt_suc.
Qed.

Definition K (j : nat0_strong_recursion_domain B) :=
    nat0_sr_f B j [0|nat0_zero_lt_suc (nat0_sr_p B j)] = c ∧
    ∀ m : nat0_to_set_type (nat0_sr_p B j),
        nat0_sr_f B j [nat0_suc [m|] | nat0_sucs_lt_impl [|m]] =
        h (make_nat0_srd B [m|] (λ x : nat0_to_set_type (nat0_suc [m|]),
            nat0_sr_f B j [[x|] | nat0_lt_suc_trans [|x] [|m]])).

Theorem ks_eq : ∀ k1 k2, K k1 → K k2 → ∀ x1 x2, [x1|] = [x2|] →
        nat0_sr_f B k1 x1 = nat0_sr_f B k2 x2.
    intros k1 k2 Kk1 Kk2 [x x_lt1] [x' x_lt2] eq; cbn in *.
    subst x'.
    unfold nat0_to_set in *.
    induction x using strong_induction.
    nat0_destruct x.
    -   destruct Kk1 as [eq1 C]; clear C.
        destruct Kk2 as [eq2 C]; clear C.
        rewrite (proof_irrelevance _ x_lt1) in eq1.
        rewrite (proof_irrelevance _ x_lt2) in eq2.
        rewrite <- eq2 in eq1.
        exact eq1.
    -   destruct Kk1 as [C Kk1]; clear C.
        destruct Kk2 as [C Kk2]; clear C.
        pose proof x_lt1 as x_lt1'.
        pose proof x_lt2 as x_lt2'.
        rewrite nat0_sucs_lt in x_lt1', x_lt2'.
        specialize (Kk1 [x|x_lt1']).
        specialize (Kk2 [x|x_lt2']).
        cbn in *.
        rewrite (proof_irrelevance _ x_lt1) in Kk1.
        rewrite (proof_irrelevance _ x_lt2) in Kk2.
        unfold nat0_to_set in *.
        rewrite Kk1, Kk2.
        apply f_equal.
        apply f_equal.
        apply functional_ext.
        intros [y y_lt]; cbn.
        unfold nat0_to_set in y_lt.
        apply H.
        exact y_lt.
Qed.

Lemma nat0_lt_suc_le_impl : ∀ {a b}, a < nat0_suc b → a ≠ b → a < b.
    intros a b ltq neq.
    rewrite nat0_lt_suc_le in ltq.
    split; assumption.
Qed.

Lemma nat0_k_ex : ∀ n : nat0, ∃ k, K k ∧ n < nat0_suc (nat0_sr_p B k).
    intros n.
    nat0_induction n.
    -   exists (make_nat0_srd B 0 (λ x, c)).
        repeat split; cbn.
        +   intros m.
            contradiction (nat0_lt_0_false m).
        +   intro contr; inversion contr.
    -   destruct IHn as [k [[k0 Kk] ltq]].
        pose (f (x : nat0_to_set_type (nat0_suc (nat0_suc (nat0_sr_p B k)))) :=
            match strong_excluded_middle ([x|] = nat0_suc (nat0_sr_p B k)) with
            | strong_or_left _ => h k
            | strong_or_right H =>
                nat0_sr_f B k [[x|] | nat0_lt_suc_le_impl [|x] H]
            end
        ).
        exists (make_nat0_srd B _ f); cbn.
        split.
        +   split; cbn.
            *   unfold f; cbn.
                destruct (strong_excluded_middle (0 = nat0_suc (nat0_sr_p B k)))
                    as [eq|neq].
                --  inversion eq.
                --  rewrite <- k0.
                    apply f_equal.
                    apply set_type_eq; reflexivity.
            *   intros [m m_lt]; cbn.
                unfold f; cbn; clear f.
                destruct (strong_excluded_middle
                    (nat0_suc m = nat0_suc (nat0_sr_p B k)))
                    as [eq|neq]; cbn.
                --  inversion eq.
                    subst m.
                    clear eq.
                    apply f_equal.
                    destruct k as [kp kf]; cbn in *.
                    apply f_equal.
                    apply functional_ext.
                    intros [x x_lt]; cbn.
                    destruct (strong_excluded_middle (x = nat0_suc kp))
                            as [eq|neq].
                    ++  exfalso.
                        rewrite eq in x_lt.
                        destruct x_lt; contradiction.
                    ++  apply f_equal.
                        apply set_type_eq; reflexivity.
                --  unfold nat0_to_set in m_lt.
                    pose proof m_lt as m_lt2.
                    rewrite nat0_lt_suc_le in m_lt2.
                    assert (m < nat0_sr_p B k) as m_lt3.
                    {
                        split; try exact m_lt2.
                        intro; subst.
                        contradiction.
                    }
                    specialize (Kk [m|m_lt3]).
                    cbn in *.
                    rewrite (proof_irrelevance _ (nat0_sucs_lt_impl m_lt3)).
                    rewrite Kk.
                    apply f_equal.
                    apply f_equal.
                    apply functional_ext.
                    intros [x x_lt]; cbn.
                    destruct
                        (strong_excluded_middle (x = nat0_suc (nat0_sr_p B k)))
                        as [eq2|neq2].
                    ++  subst.
                        unfold nat0_to_set in x_lt.
                        exfalso.
                        rewrite nat0_sucs_lt in x_lt.
                        pose proof (le_lt_trans m_lt2 x_lt) as [C0 C1].
                        contradiction.
                    ++  apply f_equal.
                        apply set_type_eq; reflexivity.
        +   rewrite nat0_sucs_lt.
            exact ltq.
Qed.

Definition k n :=
    nat0_sr_f B (ex_val (nat0_k_ex n)) [n | rand (ex_proof (nat0_k_ex n))].

End StrongRecursion.
End StrongRecursion.

Import StrongRecursion.
(* end hide *)
Theorem strong_recursion : ∀ B c (h : nat0_strong_recursion_domain B → B),
        ∃ k : nat0 → B,
        k 0 = c ∧
        ∀ n, k (nat0_suc n) = h (
            make_nat0_srd B
                n
                (λ (x : nat0_to_set_type (nat0_suc n)), k [x|])
        ).
    intros B c h.
    exists (k B c h).
    unfold k, ex_val, ex_proof.
    split.
    -   destruct (ex_to_type (nat0_k_ex B c h 0))
            as [k [[k0 Kk] z_lt]]; cbn.
        rewrite (proof_irrelevance _ (nat0_zero_lt_suc (nat0_sr_p B k))).
        exact k0.
    -   intros n.
        destruct (ex_to_type (nat0_k_ex B c h (nat0_suc n)))
            as [k [Kk n_lt]]; cbn.
        pose proof Kk as [k0 Kk2].
        pose proof n_lt as n_lt2.
        rewrite nat0_sucs_lt in n_lt2.
        specialize (Kk2 [n|n_lt2]).
        cbn in *.
        rewrite (proof_irrelevance _ (nat0_sucs_lt_impl n_lt2)).
        rewrite Kk2.
        apply f_equal.
        apply f_equal.
        apply functional_ext.
        intros [x x_lt]; cbn.
        destruct (ex_to_type (nat0_k_ex B c h x))
            as [k' [Kk' x_lt']]; cbn.
        apply (ks_eq B c h); try assumption; reflexivity.
Qed.
