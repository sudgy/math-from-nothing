Require Import init.

Require Export nat_base.
Require Export nat_plus.
Require Export nat_mult.
Require Export nat_order.
Require Export nat_abstract.

Fixpoint from_nat {U} `{Plus U, Zero U, One U} a :=
    match a with
    | nat_zero => 0
    | nat_suc a' => 1 + from_nat a'
    end.

Class Characteristic U n `{Plus U, Zero U, One U} := {
    characteristic : 0 = from_nat n
}.

Class CharacteristicNot U n `{Plus U, Zero U, One U} := {
    characteristic_not : 0 ≠ from_nat n
}.

Class CharacteristicZero U `{Plus U, Zero U, One U} := {
    characteristic_zero : ∀ n, 0 ≠ from_nat (nat_suc n)
}.

Class Archimedean U `{Plus U, Zero U, Order U} := {
    archimedean : ∀ x y, 0 < x → 0 < y → ∃ n, x < n × y
}.

Open Scope nat_scope.

(* begin hide *)
Section FromNat.

Context {U} `{OrderedField U}.
(* end hide *)

Theorem from_nat_suc : ∀ n, from_nat (nat_suc n) = 1 + from_nat n.
Proof.
    reflexivity.
Qed.

Theorem from_nat_eq_nat : ∀ a, from_nat a = a.
Proof.
    nat_induction a.
    -   reflexivity.
    -   cbn.
        rewrite IHa.
        reflexivity.
Qed.

Theorem from_nat_zero : from_nat 0 = (zero (U := U)).
Proof.
    reflexivity.
Qed.

Theorem from_nat_mult_one : ∀ a, a × (one (U := U)) = from_nat a.
Proof.
    nat_induction a.
    -   rewrite nat_mult_lanni.
        rewrite from_nat_zero.
        reflexivity.
    -   rewrite nat_mult_suc.
        rewrite IHa.
        rewrite from_nat_suc.
        reflexivity.
Qed.

Global Arguments from_nat : simpl never.

Theorem from_nat_one : from_nat 1 = (one (U := U)).
Proof.
    rewrite <- nat_one_eq.
    rewrite from_nat_suc.
    rewrite from_nat_zero.
    apply plus_rid.
Qed.

Theorem from_nat_plus : ∀ a b,
    from_nat (a + b) = from_nat a + from_nat b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite from_nat_zero.
        do 2 rewrite plus_lid.
        reflexivity.
    -   rewrite nat_plus_lsuc.
        do 2 rewrite from_nat_suc.
        rewrite IHa.
        apply plus_assoc.
Qed.

Theorem from_nat_mult : ∀ a b,
    from_nat (a * b) = from_nat a * from_nat b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite mult_lanni.
        rewrite from_nat_zero.
        rewrite mult_lanni.
        reflexivity.
    -   rewrite nat_mult_lsuc.
        rewrite from_nat_suc.
        rewrite rdist.
        rewrite mult_lid.
        rewrite from_nat_plus.
        rewrite IHa.
        reflexivity.
Qed.

Theorem from_nat_nat_mult : ∀ a b, from_nat a * b = a × b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite from_nat_zero.
        rewrite nat_mult_lanni.
        apply mult_lanni.
    -   rewrite from_nat_suc.
        rewrite rdist, mult_lid.
        rewrite IHa.
        rewrite nat_mult_suc.
        reflexivity.
Qed.

Theorem from_nat_pos : ∀ a, 0 < from_nat (nat_suc a).
Proof.
    nat_induction a.
    -   rewrite from_nat_one.
        exact one_pos.
    -   rewrite from_nat_suc.
        apply lt_pos_plus; [>exact one_pos|exact IHa].
Qed.

Theorem from_nat_pos2 : ∀ a, 0 ≤ from_nat a.
Proof.
    nat_induction a.
    -   rewrite from_nat_zero.
        apply refl.
    -   rewrite from_nat_suc.
        apply le_pos_plus; [>apply one_pos|exact IHa].
Qed.

Theorem from_nat_eq : ∀ a b, from_nat a = from_nat b → a = b.
Proof.
    nat_induction a.
    -   intros b b_eq.
        rewrite from_nat_zero in b_eq.
        nat_destruct b; [>reflexivity|].
        apply from_nat_pos in b_eq.
        contradiction b_eq.
    -   intros b eq.
        nat_destruct b.
        +   rewrite from_nat_zero in eq.
            symmetry in eq.
            apply from_nat_pos in eq.
            contradiction eq.
        +   apply f_equal.
            apply IHa.
            do 2 rewrite from_nat_suc in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Theorem from_nat_le : ∀ a b, from_nat a ≤ from_nat b ↔ a ≤ b.
Proof.
    intros a b.
    split.
    -   revert b.
        nat_induction a.
        +   intros b b_ge.
            apply nat_pos.
        +   nat_destruct b.
            *   intros contr.
                rewrite from_nat_zero in contr.
                pose proof (from_nat_pos a) as ltq.
                destruct (lt_le_trans ltq contr); contradiction.
            *   intros leq.
                rewrite nat_sucs_le.
                apply IHa.
                do 2 rewrite from_nat_suc in leq.
                apply le_plus_lcancel in leq.
                exact leq.
    -   revert b.
        nat_induction a.
        +   intros b b_ge.
            rewrite from_nat_zero.
            apply from_nat_pos2.
        +   intros b b_ge.
            nat_destruct b.
            *   pose proof (nat_pos2 a) as a_pos.
                destruct (lt_le_trans a_pos b_ge); contradiction.
            *   do 2 rewrite from_nat_suc.
                apply le_lplus.
                apply IHa.
                rewrite nat_sucs_le in b_ge.
                exact b_ge.
Qed.

Theorem from_nat_lt : ∀ a b,
    from_nat a < from_nat b ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    rewrite from_nat_le.
    rewrite (f_eq_iff from_nat_eq).
    reflexivity.
Qed.

Let a1 := ∀ x : U, ∃ n, x < from_nat n.
Let a2 := ∀ ε, 0 < ε → ∃ n, /from_nat (nat_suc n) < ε.

Theorem field_impl_arch1 : a1 → Archimedean U.
Proof.
    intros arch.
    split.
    unfold a1 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    pose proof (arch (x / y)) as [n n_lt].
    rewrite <- lt_mult_rrmove_pos in n_lt by exact y_pos.
    rewrite from_nat_nat_mult in n_lt.
    exists n.
    exact n_lt.
Qed.

Theorem field_impl_arch2 : a2 → Archimedean U.
Proof.
    intros arch.
    split.
    unfold a2 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    pose proof (div_pos x_pos) as x'_pos.
    pose proof (lt_mult x'_pos y_pos) as ε_pos.
    specialize (arch _ ε_pos) as [n eq].
    rewrite <- lt_mult_llmove_pos in eq by exact x_pos.
    rewrite <- lt_mult_rrmove_pos in eq by apply from_nat_pos.
    rewrite mult_comm in eq.
    rewrite from_nat_nat_mult in eq.
    exists (nat_suc n).
    exact eq.
Qed.

Context `{@Archimedean U UP UZ UO}.

Theorem archimedean1 : a1.
Proof.
    unfold a1; clear a1 a2.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   pose proof (archimedean x 1 x_pos one_pos) as [n eq].
        exists n.
        rewrite from_nat_mult_one in eq.
        exact eq.
    -   rewrite nlt_le in x_neg.
        exists 1.
        apply (le_lt_trans x_neg).
        apply from_nat_pos.
Qed.

Theorem archimedean2 : a2.
Proof.
    pose proof (archimedean1) as arch.
    unfold a1, a2 in *; clear a1 a2.
    intros ε ε_pos.
    specialize (arch (/ε)) as [n eq].
    nat_destruct n.
    -   rewrite from_nat_zero in eq.
        apply div_pos in ε_pos.
        destruct (trans ε_pos eq); contradiction.
    -   rewrite <- lt_mult_1_ab_da_b_pos in eq by exact ε_pos.
        rewrite lt_mult_1_ab_db_a_pos in eq by apply from_nat_pos.
        exists n.
        exact eq.
Qed.

Theorem arch_pow2 : ∀ ε, 0 < ε → ∃ n, /(2^n) < ε.
Proof.
    intros ε ε_pos.
    pose proof (archimedean2 ε ε_pos) as [n ltq].
    exists (nat_suc n).
    apply (trans2 ltq).
    apply lt_div_pos; [>apply from_nat_pos|].
    clear ltq.
    nat_induction n.
    -   rewrite from_nat_one.
        rewrite pow_1_nat.
        rewrite <- lt_plus_0_a_b_ba.
        exact one_pos.
    -   rewrite from_nat_suc.
        apply lt_lplus with 1 in IHn.
        apply (trans IHn).
        rewrite (pow_simpl _ (nat_suc n)).
        rewrite ldist.
        rewrite mult_rid.
        apply lt_rplus.
        clear IHn.
        nat_induction n.
        +   rewrite pow_1_nat.
            rewrite <- lt_plus_0_a_b_ba.
            exact one_pos.
        +   apply (trans IHn).
            rewrite (pow_simpl _ (nat_suc n)).
            rewrite <- (mult_rid (2^nat_suc n)) at 1.
            apply lt_lmult_pos.
            *   apply pow_pos2.
                exact two_pos.
            *   rewrite <- lt_plus_0_a_b_ba.
                exact one_pos.
Qed.

Context `{
    @CharacteristicNot U 2 UP UZ UE,
    @CharacteristicZero U UP UZ UE
}.

Theorem two_nz : 0 ≠ 2.
Proof.
    pose proof characteristic_not as neq.
    rewrite from_nat_plus in neq.
    rewrite from_nat_one in neq.
    exact neq.
Qed.

Local Program Instance characteristic_zero_not_trivial : NotTrivial U := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    rewrite <- from_nat_one.
    apply characteristic_zero.
Qed.

Global Program Instance not_trivial_char : CharacteristicZero U.
Next Obligation.
    apply from_nat_pos.
Qed.
(* begin hide *)

End FromNat.
Close Scope nat_scope.
(* end hide *)
