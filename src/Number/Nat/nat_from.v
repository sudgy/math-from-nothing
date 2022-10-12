Require Import init.

Require Export nat_base.
Require Export nat_plus.
Require Export nat_mult.
Require Export nat_order.
Require Export nat_abstract.
Require Import set_order.

Fixpoint from_nat {U} `{Plus U, Zero U, One U} a :=
    match a with
    | nat_zero => 0
    | nat_suc a' => 1 + from_nat a'
    end.

Definition from_nat_kernel {U} `{Plus U, Zero U, One U} (n : nat) :=
    0 = from_nat (U := U) n ∧ 0 ≠ n.

Class Characteristic U n `{Plus U, Zero U, One U} := {
    characteristic : is_least le from_nat_kernel n
}.

Class CharacteristicZero U `{Plus U, Zero U, One U} := {
    characteristic_zero : ∀ n, 0 ≠ from_nat (nat_suc n)
}.

Class FromNatZ U n `{Plus U, Zero U, One U} := {
    from_nat_z : 0 = from_nat n
}.

Class FromNatNZ U n `{Plus U, Zero U, One U} := {
    from_nat_nz : 0 ≠ from_nat n
}.

Class Archimedean U `{Plus U, Zero U, Order U} := {
    archimedean : ∀ x y, 0 < x → 0 < y → ∃ n, x < n × y
}.
(* begin hide *)

Open Scope nat_scope.

Section FromNat.

Context {U} `{OrderedField U, @CharacteristicZero U UP UZ UE}.
(* end hide *)

Theorem from_nat_suc : ∀ n, from_nat (nat_suc n) = 1 + from_nat n.
Proof.
    reflexivity.
Qed.

Theorem from_nat_zero : from_nat 0 = (zero (U := U)).
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
Global Arguments from_nat : simpl never.

Theorem from_nat_eq : ∀ a b, from_nat a = from_nat b → a = b.
Proof.
    nat_induction a.
    -   intros b b_eq.
        rewrite from_nat_zero in b_eq.
        nat_destruct b; [>reflexivity|].
        contradiction (characteristic_zero _ b_eq).
    -   intros b eq.
        nat_destruct b.
        +   rewrite from_nat_zero in eq.
            symmetry in eq.
            contradiction (characteristic_zero _ eq).
        +   apply f_equal.
            apply IHa.
            do 2 rewrite from_nat_suc in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Theorem nat_mult_rid : ∀ a, a × (one (U := U)) = from_nat a.
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

Theorem from_nat_one : from_nat (U := U) 1 = 1.
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

Theorem from_nat_two : from_nat (U := U) 2 = 2.
Proof.
    rewrite from_nat_plus.
    rewrite from_nat_one.
    reflexivity.
Qed.

Theorem from_nat_three : from_nat (U := U) 3 = 3.
Proof.
    rewrite from_nat_plus.
    rewrite from_nat_one, from_nat_two.
    reflexivity.
Qed.

Theorem from_nat_four : from_nat (U := U) 4 = 4.
Proof.
    rewrite from_nat_plus.
    rewrite from_nat_one, from_nat_three.
    reflexivity.
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

Theorem nat_mult_from : ∀ a b, a × b = from_nat a * b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite from_nat_zero.
        rewrite mult_lanni.
        apply nat_mult_lanni.
    -   rewrite nat_mult_suc.
        rewrite IHa.
        rewrite from_nat_suc.
        rewrite rdist, mult_lid.
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

(* begin hide *)
End FromNat.

(* end hide *)
Section CharacteristicImply.

Context {U} `{OrderedField U, @CharacteristicZero U UP UZ UE}.

#[refine]
Local Instance characteristic_zero_not_trivial : NotTrivial U := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    rewrite <- from_nat_one.
    apply characteristic_zero.
Qed.

Global Instance characteristic_zero_two : FromNatNZ U 2.
Proof.
    split.
    rewrite nat_plus_lsuc.
    apply characteristic_zero.
Qed.
Global Instance characteristic_zero_three : FromNatNZ U 3.
Proof.
    split.
    rewrite nat_plus_lsuc.
    apply characteristic_zero.
Qed.
Global Instance characteristic_zero_four : FromNatNZ U 4.
Proof.
    split.
    rewrite nat_plus_lsuc.
    apply characteristic_zero.
Qed.

Variable n : nat.

Local Instance characteristic_zero_not : FromNatNZ U (nat_suc n).
Proof.
    split.
    apply characteristic_zero.
Qed.

End CharacteristicImply.
Section CharacteristicSpecific.

Context {U} `{
    OrderedField U,
    @FromNatNZ U 2 UP UZ UE,
    @FromNatNZ U 3 UP UZ UE,
    @FromNatNZ U 4 UP UZ UE
}.

Theorem two_nz : 0 ≠ 2.
Proof.
    rewrite <- from_nat_two.
    apply from_nat_nz.
Qed.

Theorem three_nz : 0 ≠ 3.
Proof.
    rewrite <- from_nat_three.
    apply from_nat_nz.
Qed.

Theorem four_nz : 0 ≠ 4.
Proof.
    rewrite <- from_nat_four.
    apply from_nat_nz.
Qed.

End CharacteristicSpecific.
Section OrderedFieldCharacteristic.

Context {U} `{OrderedField U, @CharacteristicZero U UP UZ UE}.

Global Instance ordered_field_char : CharacteristicZero U.
Proof.
    split.
    apply from_nat_pos.
Qed.

End OrderedFieldCharacteristic.

(* begin hide *)
Section Archimedean.

Context {U} `{OrderedField U}.

(* end hide *)
Let a1 := ∀ x : U, 0 < x → ∃ n, x < from_nat n.
Let a2 := ∀ ε, 0 < ε → ∃ n, /from_nat (nat_suc n) < ε.

Theorem field_impl_arch1 : a1 → Archimedean U.
Proof.
    intros arch.
    split.
    unfold a1 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    pose proof (arch (x / y) (lt_mult x_pos (div_pos y_pos))) as [n n_lt].
    rewrite <- lt_mult_rrmove_pos in n_lt by exact y_pos.
    rewrite <- nat_mult_from in n_lt.
    exists n.
    exact n_lt.
Qed.

Theorem field_impl_arch2 : a2 → Archimedean U.
Proof.
    intros arch.
    apply field_impl_arch1.
    unfold a1; unfold a2 in arch; clear a1 a2.
    intros x x_pos.
    specialize (arch _ (div_pos x_pos)) as [n n_ltq].
    exists (nat_suc n).
    apply lt_div_pos in n_ltq; [>|apply div_pos; apply from_nat_pos].
    rewrite div_div in n_ltq by apply x_pos.
    rewrite div_div in n_ltq by apply from_nat_pos.
    exact n_ltq.
Qed.

Context `{@Archimedean U UP UZ UO}.

Theorem archimedean1 : a1.
Proof.
    unfold a1; clear a1 a2.
    intros x x_pos.
    pose proof (archimedean x 1 x_pos one_pos) as [n eq].
    exists n.
    rewrite nat_mult_rid in eq.
    exact eq.
Qed.

Theorem archimedean2 : a2.
Proof.
    pose proof (archimedean1) as arch.
    unfold a1, a2 in *; clear a1 a2.
    intros ε ε_pos.
    specialize (arch (/ε) (div_pos ε_pos)) as [n eq].
    nat_destruct n.
    -   rewrite from_nat_zero in eq.
        apply div_pos in ε_pos.
        destruct (trans ε_pos eq); contradiction.
    -   rewrite <- lt_mult_1_ab_da_b_pos in eq by exact ε_pos.
        rewrite lt_mult_1_ab_db_a_pos in eq by apply from_nat_pos.
        exists n.
        exact eq.
Qed.

Theorem archimedean1' : ∀ x : U, ∃ n, x < from_nat n.
Proof.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   apply archimedean1.
        exact x_pos.
    -   rewrite nlt_le in x_neg.
        exists 1.
        rewrite from_nat_one.
        exact (le_lt_trans x_neg one_pos).
Qed.

Theorem arch_pow2 : ∀ ε, 0 < ε → ∃ n, /(2^n) < ε.
Proof.
    intros ε ε_pos.
    pose proof (archimedean2 ε ε_pos) as [n ltq].
    exists (nat_suc n).
    apply (trans2 ltq).
    apply lt_div_pos; [>apply from_nat_pos|].
    clear ltq.
    remember (nat_suc n) as n'.
    clear n Heqn'; rename n' into n.
    nat_induction n.
    -   rewrite from_nat_zero.
        rewrite nat_pow_zero.
        exact one_pos.
    -   rewrite from_nat_suc.
        apply lt_lplus with 1 in IHn.
        apply (lt_le_trans IHn).
        rewrite nat_pow_suc.
        rewrite mult_comm, <- plus_two.
        apply le_rplus.
        clear IHn.
        apply nat_pow_le_one.
        rewrite <- le_plus_0_a_b_ba.
        apply one_pos.
Qed.
(* begin hide *)

End Archimedean.
Close Scope nat_scope.
(* end hide *)
