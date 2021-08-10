Require Import init.

Require Import nat0.

Fixpoint pow_nat0 {U} `{Mult U} `{One U} a b :=
    match b with
    | nat0_zero => 1
    | nat0_suc b' => pow_nat0 a b' * a
    end.
Infix "^" := pow_nat0 : nat0_scope.

Section Pow.

Context {U} `{Up : Plus U,
                  @PlusAssoc U Up,
                  @PlusComm U Up,
              Uz : Zero U,
                  @PlusLid U Up Uz,
              Un : Neg U,
                  @PlusLinv U Up Uz Un,
              Um : Mult U,
                  @MultAssoc U Um,
                  @MultComm U Um,
                  @Ldist U Up Um,
                  @Rdist U Up Um,
                  @MultLanni U Uz Um,
                  @MultRanni U Uz Um,
              Uo : One U,
                  @MultLid U Um Uo,
                  @MultRid U Um Uo,
                  @MultLcancel U Uz Um,
                  @MultRcancel U Uz Um,
              Ul : Order U,
                  @Connex U le,
                  @Antisymmetric U le,
                  @Transitive U le,
                  @NotTrivial U Uz Uo
              }.

Local Open Scope nat0_scope.

Theorem pow_simpl : ∀ a n, a ^ (nat0_suc n) = a^n * a.
    intros; reflexivity.
Qed.

Theorem pow_0_nat0 : ∀ a, a ^ 0 = 1.
    intros a.
    unfold zero; cbn.
    reflexivity.
Qed.

Theorem pow_1_nat0 : ∀ a, a ^ 1 = a.
    intros a.
    unfold one; cbn.
    apply mult_lid.
Qed.

Theorem one_pow_nat0 : ∀ n, 1 ^ n = 1.
    nat0_induction n.
    -   apply pow_0_nat0.
    -   cbn.
        rewrite IHn.
        apply mult_lid.
Qed.

Theorem pow_mult_nat0 : ∀ a m n, a ^ m * a ^ n = a ^ (m + n).
    intros a m n.
    nat0_induction n.
    -   rewrite pow_0_nat0, mult_rid.
        rewrite plus_rid.
        reflexivity.
    -   rewrite nat0_plus_rsuc.
        cbn.
        rewrite mult_assoc.
        rewrite IHn.
        reflexivity.
Qed.

Theorem pow_mult_mult_nat0 : ∀ a m n, (a ^ m) ^ n = a ^ (m * n).
    intros a m n.
    nat0_induction n.
    -   rewrite mult_ranni.
        do 2 rewrite pow_0_nat0.
        reflexivity.
    -   cbn.
        rewrite IHn.
        rewrite pow_mult_nat0.
        rewrite nat0_mult_rsuc.
        rewrite plus_comm.
        reflexivity.
Qed.

Theorem pow_not_zero_nat0 : ∀ a n, 0 ≠ a → 0 ≠ a ^ n.
    intros a n a_nz eq.
    nat0_induction n.
    -   rewrite pow_0_nat0 in eq.
        apply not_trivial.
        exact eq.
    -   apply IHn.
        cbn in eq.
        rewrite <- (mult_lanni a) in eq.
        apply mult_rcancel in eq; auto.
Qed.

End Pow.
