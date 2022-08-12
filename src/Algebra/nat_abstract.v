Require Import init.

Require Export plus.
Require Export mult.
Require Export relation.
Require Import order_mult.
Require Export nat.

Fixpoint abstract_mult {U} `{Plus U, Zero U} (a : nat) (b : U) :=
    match a with
    | nat_zero => 0
    | nat_suc a' => b + abstract_mult a' b
    end.

Infix "×" := abstract_mult (at level 40, left associativity).

Fixpoint nat_to_abstract {U} `{Plus U, Zero U, One U} a :=
    match a with
    | nat_zero => 0
    | nat_suc a' => 1 + nat_to_abstract a'
    end.

Class Archimedean U `{Plus U, Zero U, Order U} := {
    archimedean : ∀ x y, 0 < x → 0 < y → ∃ n, x < n × y
}.

(* begin hide *)
Section NatAbstract.

Context {U} `{
    p : Plus U,
    @PlusComm U p,
    @PlusAssoc U p,
    z : Zero U,
    @PlusLid U p z,
    @PlusRid U p z,
    n1 : Neg U,
    @PlusLinv U p z n1,
    @PlusRinv U p z n1,
    m1 : Mult U,
    @MultComm U m1,
    @MultAssoc U m1,
    @Ldist U p m1,
    @Rdist U p m1,
    e : One U,
    @MultLid U m1 e,
    @MultRid U m1 e,
    @MultLcancel U z m1,
    @MultRcancel U z m1,
    o : Order U,
    @Antisymmetric U le,
    @Transitive U le,
    @Connex U le,
    @OrderLplus U p o,
    @OrderRplus U p o,
    @OrderMult U z m1 o,
    @OrderLmult U z m1 o,
    @OrderRmult U z m1 o,
    @OrderMultLcancel U z m1 o,
    @OrderMultRcancel U z m1 o,
    NotTrivial U,
    d : Div U,
    @MultLinv U z m1 e d,
    @MultRinv U z m1 e d
}.
(* end hide *)
Theorem nat_to_abstract_eq_nat : ∀ a, nat_to_abstract a = a.
Proof.
    nat_induction a.
    -   reflexivity.
    -   cbn.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat_to_abstract_zero : nat_to_abstract 0 = (zero (U := U)).
Proof.
    reflexivity.
Qed.

Theorem nat_to_abstract_one : nat_to_abstract 1 = (one (U := U)).
Proof.
    unfold one at 1; cbn.
    apply plus_rid.
Qed.

Theorem nat_to_abstract_plus : ∀ a b,
    nat_to_abstract (a + b) = nat_to_abstract a + nat_to_abstract b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite nat_to_abstract_zero.
        do 2 rewrite plus_lid.
        reflexivity.
    -   rewrite nat_plus_lsuc.
        cbn.
        rewrite IHa.
        apply plus_assoc.
Qed.

Theorem nat_to_abstract_mult : ∀ a b,
    nat_to_abstract (a * b) = nat_to_abstract a * nat_to_abstract b.
Proof.
    intros a b.
    nat_induction a.
    -   do 2 rewrite nat_to_abstract_zero.
        rewrite mult_lanni.
        reflexivity.
    -   rewrite nat_mult_lsuc.
        cbn.
        rewrite rdist.
        rewrite mult_lid.
        rewrite nat_to_abstract_plus.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat_to_abstract_mult_abstract : ∀ a b, nat_to_abstract a * b = a × b.
Proof.
    intros a b.
    nat_induction a.
    -   unfold zero; cbn.
        apply mult_lanni.
    -   cbn.
        rewrite rdist, mult_lid.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat_to_abstract_mult_one : ∀ a, a × (one (U := U)) = nat_to_abstract a.
Proof.
    nat_induction a.
    -   unfold zero, one; cbn.
        reflexivity.
    -   cbn.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat_to_abstract_pos : ∀ a, 0 < nat_to_abstract (nat_suc a).
Proof.
    nat_induction a.
    -   unfold one; cbn.
        rewrite plus_rid.
        exact one_pos.
    -   cbn.
        rewrite <- (plus_lid 0).
        apply lt_lrplus; try exact IHa.
        exact one_pos.
Qed.

Theorem nat_to_abstract_pos2 : ∀ a, 0 <= nat_to_abstract a.
Proof.
    nat_induction a.
    -   rewrite nat_to_abstract_zero.
        apply refl.
    -   apply (trans IHa).
        cbn.
        rewrite <- le_plus_0_a_b_ab.
        apply one_pos.
Qed.

Theorem nat_to_abstract_eq : ∀ a b, nat_to_abstract a = nat_to_abstract b →
    a = b.
Proof.
    nat_induction a.
    -   intros b b_eq.
        rewrite nat_to_abstract_zero in b_eq.
        nat_destruct b.
        +   reflexivity.
        +   apply nat_to_abstract_pos in b_eq.
            contradiction.
    -   intros b eq.
        nat_destruct b.
        +   rewrite nat_to_abstract_zero in eq.
            symmetry in eq.
            apply nat_to_abstract_pos in eq.
            contradiction.
        +   apply f_equal.
            apply IHa.
            cbn in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Theorem nat_to_abstract_le : ∀ a b,
    nat_to_abstract a <= nat_to_abstract b ↔ a <= b.
Proof.
    intros a b.
    split.
    -   revert b.
        nat_induction a.
        +   intros b b_ge.
            apply nat_pos.
        +   nat_destruct b.
            *   intros contr.
                rewrite nat_to_abstract_zero in contr.
                pose proof (nat_to_abstract_pos a) as ltq.
                destruct (lt_le_trans ltq contr); contradiction.
            *   intros leq.
                rewrite nat_sucs_le.
                apply IHa.
                cbn in leq.
                apply le_plus_lcancel in leq.
                exact leq.
    -   revert b.
        nat_induction a.
        +   intros b b_ge.
            rewrite nat_to_abstract_zero.
            apply nat_to_abstract_pos2.
        +   intros b b_ge.
            nat_destruct b.
            *   pose proof (nat_pos2 a) as a_pos.
                destruct (lt_le_trans a_pos b_ge); contradiction.
            *   cbn.
                apply le_lplus.
                apply IHa.
                rewrite nat_sucs_le in b_ge.
                exact b_ge.
Qed.

Theorem nat_to_abstract_lt : ∀ a b,
    nat_to_abstract a < nat_to_abstract b ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    rewrite nat_to_abstract_le.
    assert ((nat_to_abstract a ≠ nat_to_abstract b) ↔ a ≠ b) as eq.
    {
        split; intros neq eq.
        -   subst.
            contradiction.
        -   apply nat_to_abstract_eq in eq.
            contradiction.
    }
    rewrite eq.
    reflexivity.
Qed.

Theorem abstract_mult_rneg : ∀ a b, -(a × b) = a × (-b).
Proof.
    intros a b.
    nat_induction a.
    -   unfold zero; cbn.
        apply neg_zero.
    -   cbn.
        rewrite neg_plus.
        rewrite IHa.
        reflexivity.
Qed.

Let a1 := ∀ x : U, ∃ n, x < nat_to_abstract n.
Let a2 := ∀ ε, 0 < ε → ∃ n, div (nat_to_abstract (nat_suc n)) < ε.

Theorem field_impl_arch1 : a1 → Archimedean U.
Proof.
    intros arch.
    split.
    unfold a1 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    pose proof (arch (x * div y)) as [n n_lt].
    apply lt_rmult_pos with y in n_lt; try exact y_pos.
    rewrite <- mult_assoc in n_lt.
    rewrite mult_linv in n_lt by apply y_pos.
    rewrite mult_rid in n_lt.
    rewrite nat_to_abstract_mult_abstract in n_lt.
    exists n.
    exact n_lt.
Qed.

Theorem field_impl_arch2 : a2 → Archimedean U.
Proof.
    intros arch.
    split.
    unfold a2 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    assert (0 < div x) as x'_pos by (apply div_pos; exact x_pos).
    assert (0 < div x * y) as ε_pos by (apply lt_mult; assumption).
    specialize (arch _ ε_pos) as [n eq].
    pose proof (nat_to_abstract_pos n) as n_pos.
    pose proof (div_pos _ n_pos) as n'_pos.
    apply lt_div_pos in eq; try assumption.
    rewrite div_div in eq by apply n_pos.
    rewrite div_mult in eq.
    2: apply x'_pos.
    2: apply y_pos.
    rewrite div_div in eq by apply x_pos.
    apply lt_rmult_pos with y in eq; try exact y_pos.
    rewrite <- mult_assoc, mult_linv, mult_rid in eq by apply y_pos.
    rewrite nat_to_abstract_mult_abstract in eq.
    exists (nat_suc n).
    exact eq.
Qed.

Context `{@Archimedean U p z o}.

Theorem archimedean1 : a1.
Proof.
    unfold a1; clear a1 a2.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   pose proof (archimedean x 1 x_pos one_pos) as [n eq].
        exists n.
        rewrite nat_to_abstract_mult_one in eq.
        exact eq.
    -   rewrite nlt_le in x_neg.
        exists 1.
        apply (le_lt_trans x_neg).
        rewrite nat_to_abstract_one.
        exact one_pos.
Qed.

Theorem archimedean2 : a2.
Proof.
    pose proof (archimedean1) as arch.
    unfold a1, a2 in *; clear a1 a2.
    intros ε ε_pos.
    specialize (arch (div ε)) as [n eq].
    nat_destruct n.
    -   rewrite nat_to_abstract_zero in eq.
        apply div_pos in ε_pos.
        pose proof (trans ε_pos eq) as [C0 C1]; contradiction.
    -   pose proof (div_pos _ ε_pos) as ε'_pos.
        pose proof (nat_to_abstract_pos n) as n_pos.
        apply lt_div_pos in eq; try assumption.
        rewrite div_div in eq by apply ε_pos.
        exists n.
        exact eq.
Qed.

(* begin hide *)
End NatAbstract.
(* end hide *)
