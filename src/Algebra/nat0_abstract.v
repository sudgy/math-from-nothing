Require Import init.

Require Export plus.
Require Export mult.
Require Export relation.
Require Import order_mult.
Require Export nat0.

Fixpoint abstract_mult {U} `{Plus U, Zero U} (a : nat0) (b : U) :=
    match a with
    | nat0_zero => 0
    | nat0_suc a' => b + abstract_mult a' b
    end.

Infix "×" := abstract_mult (at level 40, left associativity).

Fixpoint abstract_pow {U} `{Mult U, One U} (a : U) (b : nat0) :=
    match b with
    | nat0_zero => 1
    | nat0_suc b' => b * abstract_pow a b'
    end.

Infix "^" := abstract_pow.

Fixpoint nat0_to_abstract {U} `{Plus U, Zero U, One U} a :=
    match a with
    | nat0_zero => 0
    | nat0_suc a' => 1 + nat0_to_abstract a'
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
    @NotTrivial U z e,
    d : Div U,
    @MultLinv U z m1 e d,
    @MultRinv U z m1 e d
}.
(* end hide *)

Theorem nat0_to_abstract_eq : ∀ a, nat0_to_abstract a = a.
    nat0_induction a.
    -   reflexivity.
    -   cbn.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat0_to_abstract_zero : nat0_to_abstract 0 = (zero (U := U)).
    reflexivity.
Qed.

Theorem nat0_to_abstract_one : nat0_to_abstract 1 = (one (U := U)).
    unfold one at 1; cbn.
    apply plus_rid.
Qed.

Theorem nat0_to_abstract_mult : ∀ a b, nat0_to_abstract a * b = a × b.
    intros a b.
    nat0_induction a.
    -   unfold zero; cbn.
        apply mult_lanni.
    -   cbn.
        rewrite rdist, mult_lid.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat0_to_abstract_mult_one: ∀ a, a × (one (U := U)) = nat0_to_abstract a.
    nat0_induction a.
    -   unfold zero, one; cbn.
        reflexivity.
    -   cbn.
        rewrite IHa.
        reflexivity.
Qed.

Theorem nat0_to_abstract_pos : ∀ a, 0 < nat0_to_abstract (nat0_suc a).
    nat0_induction a.
    -   unfold one; cbn.
        rewrite plus_rid.
        exact one_pos.
    -   cbn.
        rewrite <- (plus_lid 0).
        apply lt_lrplus; try exact IHa.
        exact one_pos.
Qed.

Theorem abstract_mult_rneg : ∀ a b, -(a × b) = a × (-b).
    intros a b.
    nat0_induction a.
    -   unfold zero; cbn.
        apply neg_zero.
    -   cbn.
        rewrite neg_plus.
        rewrite IHa.
        reflexivity.
Qed.

Let a1 := ∀ x : U, ∃ n, x < nat0_to_abstract n.
Let a2 := ∀ ε, 0 < ε → ∃ n, div (nat0_to_abstract (nat0_suc n)) < ε.

Theorem field_impl_arch1 : a1 → Archimedean U.
    intros arch.
    split.
    unfold a1 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    pose proof (arch (x * div y)) as [n n_lt].
    apply lt_rmult_pos with y in n_lt; try exact y_pos.
    rewrite <- mult_assoc in n_lt.
    rewrite mult_linv in n_lt by apply y_pos.
    rewrite mult_rid in n_lt.
    rewrite nat0_to_abstract_mult in n_lt.
    exists n.
    exact n_lt.
Qed.

Theorem field_impl_arch2 : a2 → Archimedean U.
    intros arch.
    split.
    unfold a2 in arch; clear a1 a2.
    intros x y x_pos y_pos.
    assert (0 < div x) as x'_pos by (apply div_pos; exact x_pos).
    assert (0 < div x * y) as ε_pos by (apply lt_mult; assumption).
    specialize (arch _ ε_pos) as [n eq].
    pose proof (nat0_to_abstract_pos n) as n_pos.
    pose proof (div_pos _ n_pos) as n'_pos.
    apply lt_div_pos in eq; try assumption.
    rewrite div_div in eq by apply n_pos.
    rewrite div_mult in eq.
    2: apply x'_pos.
    2: apply y_pos.
    rewrite div_div in eq by apply x_pos.
    apply lt_rmult_pos with y in eq; try exact y_pos.
    rewrite <- mult_assoc, mult_linv, mult_rid in eq by apply y_pos.
    rewrite nat0_to_abstract_mult in eq.
    exists (nat0_suc n).
    exact eq.
Qed.

Context `{@Archimedean U p z o}.

Theorem archimedean1 : a1.
    unfold a1; clear a1 a2.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   pose proof (archimedean x 1 x_pos one_pos) as [n eq].
        exists n.
        rewrite nat0_to_abstract_mult_one in eq.
        exact eq.
    -   rewrite nlt_le in x_neg.
        exists 1.
        apply (le_lt_trans x_neg).
        rewrite nat0_to_abstract_one.
        exact one_pos.
Qed.

Theorem archimedean2 : a2.
    pose proof (archimedean1) as arch.
    unfold a1, a2 in *; clear a1 a2.
    intros ε ε_pos.
    specialize (arch (div ε)) as [n eq].
    nat0_destruct n.
    -   rewrite nat0_to_abstract_zero in eq.
        apply div_pos in ε_pos.
        pose proof (trans ε_pos eq) as [C0 C1]; contradiction.
    -   pose proof (div_pos _ ε_pos) as ε'_pos.
        pose proof (nat0_to_abstract_pos n) as n_pos.
        apply lt_div_pos in eq; try assumption.
        rewrite div_div in eq by apply ε_pos.
        exists n.
        exact eq.
Qed.

(* begin hide *)
End NatAbstract.
(* end hide *)
