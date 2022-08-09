Require Import init.

Require Import nat_abstract.
Require Import mult_characteristic.

Require Export int.
Require Import set.

Section IntAbstract.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultLid U UM UO,
    @CharacteristicZero U UP UZ UO
}.

Definition int_to_abstract_base (x : nat * nat)
    := nat_to_abstract (fst x) - nat_to_abstract (snd x).

Local Open Scope int_scope.

Theorem int_to_abstract_wd : ∀ a b, a ~ b →
    int_to_abstract_base a = int_to_abstract_base b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in eq.
    unfold int_to_abstract_base; cbn.
    rewrite <- plus_rrmove.
    rewrite (plus_comm (_ b1)).
    rewrite <- plus_assoc.
    rewrite <- plus_llmove.
    do 2 rewrite <- nat_to_abstract_plus.
    rewrite plus_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition int_to_abstract := unary_op int_to_abstract_wd.

Theorem int_to_abstract_eq : ∀ a b,
    int_to_abstract a = int_to_abstract b → a = b.
Proof.
    intros a b eq.
    equiv_get_value a b.
    unfold int_to_abstract in eq.
    equiv_simpl in eq.
    equiv_simpl.
    unfold int_to_abstract_base in eq.
    rewrite plus_comm in eq.
    rewrite <- plus_lrmove in eq.
    rewrite <- plus_assoc in eq.
    rewrite <- plus_rlmove in eq.
    do 2 rewrite <- nat_to_abstract_plus in eq.
    apply nat_to_abstract_eq in eq.
    rewrite eq.
    apply plus_comm.
Qed.

Theorem int_to_abstract_zero : int_to_abstract 0 = 0.
Proof.
    unfold zero at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    rewrite nat_to_abstract_zero.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem int_to_abstract_one : int_to_abstract 1 = 1.
Proof.
    unfold one at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    rewrite nat_to_abstract_zero, nat_to_abstract_one.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem int_to_abstract_plus : ∀ a b,
    int_to_abstract (a + b) = int_to_abstract a + int_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold plus at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    do 2 rewrite nat_to_abstract_plus.
    rewrite neg_plus.
    repeat rewrite plus_assoc.
    apply rplus.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    apply plus_comm.
Qed.

Theorem int_to_abstract_neg : ∀ a, int_to_abstract (-a) = -int_to_abstract a.
Proof.
    intros a.
    equiv_get_value a.
    unfold neg at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    rewrite plus_comm.
    rewrite neg_plus.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem int_to_abstract_mult : ∀ a b,
    int_to_abstract (a * b) = int_to_abstract a * int_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold mult at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    do 2 rewrite nat_to_abstract_plus.
    do 4 rewrite nat_to_abstract_mult.
    rewrite ldist.
    do 2 rewrite rdist.
    repeat rewrite <- plus_assoc.
    apply lplus.
    rewrite plus_comm.
    rewrite plus_assoc.
    do 2 rewrite mult_lneg.
    do 2 rewrite mult_rneg.
    rewrite neg_neg.
    apply rplus.
    rewrite plus_comm.
    rewrite neg_plus.
    reflexivity.
Qed.

Theorem nat_to_int_to_abstract : ∀ n,
    int_to_abstract (nat_to_int n) = nat_to_abstract n.
Proof.
    nat_induction n.
    -   unfold int_to_abstract, nat_to_int; equiv_simpl.
        unfold int_to_abstract_base; cbn.
        rewrite nat_to_abstract_zero.
        rewrite neg_zero.
        apply plus_lid.
    -   cbn.
        change (nat_suc n) with (1 + n).
        rewrite nat_to_int_plus.
        rewrite int_to_abstract_plus.
        rewrite IHn.
        rewrite int_to_abstract_one.
        reflexivity.
Qed.

End IntAbstract.