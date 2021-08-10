Require Import init.

Require Export linear_base.

Require Import set.
Require Import list.
Require Import plus_sum.

Section LinearExtend.

Context {U V} `{
    VP : Plus V,
    @PlusAssoc V VP,
    @PlusComm V VP,
    VZ : Zero V,
    @PlusLid V VP VZ,
    VN : Neg V,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V
}.

Variable simple : V → Prop.
Variable mult_base : set_type simple → set_type simple → V.
Hypothesis simple_sum : ∀ v, ∃ l : list (set_type simple),
    v = list_sum (list_image l (λ x, [x|])).

Instance linear_extend_mult : Mult V := {
    mult a b := list_sum (list_prod2 mult_base
        (ex_val (simple_sum a))
        (ex_val (simple_sum b)))
}.

Lemma linear_extend_ldist : ∀ a b c, a * (b + c) = a * b + a * c.
Admitted.
Instance linear_extend_ldist_class : Ldist V := {
    ldist := linear_extend_ldist
}.
Lemma linear_extend_rdist : ∀ a b c, (a + b) * c = a * c + b * c.
Admitted.
Instance linear_extend_rdist_class : Rdist V := {
    rdist := linear_extend_rdist
}.

Theorem linear_extend_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    destruct (simple_sum a) as [al a_eq].
    destruct (simple_sum b) as [bl b_eq].
    destruct (simple_sum c) as [cl c_eq].
    subst.
    induction cl as [|c cl].
    {
        cbn.
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    cbn.
    do 3 rewrite ldist.
    rewrite IHcl; clear IHcl.
    apply rplus.
    induction bl as [|b bl].
    {
        cbn.
        rewrite mult_lanni, mult_ranni, mult_lanni.
        reflexivity.
    }
    cbn.
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHbl; clear IHbl.
    apply rplus.
    induction al as [|a al].
    {
        cbn.
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    cbn.
    do 3 rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus.
    clear al bl cl.
    destruct a as [a a_simple], b as [b b_simple], c as [c c_simple]; cbn.
    destruct (simple_sum (b * c)) as [bcl bc_eq].

End LinearExtend.
