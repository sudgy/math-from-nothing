Require Import init.

Require Import set.
Require Import zorn.

Section Preorder.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Transitive U op
}.

Local Instance preorder_order : Order U := {le := op}.

Definition preorder_eq (a b : U) := a ≤ b ∧ b ≤ a.
Local Infix "~" := preorder_eq.

Local Instance preorder_eq_reflexive : Reflexive preorder_eq.
Proof.
    split.
    intros x.
    unfold preorder_eq.
    split; apply refl.
Qed.

Local Instance preorder_eq_symmetric : Symmetric preorder_eq.
Proof.
    split.
    intros x y eq.
    unfold preorder_eq in *.
    split; apply eq.
Qed.

Local Instance preorder_eq_transitive : Transitive preorder_eq.
Proof.
    split.
    intros x y z xy yz.
    unfold preorder_eq in *.
    destruct xy as [xy yx], yz as [yz zy].
    split.
    -   exact (trans xy yz).
    -   exact (trans zy yx).
Qed.

Definition preorder_equiv := make_equiv _
    preorder_eq_reflexive preorder_eq_symmetric preorder_eq_transitive.

Lemma preorder_le_wd_1 : ∀ a b c d : U, a ~ b → c ~ d → a ≤ c → b ≤ d.
Proof.
    intros a b c d ab cd ac.
    unfold preorder_eq in *.
    destruct ab as [ab ba].
    destruct cd as [cd dc].
    apply (trans ba).
    apply (trans ac).
    exact cd.
Qed.

Lemma preorder_le_wd : ∀ a b c d : U, a ~ b → c ~ d → (a ≤ c) = (b ≤ d).
Proof.
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply preorder_le_wd_1.
    3, 4: apply preorder_eq_symmetric.
    all: assumption.
Qed.

Local Instance preorder_le : Order (equiv_type preorder_equiv) := {
    le := binary_op preorder_le_wd (E := preorder_equiv)
}.

Local Instance preorder_le_refl : Reflexive le.
Proof.
    split.
    intros x.
    equiv_get_value x.
    unfold le; equiv_simpl.
    apply refl.
Qed.

Local Instance preorder_le_antisym : Antisymmetric le.
Proof.
    split.
    intros x y.
    equiv_get_value x y.
    unfold le; equiv_simpl.
    unfold preorder_eq.
    split; assumption.
Qed.

Local Instance preorder_le_trans : Transitive le.
Proof.
    split.
    intros x y z.
    equiv_get_value x y z.
    unfold le; equiv_simpl.
    apply trans.
Qed.

Theorem preorder_zorn : (∀ F : U → Prop, is_chain le F → has_upper_bound le F) →
    ∃ a : U, ∀ x : U, a ≤ x → x ≤ a.
Proof.
    intros chain_ub.
    pose proof (zorn (U := equiv_type preorder_equiv) le) as a_ex.
    prove_parts a_ex.
    {
        intros F F_chain.
        specialize (chain_ub (λ x, F (to_equiv preorder_equiv x))).
        prove_parts chain_ub.
        {
            intros x y Fx Fy.
            specialize (F_chain _ _ Fx Fy).
            unfold le in F_chain; equiv_simpl in F_chain.
            exact F_chain.
        }
        destruct chain_ub as [a a_upper].
        exists (to_equiv preorder_equiv a).
        intros x Fx.
        equiv_get_value x.
        unfold le; equiv_simpl.
        apply a_upper.
        exact Fx.
    }
    destruct a_ex as [a a_max].
    equiv_get_value a.
    exists a.
    intros x leq.
    specialize (a_max (to_equiv preorder_equiv x)).
    unfold strict in a_max.
    rewrite not_and, not_not in a_max.
    unfold le in a_max; equiv_simpl in a_max.
    destruct a_max as [nleq|eq]; [>contradiction|].
    apply eq.
Qed.

End Preorder.
