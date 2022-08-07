Require Import init.
Require Import set.

Require Export category_functor.
Require Import category_natural_transformation.

Class Adjunction `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C2 C1) := {
    adj_a : ∀ {A B}, cat_morphism C2 (F ⌈A⌉) B → cat_morphism C1 A (G ⌈B⌉);
    adj_bij : ∀ A B, bijective (@adj_a A B);
    adj_b {A B} := bij_inv _ (adj_bij A B);
    adj_nat1 : ∀ {A B C} (g : cat_morphism C2 (F ⌈A⌉) B)
                         (q : cat_morphism C2 B C),
        adj_a (q ∘ g) = (G ⋄ q) ∘ adj_a g;
    adj_nat2 : ∀ {A B C} (p : cat_morphism C1 A B)
                         (f : cat_morphism C1 B (G ⌈C⌉)),
        adj_b (f ∘ p) = adj_b f ∘ (F ⋄ p);
}.

Arguments adj_a {C1 C2 F G} Adjunction {A B}.
Arguments adj_b {C1 C2 F G} Adjunction {A B}.

Definition adjoint `{C1 : Category, C2 : Category}
    (F : Functor C1 C2) (G : Functor C2 C1) := inhabited (Adjunction F G).

Notation "F ⊣ G" := (adjoint F G) (at level 70, no associativity).

Section Adjunction.

Context `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C2 C1}.
Context `(Ad : @Adjunction C1 C2 F G).

Theorem adj_ab : ∀ {A B} (f : cat_morphism C1 A (G ⌈B⌉)), adj_a Ad (adj_b Ad f) = f.
Proof.
    intros A B f.
    unfold adj_b.
    apply inverse_eq2.
    apply bij_inv_inv.
Qed.
Theorem adj_ba : ∀ {A B} (f : cat_morphism C2 (F ⌈A⌉) B), adj_b Ad (adj_a Ad f) = f.
Proof.
    intros A B f.
    unfold adj_b.
    apply inverse_eq1.
    apply bij_inv_inv.
Qed.

End Adjunction.

Local Program Instance compose_adjunction
    `{C1 : Category, C2 : Category, C3 : Category}
    `{F  : @Functor C1 C2, G  : @Functor C2 C1}
    `{F' : @Functor C2 C3, G' : @Functor C3 C2}
    `(A1 : @Adjunction C1 C2 F G, A2 : @Adjunction C2 C3 F' G')
    : Adjunction (F' ○ F) (G ○ G') :=
{
    adj_a {A B} (f : cat_morphism C3 (F' ⌈F ⌈A⌉⌉) B)
        := adj_a A1 (adj_a A2 f);
}.
Next Obligation.
    apply bij_comp; apply adj_bij.
Qed.
Next Obligation.
    do 2 rewrite adj_nat1.
    reflexivity.
Qed.
Next Obligation.
    unfold bij_inv.
    rewrite_ex_val a a_inv.
    rewrite_ex_val b b_inv.
    assert (a = (λ f, adj_b A2 (adj_b A1 f))) as a_eq.
    {
        apply functional_ext.
        intros g.
        pose proof (inverse_eq2 _ _ a_inv g) as eq.
        cbn in eq.
        apply (f_equal (adj_b A1)) in eq.
        apply (f_equal (adj_b A2)) in eq.
        do 2 rewrite adj_ba in eq.
        exact eq.
    }
    assert (b = (λ f, adj_b A2 (adj_b A1 f))) as b_eq.
    {
        apply functional_ext.
        intros g.
        pose proof (inverse_eq2 _ _ b_inv g) as eq.
        cbn in eq.
        apply (f_equal (adj_b A1)) in eq.
        apply (f_equal (adj_b A2)) in eq.
        do 2 rewrite adj_ba in eq.
        exact eq.
    }
    subst a b.
    do 2 rewrite adj_nat2.
    reflexivity.
Qed.

Local Program Instance adj_unit `{C1 : Category, C2 : Category}
    `{F : @Functor C1 C2, G : @Functor C2 C1}
    `(Ad : @Adjunction C1 C2 F G) : NatTransformation 𝟏 (G ○ F) :=
{
    nat_trans_f A := adj_a Ad 𝟙;
}.
Next Obligation.
    rewrite <- adj_nat1.
    rewrite cat_rid.
    rewrite <- (adj_ab Ad (adj_a Ad 𝟙 ∘ f)).
    rewrite adj_nat2.
    rewrite adj_ba.
    rewrite cat_lid.
    reflexivity.
Qed.
Local Program Instance adj_counit `{C1 : Category, C2 : Category}
    `{F : @Functor C1 C2, G : @Functor C2 C1}
    `(Ad : @Adjunction C1 C2 F G) : NatTransformation (F ○ G) 𝟏 :=
{
    nat_trans_f A := adj_b Ad 𝟙;
}.
Next Obligation.
    rewrite <- adj_nat2.
    rewrite cat_lid.
    rewrite <- (adj_ba Ad (f ∘ adj_b Ad 𝟙)).
    rewrite adj_nat1.
    rewrite adj_ab.
    rewrite cat_rid.
    reflexivity.
Qed.
