Require Import init.
Require Import set.

Require Export category_functor.

Class Adjunction `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C2 C1) := {
    adj_a : ∀ {A B}, cat_morphism C2 (F ⌈A⌉) B → cat_morphism C1 A (G ⌈B⌉);
    adj_bij : ∀ A B, bijective (@adj_a A B);
    adj_nat1 : ∀ {A B C} (g : cat_morphism C2 (F ⌈A⌉) B)
                         (q : cat_morphism C2 B C),
        adj_a (q ∘ g) = (G ⋄ q) ∘ adj_a g;
    adj_b {A B} := bij_inv _ (adj_bij A B);
    adj_nat2 : ∀ {A B C} (p : cat_morphism C1 A B)
                         (f : cat_morphism C1 B (G ⌈C⌉)),
        adj_b (f ∘ p) = adj_b f ∘ (F ⋄ p);
}.

Definition adjoint `{C1 : Category, C2 : Category}
    (F : Functor C1 C2) (G : Functor C2 C1) := inhabited (Adjunction F G).

Section Adjunction.

Context `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C2 C1}.
Context `(Ad : @Adjunction C1 C2 F G).

Theorem adj_ab : ∀ {A B} (f : cat_morphism C1 A (G ⌈B⌉)), adj_a (adj_b f) = f.
    intros A B f.
    unfold adj_b.
    apply inverse_eq2.
    apply bij_inv_inv.
Qed.
Theorem adj_ba : ∀ {A B} (f : cat_morphism C2 (F ⌈A⌉) B), adj_b (adj_a f) = f.
    intros A B f.
    unfold adj_b.
    apply inverse_eq1.
    apply bij_inv_inv.
Qed.

End Adjunction.
