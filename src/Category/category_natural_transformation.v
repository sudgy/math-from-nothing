Require Import init.

Require Export category_functor.

Class NatTransformation `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C1 C2) :=
{
    nat_trans_f : ∀ A,
        cat_morphism C2 (F ⌈A⌉) (G ⌈A⌉);
    nat_trans_commute : ∀ {A B} (f : cat_morphism C1 A B),
        nat_trans_f B ∘ (F ⋄ f) = (G ⋄ f) ∘ nat_trans_f A;
}.

Arguments nat_trans_f {C1 C2 F G} NatTransformation.
Arguments nat_trans_commute {C1 C2 F G} NatTransformation {A B}.

Notation "α • A" := (nat_trans_f α A) (at level 30).
(** So nat_trans_commute says:
    [(α • B) ∘ (F ⋄ f) = (G ⋄ f) ∘ (α • A)]
*)

Program Instance id_nat_transformation `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2) : NatTransformation F F :=
{
    nat_trans_f A := 𝟙
}.
Next Obligation.
    rewrite cat_lid.
    rewrite cat_rid.
    reflexivity.
Qed.

Program Instance vcompose_nat_transformation `{C1 : Category, C2 : Category}
    `{F : @Functor C1 C2, G : @Functor C1 C2, H : @Functor C1 C2}
    `(α : @NatTransformation C1 C2 G H, β : @NatTransformation C1 C2 F G)
    : NatTransformation F H :=
{
    nat_trans_f A := α • A ∘ β • A
}.
Next Obligation.
    rewrite cat_assoc.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite nat_trans_commute.
    reflexivity.
Qed.

Program Instance hcompose_nat_transformation
    `{C1 : Category, C2 : Category, C3 : Category}
    `{F' : @Functor C2 C3, G' : @Functor C2 C3}
    `{F : @Functor C1 C2, G : @Functor C1 C2}
    `(β : @NatTransformation C2 C3 F' G', α : @NatTransformation C1 C2 F G)
    : NatTransformation (F' ○ F) (G' ○ G) :=
{
    nat_trans_f A := β • (G ⌈A⌉) ∘ (F' ⋄ α • A)
}.
Next Obligation.
    rewrite nat_trans_commute.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite <- functor_compose.
    rewrite nat_trans_commute.
    rewrite functor_compose.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    reflexivity.
Qed.

Notation "α □ β" := (vcompose_nat_transformation α β) (at level 20, left associativity).
Notation "α ⊡ β" := (hcompose_nat_transformation α β) (at level 20, left associativity).

Global Remove Hints id_nat_transformation vcompose_nat_transformation hcompose_nat_transformation : typeclass_instances.
