Require Import init.

Require Export list_base.

Set Implicit Arguments.

Fixpoint list_image (A B : Type) (l : list A) (f : A → B) :=
    match l with
    | [] => []
    | a :: l' => f a :: list_image l' f
    end.
Arguments list_image : simpl never.

Theorem list_image_end {A B : Type} : ∀ (f : A → B), list_image [] f = [].
Proof.
    reflexivity.
Qed.

Theorem list_image_add {A B : Type} : ∀ a l (f : A → B),
    list_image (a :: l) f = f a :: list_image l f.
Proof.
    reflexivity.
Qed.

Theorem list_image_single {A B : Type} : ∀ a (f : A → B),
    list_image [a] f = [f a].
Proof.
    reflexivity.
Qed.

Theorem list_image_conc {A B : Type} : ∀ (l1 l2 : list A) (f : A → B),
    list_image (l1 ++ l2) f = list_image l1 f ++ list_image l2 f.
Proof.
    intros l1 l2 f.
    induction l1.
    -   rewrite list_image_end.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_image_add.
        rewrite IHl1.
        rewrite list_conc_add.
        reflexivity.
Qed.

Theorem list_image_comp {A B C : Type} : ∀ (l : list A) (f : A → B) (g : B → C),
    list_image (list_image l f) g = list_image l (λ x, g (f x)).
Proof.
    intros l f g.
    induction l.
    -   do 2 rewrite list_image_end.
        reflexivity.
    -   do 3 rewrite list_image_add.
        rewrite IHl.
        reflexivity.
Qed.

Fixpoint list_prod2 {A B : Type} (op : A → A → B) (l1 l2 : list A) :=
    match l2 with
    | [] => []
    | b :: l2' => list_image l1 (λ x, op x b) ++ list_prod2 op l1 l2'
    end.
Arguments list_prod2 : simpl never.

Theorem list_prod2_rend {A B : Type} (op : A → A → B) : ∀ (l : list A),
    list_prod2 op l [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_prod2_radd {A B : Type} (op : A → A → B) : ∀ a (l1 l2 : list A),
    list_prod2 op l1 (a :: l2) =
    list_image l1 (λ x, op x a) ++ list_prod2 op l1 l2.
Proof.
    reflexivity.
Qed.

Theorem list_prod2_lend {A B : Type} (op : A → A → B) (l : list A) :
    list_prod2 op [] l = [].
Proof.
    induction l.
    -   apply list_prod2_rend.
    -   rewrite list_prod2_radd.
        rewrite IHl.
        rewrite list_image_end.
        apply list_conc_lid.
Qed.
