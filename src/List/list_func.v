Require Import init.

Require Export list_base.

Set Implicit Arguments.

Fixpoint list_image (A B : Type) (l : list A) (f : A → B) :=
    match l with
    | list_end => list_end
    | a :: l' => f a :: list_image l' f
    end.

Theorem list_image_conc {A B : Type} : ∀ (l1 l2 : list A) (f : A → B),
        list_image (l1 ++ l2) f = list_image l1 f ++ list_image l2 f.
    intros l1 l2 f.
    induction l1.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        reflexivity.
Qed.

Theorem list_image_comp {A B C : Type} : ∀ (l : list A) (f : A → B) (g : B → C),
        list_image (list_image l f) g = list_image l (λ x, g (f x)).
    intros l f g.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl.
        reflexivity.
Qed.

Fixpoint list_prod2_base {A B : Type} (op : A → A → B) (l : list A) (b : A) :=
    match l with
    | list_end => list_end
    | a :: l' => op a b :: list_prod2_base op l' b
    end.

Fixpoint list_prod2 {A B : Type} (op : A → A → B) (l1 l2 : list A) :=
    match l2 with
    | list_end => list_end
    | b :: l2' => list_prod2_base op l1 b ++ list_prod2 op l1 l2'
    end.

Theorem list_prod2_lend {A B : Type} (op : A → A → B) (l : list A) :
        list_prod2 op list_end l = list_end.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        exact IHl.
Qed.

Theorem list_prod2_rend {A B : Type} (op : A → A → B) (l : list A) :
        list_prod2 op l list_end = list_end.
    cbn.
    reflexivity.
Qed.

Theorem list_prod2_base_image {A B} (op : A → A → B) : ∀ l b,
        list_prod2_base op l b = list_image l (λ x, op x b).
    intros l b.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl.
        reflexivity.
Qed.
