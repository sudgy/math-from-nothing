Require Import init.

Require Export list_base.

Set Implicit Arguments.

Fixpoint list_image (A B : Type) (l : list A) (f : A → B) :=
    match l with
    | list_end => list_end
    | a :: l' => f a :: list_image l' f
    end.
Arguments list_image : simpl never.

Theorem list_image_end {A B : Type} : ∀ (f : A → B),
    list_image list_end f = list_end.
Proof.
    reflexivity.
Qed.

Theorem list_image_add {A B : Type} : ∀ a l (f : A → B),
    list_image (a :: l) f = f a :: list_image l f.
Proof.
    reflexivity.
Qed.

Theorem list_image_single {A B : Type} : ∀ a (f : A → B),
    list_image (a :: list_end) f = f a :: list_end.
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
Arguments list_prod2_base : simpl never.
Arguments list_prod2 : simpl never.

Theorem list_prod2_base_end {A B} (op : A → A → B) : ∀ a,
    list_prod2_base op list_end a = list_end.
Proof.
    reflexivity.
Qed.

Theorem list_prod2_base_add {A B} (op : A → A → B) : ∀ a b l,
    list_prod2_base op (b :: l) a = op b a :: list_prod2_base op l a.
Proof.
    reflexivity.
Qed.

Theorem list_prod2_rend {A B : Type} (op : A → A → B) : ∀ (l : list A),
    list_prod2 op l list_end = list_end.
Proof.
    reflexivity.
Qed.

Theorem list_prod2_radd {A B : Type} (op : A → A → B) : ∀ a (l1 l2 : list A),
    list_prod2 op l1 (a :: l2) = list_prod2_base op l1 a ++ list_prod2 op l1 l2.
Proof.
    reflexivity.
Qed.

Theorem list_prod2_lend {A B : Type} (op : A → A → B) (l : list A) :
    list_prod2 op list_end l = list_end.
Proof.
    induction l.
    -   apply list_prod2_rend.
    -   rewrite list_prod2_radd.
        rewrite IHl.
        rewrite list_prod2_base_end.
        apply list_conc_lid.
Qed.

Theorem list_prod2_base_image {A B} (op : A → A → B) : ∀ l b,
    list_prod2_base op l b = list_image l (λ x, op x b).
Proof.
    intros l b.
    induction l.
    -   rewrite list_prod2_base_end, list_image_end.
        reflexivity.
    -   rewrite list_prod2_base_add, list_image_add.
        apply f_equal.
        exact IHl.
Qed.

Fixpoint rfold {U} (op : U → U → U) (init : U) (l : list U) :=
    match l with
    | list_end => init
    | a :: l' => op a (rfold op init l')
    end.
Arguments rfold : simpl never.

Theorem rfold_end {U} (op : U → U → U) init : rfold op init list_end = init.
Proof.
    reflexivity.
Qed.

Theorem rfold_add {U} (op : U → U → U) init : ∀ a l,
    rfold op init (a :: l) = op a (rfold op init l).
Proof.
    reflexivity.
Qed.
