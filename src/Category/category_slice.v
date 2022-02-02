Require Import init.

Require Export category_base.

Require Import set.

Record morphism_to `{C0 : Category} (X : cat_U C0) := {
    morphism_to_obj : cat_U C0;
    morphism_to_f : cat_morphism C0 morphism_to_obj X;
}.

Arguments morphism_to_obj {C0} {X}.
Arguments morphism_to_f {C0} {X}.

Definition slice_set `{C0 : Category} {X : cat_U C0} (f g : morphism_to X)
    (h : cat_morphism C0 (morphism_to_obj f) (morphism_to_obj g))
    := morphism_to_f g ∘ h = morphism_to_f f.

Definition slice_set_compose `{C0 : Category} {X : cat_U C0}
    {F G H : morphism_to X}
    (f : set_type (slice_set G H)) (g : set_type (slice_set F G))
    := [f|] ∘ [g|].

Lemma slice_set_compose_in `{C0 : Category} {X : cat_U C0}
        {F G H : morphism_to X} : ∀ (f : set_type (slice_set G H)) g,
        slice_set F H (slice_set_compose f g).
    intros [f f_eq] [g g_eq].
    unfold slice_set in *.
    unfold slice_set_compose; cbn.
    rewrite cat_assoc.
    rewrite f_eq.
    exact g_eq.
Qed.

Lemma slice_set_id_in `{C0 : Category} {X : cat_U C0}
        : ∀ f : morphism_to X, slice_set f f 𝟙.
    intros f.
    unfold slice_set.
    apply cat_rid.
Qed.

(* begin show *)
Local Program Instance SLICE `(C0 : Category) (X : cat_U C0) : Category := {
    cat_U := morphism_to X;
    cat_morphism f g := set_type (slice_set f g);
    cat_compose {F G H} f g := [_|slice_set_compose_in f g];
    cat_id f := [_|slice_set_id_in f];
}.
(* end show *)
Next Obligation.
    apply set_type_eq; cbn.
    unfold slice_set_compose; cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold slice_set_compose; cbn.
    apply cat_lid.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold slice_set_compose; cbn.
    apply cat_rid.
Qed.

Record morphism_from `{C0 : Category} (X : cat_U C0) := {
    morphism_from_obj : cat_U C0;
    morphism_from_f : cat_morphism C0 X morphism_from_obj;
}.

Arguments morphism_from_obj {C0} {X}.
Arguments morphism_from_f {C0} {X}.

Definition coslice_set `{C0 : Category} {X : cat_U C0} (f g : morphism_from X)
    (h : cat_morphism C0 (morphism_from_obj f) (morphism_from_obj g))
    := h ∘ morphism_from_f f = morphism_from_f g.

Definition coslice_set_compose `{C0 : Category} {X : cat_U C0}
    {F G H : morphism_from X}
    (f : set_type (coslice_set G H)) (g : set_type (coslice_set F G))
    := [f|] ∘ [g|].

Lemma coslice_set_compose_in `{C0 : Category} {X : cat_U C0}
        {F G H : morphism_from X} : ∀ (f : set_type (coslice_set G H)) g,
        coslice_set F H (coslice_set_compose f g).
    intros [f f_eq] [g g_eq].
    unfold coslice_set in *.
    unfold coslice_set_compose; cbn.
    rewrite <- cat_assoc.
    rewrite g_eq.
    exact f_eq.
Qed.

Lemma coslice_set_id_in `{C0 : Category} {X : cat_U C0}
        : ∀ f : morphism_from X, coslice_set f f 𝟙.
    intros f.
    unfold coslice_set.
    apply cat_lid.
Qed.

Local Program Instance COSLICE `(C0 : Category) (X : cat_U C0) : Category := {
    cat_U := morphism_from X;
    cat_morphism f g := set_type (coslice_set f g);
    cat_compose {F G H} f g := [_|coslice_set_compose_in f g];
    cat_id f := [_|coslice_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    unfold coslice_set_compose; cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold coslice_set_compose; cbn.
    apply cat_lid.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold slice_set_compose; cbn.
    apply cat_rid.
Qed.
