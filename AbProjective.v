From HoTT Require Import Basics Types Pointed
  Algebra.Groups Algebra.AbGroups
  WildCat Limits.Pullback.

(** * Projective abelian groups *)

(** We define projective abelian groups and show that [P] is projective if and only if every epimorphism [A -> P] merely splits. From this it follows that [Ext P A] is trivial for all [A]. We also show that [Z] is projective. (And maybe we show that the free abelian group on a projective set is projective?) *)

(* jarl: Projective types have already been studied in Projectivity.v. Studying that file might be helpful. (You can disregard everything about modalities in that file. We're working with the "identity modality" here, so that [In O A] is a tautology). *)

(** An abelian group is [P] projective if for any map [P -> B] and epimorphism [A -> B], there merely exists a lift [P -> A] making the triangle commute. *)
(* jarl: maybe this should be a Class? *)
Definition IsAbProjective (P : AbGroup) : Type :=
  forall (A : AbGroup), forall (B : AbGroup), forall (f : P $-> B), 
  forall (e : A $-> B), IsSurjection e -> merely (exists l : P $-> A, e $o l == f).


(** An abelian group is projective iff epis into it merely split. *)
(* jarl: The WildCat library gives us handy notation like [A $-> B] for group homomorphisms and [g $o f] for composition of group homomorphisms. You could also write them out (composition is [grp_homo_compose]).  *)
Proposition iff_isabprojective_surjections_split (P : AbGroup)
  : IsAbProjective P <->
      (forall A, forall p : A $-> P,
          IsSurjection p -> merely (exists s : P $-> A, p $o s == idmap)).
Proof.
  split.
  + intros H A p H1.
    exact (H A P (grp_homo_id) p H1).
  + intro H. unfold IsAbProjective. intros A B f e H1.
    pose proof (s := H (ab_pullback f e) (grp_pullback_pr1 f e) (conn_map_pullback _ f e)).
    strip_truncations.
    destruct s as [s h].
    apply tr. exists ((grp_pullback_pr2 f e) $o s).
    intro x. refine ((pullback_commsq f e _)^ @ _).
    exact (ap f (h x)).
Defined.

(** Using [iff_ab_ext_trivial_split], show that [AbSES B A] is trivial. *)
Proposition abext_projective_trivial `{Univalence} (P : AbGroup) {proj_P : IsAbProjective P}
  : forall A, forall E : AbSES P A, tr E = point (Ext P A).
Proof.
  intros A E. rapply iff_ab_ext_trivial_split.
  exact (fst (iff_isabprojective_surjections_split P) proj_P E
           (projection E) _).
  Defined.

(** Can you show the converse? That if [forall A, forall E, tr E = point (Ext P A)] then [P] is projective. *)

Proposition abext_trivial_projective `{Univalence} (P : AbGroup) : (forall A, forall E : AbSES P A, tr E = point (Ext P A)) -> IsAbProjective P.
Proof.
  Admitted.

(* jarl: Now import this file in [Z.v] and show that [Z] is projective. *)
