From HoTT Require Import Basics Types Pointed Truncations
          Algebra.Groups Algebra.AbGroups
          Homotopy.ExactSequence WildCat WildCat.Profunctor.

Require Import BaerSumLaws.

(** * The six-term exact sequence of Ext groups *)

(** We convert our purely exact sequence to a fiber sequence, to which the tools of Homotopy/ExactSequence.v more easily apply. *)

Definition fiberseq_abses_pullback `{Univalence} {A B C : AbGroup} {E : AbSES C B}
  : FiberSeq (AbSES C A) (AbSES E A) (AbSES B A)
  := fiberseq_isexact_purely
       (abses_pullback_pmap (A:=A) (projection E))
       (abses_pullback_pmap (inclusion E)).

(** Thus [Pi_les] gives the six-term exact sequence. We need to identify the maps. *)

(** todo: place in AbSES/Pullback.v *)
Definition abses_pullback_point `{Univalence} {A B B' : AbGroup} (f : B' $-> B)
  : abses_pullback f (point _) = point (AbSES B' A)
  := equiv_path_abses_iso (abses_pullback_point' f).

(** The functorial action of [abses_pullback_pmap] on loops. *)
Definition abses_loops_pullback_data `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : forall p, fmap loops (abses_pullback_pmap (A:=A) g) p
         = equiv_path_abses_iso
             ((abses_pullback_point' g)^$
                $@ (fmap (abses_pullback g) (equiv_path_abses_iso^-1 p)
                      $@ abses_pullback_point' g)).
Proof.
  intro p.
  refine (_ @ abses_path_data_compose_beta _ _).
  refine (_ @ ap011 _ (abses_path_data_V _) (abses_path_data_compose_beta _ _)).
  apply whiskerL.
  apply whiskerR.
  apply ap_abses_pullback.
Defined.

(** The inverse of [loops_abses]. *)
Definition loops_abses_inv `{Univalence} {A B : AbGroup}
  : loops (AbSES B A) <~> (B $-> A)
  := abses_endomorphism_trivial oE equiv_path_abses^-1.

(** Loop spaces of a 1-truncated type are automatically groups. *)
Definition loops_1trunc (X : pType) `{IsTrunc 1 X} : Group.
Proof.
  nrefine (Build_Group (loops X) concat idpath inverse _).
  nrapply Build_IsGroup; repeat split.
  - by apply istrunc_paths.
  - rapply concat_p_pp.
  - rapply concat_1p.
  - rapply concat_p1.
  - rapply concat_Vp.
  - rapply concat_pV.
Defined.

(** [loops_abses_inv] is a group homomorphism *)
Definition iso_loops_abses `{Univalence} {A B : AbGroup@{u}}
  : GroupIsomorphism
      (loops_1trunc@{v} (AbSES@{v u u u u u} B A))
      (ab_hom@{u v w} B A).
Proof.
  snrapply Build_GroupIsomorphism'.
  1: apply loops_abses_inv.
  unfold IsSemiGroupPreserving.
  (* We reformulate the equation in terms of path data. *)
  rapply (equiv_ind equiv_path_abses_iso); intros [p [p0 p1]].
  rapply (equiv_ind equiv_path_abses_iso); intros [q [q0 q1]].
  refine (ap loops_abses_inv _ @ _ @ ap011 sg_op _ _); only 3,4: symmetry.
  1: apply abses_path_data_compose_beta.
  all: refine (ap _ (equiv_inverse_compose _ _ _) @ _).
  all: nrefine (ap (abses_endomorphism_trivial o _^-1) (eissect _ _) @ _).
  2,3: reflexivity.
  apply equiv_path_grouphomomorphism; intro b; cbn.
  refine (ap fst _ @ _).
  { refine (ap q _ @ _).
    { refine (ab_biprod_decompose _ _ @ _).
      refine (ap (fun x => sg_op _ x) _).
      exact (ap (fun x => (_, x)) (p1 _)^). }
    refine (grp_homo_op _ _ _ @ ap (fun x => sg_op x _) _).
    apply q0. }
  reflexivity.
Defined.

(** Under the equivalence [loops_abses], [fmap loops (abses_pullback g)] corresponds to precomposition by [g]. *)
Definition abses_loops_pullback `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : loops_abses_inv o fmap loops (abses_pullback_pmap (A:=A) g)
    == (fun f => f $o g) o loops_abses_inv.
Proof.
  intro phi; unfold loops_abses_inv.
  refine (ap abses_endomorphism_trivial _
            (x:=equiv_path_abses^-1%equiv (fmap loops _ phi))
            @ _).
  { refine (ap _ (abses_loops_pullback_data _ _) @ _).
    refine (equiv_inverse_compose _ _ _ @ _).
    exact (ap _ (eissect _ _)). }
  by apply equiv_path_grouphomomorphism.
Defined.


(** ** The six-term exact sequence *)

(** Given a short exact sequence [B -> E -> C] and an abelian group [A], we show exactness at all points of the associated six-term exact sequence. *)

(* Place in Groups/Group.v? *)
Definition pequiv_groupisomorphism {A B : Group}
  : GroupIsomorphism A B -> (A <~>* B)
  := fun phi => Build_pEquiv _ _ phi _.

Coercion pequiv_groupisomorphism : GroupIsomorphism >-> pEquiv.


From HoTT Require Import Modalities.ReflectiveSubuniverse Modalities.Identity.

(* Place in Homotopy/ExactSequence.v *)
(** A purely exact sequence is [O]-exact for any modality [O]. *)
Definition isexact_purely_O {O : Modality} {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely _ _ _ i f}
  : IsExact O i f.
Proof.
  srapply Build_IsExact.
  1: apply cx_isexact.
  exact _.
Defined.

(* jarl: The exact sequence [ab_hom C A $-> ab_hom E A $-> ab_hom B A] lives in the base universe, whereas the exact sequence coming from [loops [AbSES ? ?)] lives in a higher universe. Unforunately, [isexact_square_if] doesn't let the two fiber sequences live in separate universes (though maybe one could change it to allow for that). Instead, we've made [ab_hom] polymorphic so that it spits out an abelian group in whatever higher universe we need. *)

(** The sequence [ab_hom C A $-> ab_hom E A $-> ab_hom B A] is exact. *)
(* jarl: This definitely needs a clea *)
Definition abses_sixterm_1 `{Univalence} {A B C: AbGroup} (E : AbSES C B)
  : IsExact (Tr (-1))
      (fmap10 ab_hom@{u _ w} (projection E) A)
      (fmap10 ab_hom (inclusion E) A).
Proof.
  snrapply isexact_square_if.
  - exact (loops_1trunc (AbSES C A)).
  - exact (loops_1trunc (AbSES E A)).
  - exact (loops_1trunc (AbSES B A)).
  - exact (fmap loops (abses_pullback_pmap (projection E))).
  - exact (fmap loops (abses_pullback_pmap (inclusion E))).
  - symmetry; exact iso_loops_abses.
  - symmetry; exact iso_loops_abses.
  - symmetry; exact iso_loops_abses.
    (* jarl: Factor this out as a lemma or prove it instead of [abses_loops_pullback]. *)
  - nrapply moveR_pequiv_Vf.
    refine (_ @* pmap_compose_assoc _ _ _).
    (* todo: This function is incorrectly named! It should be [moveL_pequiv_fV]. *)
    nrapply moveR_pequiv_fV.
    apply phomotopy_homotopy_hset; intro phi.
    exact (abses_loops_pullback _ phi)^.
  - nrapply moveR_pequiv_Vf.
    refine (_ @* pmap_compose_assoc _ _ _).
    nrapply moveR_pequiv_fV. (* todo: incorrectly named! *)
    apply phomotopy_homotopy_hset; intro phi.
    exact (abses_loops_pullback _ phi)^.
  - apply isexact_purely_O.
    apply isexact_loops.
    exact _.
Defined.
