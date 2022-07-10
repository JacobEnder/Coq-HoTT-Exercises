From HoTT Require Import HFiber Algebra.Groups Algebra.AbGroups.

(* Given a group [G], we define centralizer of an element [g : G] as a subgroup and use this to show that the cyclic subgroup generated by [g] is abelian. *)

Open Scope mc_mult_scope.

(* First we show that the collection of elements that commute with a fixed element [g] is a subgroup. *)

Definition centralizer {G : Group} (g : G)
  := fun h => g * h = h * g.

Definition centralizer_unit {G : Group} (g : G) : centralizer g mon_unit.
Proof.
  exact (grp_unit_r _ @ (grp_unit_l _)^).
Defined.

Definition centralizer_sgop {G : Group} (g h k : G)
           (p : centralizer g h) (q : centralizer g k)
  : centralizer g (h * k).
Proof.
  refine (grp_assoc _ _ _ @ _).
  refine (ap (fun x => x * k) p @ _).
  refine ((grp_assoc _ _ _)^ @ _).
  refine (ap (fun x => h * x) q @ _).
  apply grp_assoc.
Defined.

Definition centralizer_inverse {G : Group} (g h : G)
           (p : centralizer g h)
  : centralizer g (-h).
Proof.
  unfold centralizer in *.
  symmetry.
  refine ((grp_unit_r _)^ @ _ @ grp_unit_l _).
  refine (ap (fun x => (-h * g * x)) (grp_inv_r h)^ @ _ @ ap (fun x => x * (g * -h)) (grp_inv_l h)).
  refine (grp_assoc _ _ _ @ _ @ (grp_assoc _ _ _)^).
  refine (ap (fun x => x * (-h)) _).
  refine ((grp_assoc _ _ _)^ @ _ @ grp_assoc _ _ _).
  exact (ap (fun x => (-h) * x) p).
Defined.

Global Instance issubgroup_centralizer {G : Group} (g : G)
  : IsSubgroup (centralizer g).
Proof.
  srapply Build_IsSubgroup.
  - apply centralizer_unit.
  - apply centralizer_sgop.
  - apply centralizer_inverse.
Defined.

Definition centralizer_subgroup {G : Group} (g : G)
  := Build_Subgroup G (centralizer g) _.

Definition cyclic_subgroup {G : Group} (g : G) := subgroup_generated (fun h => g = h).

Global Instance commutative_cyclic_subgroup {G : Group} (g : G)
  : Commutative (@group_sgop (cyclic_subgroup g)).
Proof.
  intros h k.
  destruct h as [h H]; cbn in H.
  destruct k as [k K]; cbn in K.
  strip_truncations.
  (* It's enough to check equality after including into G: *)
  apply (equiv_ap_isembedding (subgroup_incl _) _ _)^-1.  cbn.
  induction H as [h p| |h1 h2 H1 H2 IHH1 IHH2].
  - (* The case when h = g: *)
    induction p.
    induction K as [k q| |k1 k2 K1 K2 IHK1 IHK2].
    + (* The case when k = g: *)
      induction q.
      reflexivity.
    + (* The case when k = mon_unit: *)
      apply centralizer_unit.
    + (* The case when k = k1 (-k2): *)
      srapply (issubgroup_in_op_inv (H:=centralizer g)); assumption.
  - (* The case when h = mon_unit: *)
    symmetry; apply centralizer_unit.
  - (* The case when h = h1 (-h2): *)
    symmetry.
    srapply (issubgroup_in_op_inv (H:=centralizer k)); unfold centralizer; symmetry; assumption.
Defined.

Definition abgroup_cyclic_subgroup {G : Group} (g : G) : AbGroup
  := Build_AbGroup (cyclic_subgroup g) _.
