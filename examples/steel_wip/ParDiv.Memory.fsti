module ParDiv.Memory

open ParDiv

open Steel.Resource
module HS = FStar.HyperStack

(* Instantiate the commutative monoid with steel resources *)

let equals = equal

let interp (r:resource) (h:HS.mem) = r.view.inv h

let equals_law_explicit (x1 x2 y:resource) : Lemma
  (requires x1 `equals` x2)
  (ensures (x1 <*> y) `equals` (x2 <*> y))
  = equal_refl y;
    equal_comm_monoid_cong x1 y x2 y

let interp_star_explicit (x1 x2:resource) (h:HS.mem) : Lemma
  (requires interp (x1 <*> x2) h)
  (ensures interp x1 h /\ interp x2 h)
  = reveal_star_inv x1 x2 h

val interp_extensionality_explicit (x y:resource) (h:HS.mem) : Lemma
  (requires x `equals` y /\ interp x h)
  (ensures interp y h)


let lemma_laws () : Lemma
  ( symmetry equals /\ transitive equals /\ equals_law equals (<*>) /\
    associative equals (<*>) /\ commutative equals (<*>) /\ is_unit empty_resource equals (<*>) /\
    interp_star (<*>) interp /\ interp_extensionality equals interp
    )
  = Classical.forall_intro_2 (fun x y -> Classical.move_requires (equal_symm x) y);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equal_trans x y) z);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equals_law_explicit x y) z);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equal_comm_monoid_associativity x y) z);
    Classical.forall_intro_2 (fun x y -> Classical.move_requires (equal_comm_monoid_commutativity x) y);
    Classical.forall_intro (equal_comm_monoid_left_unit);
    Classical.forall_intro (equal_comm_monoid_right_unit);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (interp_star_explicit x y) z);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (interp_extensionality_explicit x y) z)

let laws : squash
  ( symmetry equals /\ transitive equals /\ equals_law equals (<*>) /\
    associative equals (<*>) /\ commutative equals (<*>) /\ is_unit empty_resource equals (<*>) /\
    interp_star (<*>) interp /\ interp_extensionality equals interp
    )
 =
  lemma_laws();
  FStar.Squash.get_proof
  ( symmetry equals /\ transitive equals /\ equals_law equals (<*>) /\
    associative equals (<*>) /\ commutative equals (<*>) /\ is_unit empty_resource equals (<*>) /\
    interp_extensionality equals interp
    )

let res_monoid : comm_monoid HS.mem =
  { r = resource;
    equals = equals;
    emp = empty_resource;
    star = (<*>) ;
    interp = interp;
    laws = laws }

(* Define actions operating on this monoid *)
// AF: Should we just consider functions from Steel.Array as actions?
// And build purely out of them?

let get (#a:Type) (#rel:Preorder.preorder a) (s:HS.mreference a rel)
  (r:resource{forall h. r.view.inv h ==> h `HS.contains` s})
  : action res_monoid a =
    let sem (h:HS.mem{r.view.inv h}) : (a * HS.mem) = HS.sel_tot h s, h in
  { sem = sem;
    pre = r;
    post = (fun _ -> r);
    action_ok = (fun _ -> ());
    action_frame = (fun _ _ -> ()) }

let put (#a:Type) (#rel:Preorder.preorder a) (s:HS.mreference a rel)
  (pre_r:resource{forall h. pre_r.view.inv h ==> h `HS.contains` s})
  (post_r:resource) : action res_monoid unit
  = admit()
