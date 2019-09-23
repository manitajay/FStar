module ParDiv.Memory

open ParDiv

open Steel.Resource
module HS = FStar.HyperStack

let equals = equal

let interp (r:resource) (h:HS.mem) = r.view.inv h

let equals_law_explicit (x1 x2 y:resource) : Lemma
  (requires x1 `equals` x2)
  (ensures (x1 <*> y) `equals` (x2 <*> y))
  = equal_refl y;
    equal_comm_monoid_cong x1 y x2 y

val interp_extensionality_explicit (x y:resource) (h:HS.mem) : Lemma
  (requires x `equals` y /\ interp x h)
  (ensures interp y h)


let lemma_laws () : Lemma
  ( symmetry equals /\ transitive equals /\ equals_law equals (<*>) /\
    associative equals (<*>) /\ commutative equals (<*>) /\ is_unit empty_resource equals (<*>) /\
    interp_extensionality equals interp
    )
  = Classical.forall_intro_2 (fun x y -> Classical.move_requires (equal_symm x) y);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equal_trans x y) z);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equals_law_explicit x y) z);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (equal_comm_monoid_associativity x y) z);
    Classical.forall_intro_2 (fun x y -> Classical.move_requires (equal_comm_monoid_commutativity x) y);
    Classical.forall_intro (equal_comm_monoid_left_unit);
    Classical.forall_intro (equal_comm_monoid_right_unit);
    Classical.forall_intro_3 (fun x y z -> Classical.move_requires (interp_extensionality_explicit x y) z)

let laws : squash
  ( symmetry equals /\ transitive equals /\ equals_law equals (<*>) /\
    associative equals (<*>) /\ commutative equals (<*>) /\ is_unit empty_resource equals (<*>) /\
    interp_extensionality equals interp
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
