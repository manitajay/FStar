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

/// Define actions operating on this monoid

/// Heaps are usually in a universe higher than the values they store
/// Pick it in universe 1
val heap : Type u#1 //= HS.mem

/// Assume some monoid of heap assertions
val hm : comm_monoid heap

/// For this demo, we'll also assume that this assertions are affine
///  i.e., it's ok to forget some properties of the heap
val hm_affine (r0 r1:hm.r) (h:heap)
  : Lemma (hm.interp (r0 `hm.star` r1) h ==>
           hm.interp r0 h)

/// Here's a ref type
val ref : Type u#0 -> Type u#0

/// And two atomic heap assertions
val ptr_live (r:ref 'a) : hm.r



val pts_to (r:ref 'a) (x:'a) : hm.r
//  { t = 'a; view = pts_to_view r x }

/// sel: Selected a reference from a heap, when that ref is live
val sel (x:ref 'a) (h:heap{hm.interp (ptr_live x) h})
  : Tot 'a // = HS.sel_tot h x

/// this tells us that sel is frameable
val sel_ok (x:ref 'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
           (hm_affine (ptr_live x) frame h;
            let v = sel x h in
            hm.interp (pts_to x v `hm.star` frame) h))
//  Classical.move_requires (sel_ok' x h) frame

/// upd: updates a heap at a given reference, when the heap contains it
val upd (x:ref 'a) (v:'a) (h:heap{hm.interp (ptr_live x) h})
  : Tot heap
/// and upd is frameable too
val upd_ok (x:ref 'a) (v:'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
           (hm_affine (ptr_live x) frame h;
            let h' = upd x v h in
            hm.interp (pts_to x v `hm.star` frame) h'))
#push-options "--print_universes"

/// Here's a sample action for dereference
let (!) (x:ref 'a)
  : eff 'a (ptr_live x) (fun v -> pts_to x v)
  = let act : action hm 'a =
    {
      pre = ptr_live x;
      post = pts_to x;
      sem = (fun frame h0 ->
        hm_affine (ptr_live x) frame h0;
        sel_ok x h0 frame;
        (| sel x h0, h0 |))
    } in
    Act act Ret

/// And a sample action for assignment
let (:=) (x:ref 'a) (v:'a)
  : eff unit (ptr_live x) (fun _ -> pts_to x v)
  = let act : action hm unit =
    {
      pre = ptr_live x;
      post = (fun _ -> pts_to x v);
      sem = (fun frame h0 ->
        hm_affine (ptr_live x) frame h0;
        upd_ok x v h0 frame;
        (| (), upd x v h0 |))
    } in
    Act act Ret


(*
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
*)
