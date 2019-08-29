module Steel.Impl.Chacha20.Core32

open Steel.RST
open FStar.UInt32
module A = Steel.Array
module P = LowStar.Permissions

module Spec = Steel.Spec.Chacha20

let state = b:A.array t{A.vlength b == 16}
let index = i:UInt32.t{v i < 16}
let size = Spec.size

val create_state: unit -> RST state
  (empty_resource)
  (fun st -> A.array_resource st)
  (fun _ -> True)
  (fun _ st h1 ->
      A.freeable st /\
      A.as_rseq st h1 == Seq.create 16 0ul /\
      A.get_rperm st h1 = FStar.Real.one)

let create_state () = A.alloc 0ul 16ul

val line:
  st:state
  -> a:index
  -> b:index
  -> d:index
  -> r:Spec.rotval ->
  RST unit
    (A.array_resource st)
    (fun _ -> A.array_resource st)
    (requires fun h0 -> v a <> v d /\ P.allows_write (A.get_rperm st h0))
    (ensures fun h0 _ h1 ->
      P.allows_write (A.get_rperm st h1) /\
      A.as_rseq st h1 == Spec.line (v a) (v b) (v d) r (A.as_rseq st h0))

#set-options " --max_fuel 0 --max_ifuel 0"
//#set-options "--z3cliopt smt.qi.eager_threshold=1000"

let line st a b d r =
  let sta = A.index st a in
  let stb = A.index st b in
  let std = A.index st d in
  let sta = sta `add_mod` stb in
  let std = std `logxor` sta in
  let std = Spec.rotate_left std r in
  A.upd st a sta;
  A.upd st d std

val quarter_round:
    st:state
  -> a:index
  -> b:index
  -> c:index
  -> d:index ->
  RST unit
  (A.array_resource st)
  (fun _ -> A.array_resource st)
  (requires fun h -> v a <> v d /\ v c <> v b /\
    P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 == Spec.quarter_round (v a) (v b) (v c) (v d) (A.as_rseq st h0))


let quarter_round st a b c d =
  line st a b d (size 16);
  line st c d b (size 12);
  line st a b d (size 8);
  line st c d b (size 7)


val double_round:
  st:state ->
  RST unit
  (A.array_resource st)
  (fun _ -> A.array_resource st)
  (requires fun h -> P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 == Spec.double_round (A.as_rseq st h0))

#set-options "--z3rlimit 10"

let double_round st =
  quarter_round st (size 0) (size 4) (size 8) (size 12);
  quarter_round st (size 1) (size 5) (size 9) (size 13);
  quarter_round st (size 2) (size 6) (size 10) (size 14);
  quarter_round st (size 3) (size 7) (size 11) (size 15);

  quarter_round st (size 0) (size 5) (size 10) (size 15);
  quarter_round st (size 1) (size 6) (size 11) (size 12);
  quarter_round st (size 2) (size 7) (size 8) (size 13);
  quarter_round st (size 3) (size 4) (size 9) (size 14)

val sum_state:
    st:state
  -> ost:state ->
  RST unit
  (A.array_resource st <*> A.array_resource ost)
  (fun _ -> A.array_resource st <*> A.array_resource ost)
  (requires fun h -> P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    h0 (A.array_resource ost) == h1 (A.array_resource ost) /\
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 `Seq.equal` Spec.sum_state (A.as_rseq st h0) (A.as_rseq ost h0))

#set-options "--z3rlimit 70"
// This is needed to conclude about RST.modifies. This will disappear with effect layering
#set-options "--z3cliopt smt.qi.eager_threshold=1000"

let sum_state st ost =
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 0ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 0ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 0ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 1ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 1ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 1ul v);

  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 2ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 2ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 2ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 3ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 3ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 3ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 4ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 4ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 4ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 5ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 5ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 5ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 6ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 6ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 6ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 7ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 7ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 7ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 8ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 8ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 8ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 9ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 9ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 9ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 10ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 10ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 10ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 11ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 11ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 11ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 12ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 12ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 12ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 13ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 13ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 13ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 14ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 14ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 14ul v);
  let v1 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index st 15ul) in
  let v2 = rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.index ost 15ul) in
  let v = add_mod v1 v2 in
  rst_frame
    (A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.array_resource st <*> A.array_resource ost)
    (fun _ -> A.upd st 15ul v)
