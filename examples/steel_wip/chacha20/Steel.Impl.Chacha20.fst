module Steel.Impl.Chacha20

open Steel.RST
open FStar.UInt32
module A = Steel.Array
module P = LowStar.Permissions

module Spec = Steel.Spec.Chacha20
open Steel.Impl.Chacha20.Core32

#reset-options " --max_fuel 0 --max_ifuel 0"

val rounds: st:state -> RST unit
  (A.array_resource st)
  (fun _ -> A.array_resource st)
  (fun h -> P.allows_write (A.get_rperm st h))
  (fun h0 _ h1 ->
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 == Spec.rounds (A.as_rseq st h0))

#set-options "--z3rlimit 10"
// #set-options "--z3cliopt smt.qi.eager_threshold=100"
// #set-options "--query_stats"

module HST = FStar.HyperStack.ST

let rounds st =
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st

val chacha20_core:
    k:state
  -> ctx0:state
  -> ctr:Spec.counter ->
  RST unit
  (A.array_resource k <*> A.array_resource ctx0)
  (fun _ -> A.array_resource k <*> A.array_resource ctx0)
  (requires fun h -> P.allows_write (A.get_rperm k h))
  (ensures  fun h0 _ h1 ->
    h0 (A.array_resource ctx0) == h1 (A.array_resource ctx0) /\
    P.allows_write (A.get_rperm k h1) /\
    A.as_rseq k h1 == Spec.chacha20_core ctr (A.as_rseq ctx0 h0))

let chacha20_core k ctx ctr =
  copy_state k ctx;
  let v = rst_frame
    (A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.index k 12ul) `UInt32.add_mod` ctr
  in
  rst_frame
    (A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.upd k 12ul v);
  rst_frame
    (A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.array_resource k <*> A.array_resource ctx)
    (fun _ -> rounds k);
  sum_state k ctx;
  let v = rst_frame
    (A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.index k 12ul) `UInt32.add_mod` ctr
  in
  rst_frame
    (A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.array_resource k <*> A.array_resource ctx)
    (fun _ -> A.upd k 12ul v)

val setup:
    st:state
  -> k:A.array UInt8.t{A.vlength k == 32}
  -> n:A.array UInt8.t{A.vlength k == 12}
  -> ctr0:Spec.counter ->
  RST unit
  (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
  (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
  (requires fun h -> P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    h0 (A.array_resource k) == h1 (A.array_resource k) /\
    h0 (A.array_resource n) == h1 (A.array_resource n) /\
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 `Seq.equal` Spec.setup (A.as_rseq k h0) (A.as_rseq n h0) ctr0 (A.as_rseq st h0))

let setup st k n ctr0 =
  rst_frame
    (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.upd st 0ul Spec.c0);
  rst_frame
    (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.upd st 1ul Spec.c1);
  rst_frame
    (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.upd st 2ul Spec.c2);
  rst_frame
    (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.upd st 3ul Spec.c3);

  let st04, st416 =
    rst_frame
      (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
      (fun v -> A.array_resource (fst v) <*> A.array_resource (snd v) <*> A.array_resource k <*> A.array_resource n)
      (fun _ -> A.split st 4ul) in
  let st48, st816 =
    rst_frame
      (A.array_resource st04 <*> A.array_resource st416 <*> A.array_resource k <*> A.array_resource n)
      (fun v -> A.array_resource (fst v) <*> A.array_resource (snd v) <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
      (fun _ -> A.split st416 4ul) in

  rst_frame
    (A.array_resource st48 <*> A.array_resource st816 <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st48 <*> A.array_resource st816 <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> uints_from_bytes_le #4 st48 k);

  rst_frame
    (A.array_resource st48 <*> A.array_resource st816 <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st416 <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.glue st416 st48 st816);

  rst_frame
    (A.array_resource st416 <*> A.array_resource st04 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.glue st st04 st416);

  rst_frame
    (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.upd st 12ul ctr0);

  let st013, st1316 =
    rst_frame
      (A.array_resource st <*> A.array_resource k <*> A.array_resource n)
      (fun v -> A.array_resource (fst v) <*> A.array_resource (snd v) <*> A.array_resource k <*> A.array_resource n)
      (fun _ -> A.split st 13ul) in

  rst_frame
    (A.array_resource st013 <*> A.array_resource st1316 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st013 <*> A.array_resource st1316 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> uints_from_bytes_le #4 st1316 n);

  rst_frame
    (A.array_resource st013 <*> A.array_resource st1316 <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.glue st st013 st1316)

val chacha20_init:
     k:A.array UInt8.t{A.vlength k == 32}
  -> n:A.array UInt8.t{A.vlength k == 12}
  -> ctr0:Spec.counter ->
  RST state
  (A.array_resource k <*> A.array_resource n)
  (fun st -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
  (requires fun h -> True)
  (ensures  fun h0 st h1 ->
    h0 (A.array_resource k) == h1 (A.array_resource k) /\
    h0 (A.array_resource n) == h1 (A.array_resource n) /\
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 == Spec.chacha20_init (A.as_rseq k h0) (A.as_rseq n h0) ctr0)

let chacha20_init k n ctr0 =
  let st = rst_frame
    (A.array_resource k <*> A.array_resource n)
    (fun st -> A.array_resource st <*> A.array_resource k <*> A.array_resource n)
    (fun _ -> A.alloc 0ul 16ul) in
  setup st k n ctr0;
  st
