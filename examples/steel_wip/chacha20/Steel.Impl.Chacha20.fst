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

let rounds st =
  let h0 = get (A.array_resource st) in
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  let h1 = get (A.array_resource st) in
  assert (P.allows_write (A.get_rperm st h1));
  assert (A.as_rseq st h1 == Spec.rounds (A.as_rseq st h0));
  admit()

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
  admit()
  // copy_state k ctx;
  // k.(12ul) <- k.(12ul) +. ctr_u32;
  // rounds k;
  // sum_state k ctx;
  // k.(12ul) <- k.(12ul) +. ctr_u32
