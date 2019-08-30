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

val double_round:
  st:state ->
  RST unit
  (A.array_resource st)
  (fun _ -> A.array_resource st)
  (requires fun h -> P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 == Spec.double_round (A.as_rseq st h0))

inline_for_extraction
val copy_state:
    st:state
  -> ost:state ->
  RST unit
  (A.array_resource st <*> A.array_resource ost)
  (fun _ -> A.array_resource st <*> A.array_resource ost)
  (requires fun h -> P.allows_write (A.get_rperm st h))
  (ensures  fun h0 _ h1 ->
    h0 (A.array_resource ost) == h1 (A.array_resource ost) /\
    P.allows_write (A.get_rperm st h1) /\
    A.as_rseq st h1 `Seq.equal` A.as_rseq ost h0)

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

open FStar.Mul

val uints_from_bytes_le:  #len:nat
  -> o:A.array UInt32.t
  -> i:A.array UInt8.t ->
  RST unit
    (A.array_resource o <*> A.array_resource i)
    (fun _ -> A.array_resource o <*> A.array_resource i)
    (requires fun h0 ->
      A.vlength o == len /\ A.vlength i == len * 4 /\
      P.allows_write (A.get_rperm o h0))
    (ensures  fun h0 _ h1 ->
      A.vlength o == len /\ A.vlength i == len * 4 /\
      h0 (A.array_resource i) == h1 (A.array_resource i) /\
      P.allows_write (A.get_rperm o h1) /\
      A.as_rseq o h1 == Spec.uints_from_bytes_le (A.as_rseq i h0)
    )

val uints_to_bytes_le:  #len:nat
  -> o:A.array UInt8.t{A.vlength o == len * 4}
  -> i:A.array UInt32.t{A.vlength i == len} ->
  RST unit
    (A.array_resource o <*> A.array_resource i)
    (fun _ -> A.array_resource o <*> A.array_resource i)
    (requires fun h0 ->
      P.allows_write (A.get_rperm o h0))
    (ensures  fun h0 _ h1 ->
      h0 (A.array_resource i) == h1 (A.array_resource i) /\
      P.allows_write (A.get_rperm o h1) /\
      A.as_rseq o h1 == Spec.uints_to_bytes_le (A.as_rseq i h0)
    )

val xor_block:
    o:A.array UInt8.t{A.vlength o == 64}
  -> st:state
  -> b:A.array UInt8.t{A.vlength b == 64} ->
  RST unit
    (A.array_resource o <*> A.array_resource st <*> A.array_resource b)
    (fun _ -> A.array_resource o <*> A.array_resource st <*> A.array_resource b)
    (requires fun h ->
      // TODO: Figure out why is_subresource lemmas patterns are not triggering,
      // although they are for funcions in Chacha20.fst
      assert (A.array_resource o `is_subresource_of` (A.array_resource o <*> A.array_resource st));
      assert ( (A.array_resource o <*> A.array_resource st) `is_subresource_of`
        (A.array_resource o <*> A.array_resource st <*> A.array_resource b));
      P.allows_write (A.get_rperm o h))
    (ensures  fun h0 _ h1 ->
      assert (A.array_resource o `is_subresource_of` (A.array_resource o <*> A.array_resource st));
      assert (A.array_resource st `is_subresource_of` (A.array_resource o <*> A.array_resource st));
      assert ( (A.array_resource o <*> A.array_resource st) `is_subresource_of`
        (A.array_resource o <*> A.array_resource st <*> A.array_resource b));

      h0 (A.array_resource st) == h1 (A.array_resource st) /\
      h0 (A.array_resource b) == h1 (A.array_resource b) /\
      P.allows_write (A.get_rperm o h1) /\
      A.as_rseq o h1 `Seq.equal` Spec.xor_block (A.as_rseq st h0) (A.as_rseq b h0))
