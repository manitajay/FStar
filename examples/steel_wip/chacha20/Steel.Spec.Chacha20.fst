module Steel.Spec.Chacha20

open FStar.Mul
open FStar.Seq

/// Constants and Types

let size_key = 32
let size_block = 64
let size_nonce = 12

(* TODO: Remove, left here to avoid breaking implementation *)
let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type bytes = seq UInt8.t
let lbytes = lseq UInt8.t

type key = lbytes size_key
type block = lbytes size_block
type nonce = lbytes size_nonce
type counter = UInt32.t
type subblock = b:bytes{length b <= size_block}
type rotval = (r:UInt32.t{UInt32.v r > 0 /\ UInt32.v r < 32})
let size = UInt32.uint_to_t

// Internally, blocks are represented as 16 x 4-byte integers
type state = lseq UInt32.t 16
type idx = n:nat{n < 16}
type shuffle = state -> Tot state

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)

/// Specification

let op_String_Access = Seq.index
let op_String_Assignment = Seq.upd

let rotate_left (a:UInt32.t) (b:rotval) : UInt32.t =
  let open FStar.UInt32 in
  logor (shift_left a b) (shift_right a (sub (size 32) b))

let line (a:idx) (b:idx) (d:idx) (s:rotval) (m:state) : Tot state =
  let m = m.[a] <- (m.[a] `FStar.UInt32.add_mod` m.[b]) in
  let m = m.[d] <- ((m.[d] `FStar.UInt32.logxor` m.[a]) `rotate_left` s) in m

let quarter_round a b c d : Tot shuffle =
  line a b d (size 16) @
  line c d b (size 12) @
  line a b d (size 8)  @
  line c d b (size 7)


let column_round : shuffle =
  quarter_round 0 4 8  12 @
  quarter_round 1 5 9  13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round : shuffle =
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8  13 @
  quarter_round 3 4 9  14

let double_round : shuffle =
  column_round @ diagonal_round (* 2 rounds *)


let rounds : shuffle =
  fun st ->
    double_round (
    double_round (
    double_round (
    double_round (
    double_round (
    double_round (
    double_round (
    double_round (
    double_round (
    double_round st))))))))) (* 20 rounds *)

assume
val map2:#a:Type -> #b:Type -> #c:Type
  -> f:(a -> b -> Tot c)
  -> s1:lseq a 16
  -> s2:lseq b 16 ->
  Tot (s3:lseq c 16{(forall (i:nat).
    {:pattern (index s3 i)} i < 16 ==> index s3 i == f s1.[i] s2.[i])})

let sum_state (s0:state) (s1:state) : Tot state =
  map2 UInt32.add_mod s0 s1

let chacha20_add_counter (s0:state) (ctr:counter) : Tot state =
  s0.[12] <- s0.[12] `UInt32.add_mod` ctr

let chacha20_core (ctr:counter) (s0:state)  : Tot state =
  let k = chacha20_add_counter s0 ctr in
  let k = rounds k in
  let k = sum_state k s0 in
  chacha20_add_counter k  ctr

inline_for_extraction
let c0 = 0x61707865ul
inline_for_extraction
let c1 = 0x3320646eul
inline_for_extraction
let c2 = 0x79622d32ul
inline_for_extraction
let c3 = 0x6b206574ul

let chacha20_constants : lseq UInt32.t 4 =
  [@ inline_let]
  let l = [c0;c1;c2;c3] in
  assert_norm(List.Tot.length l == 4);
  createL l

(** Updating a sub-Sequence from another fixed-length Sequence *)
val update_sub:
    #a:Type
  -> #len:nat
  -> i:lseq a len
  -> start:nat
  -> n:nat{start + n <= len}
  -> x:lseq a n ->
  Tot (o:lseq a len{Seq.slice o start (start + n) == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < len)}).
      {:pattern (index o k)} index o k == index i k)})

let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) (length s)) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

assume
val uints_from_bytes_le: #len:nat -> lbytes (len * 4) -> lseq UInt32.t len
assume
val uints_to_bytes_le: #len:nat -> lseq UInt32.t len -> lbytes (len * 4)



let setup (k:key) (n:nonce) (ctr0:counter) (st:state) : Tot state =
  let st = update_sub st 0 4 chacha20_constants in
  let st = update_sub st 4 8 (uints_from_bytes_le k) in
  let st = st.[12] <- ctr0 in
  let st = update_sub st 13 3 (uints_from_bytes_le n) in
  st

let chacha20_init (k:key) (n:nonce) (ctr0:counter) : Tot state =
  let st = create 16 (0ul) in
  let st  = setup k n ctr0 st in
  st

let xor_block (k:state) (b:block) : block  =
  let ib = uints_from_bytes_le b in
  let ob = map2 UInt32.logxor ib k in
  uints_to_bytes_le ob

let chacha20_encrypt_block (st0:state) (incr:counter) (b:block) : Tot block =
  let k = chacha20_core incr st0 in
  xor_block k b
