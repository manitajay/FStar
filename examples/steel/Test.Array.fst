module Test.Array

open Steel.RST
open Steel.Array

module U32 = FStar.UInt32
module P = LowStar.Permissions

let basic_test_increment (p: array U32.t) : RST unit
  (array_resource p)
  (fun _ -> array_resource p)
  (fun h0 -> P.allows_write (get_rperm p h0))
  (fun h0 _ h1 -> Seq.index (as_rseq p h1) 0 == U32.add_mod (Seq.index (as_rseq p h0) 0) 1ul)
  =
  let x = rst_frame
    (array_resource p)
    (fun _ -> array_resource p)
    (fun _ -> index p 0ul)
  in
  let new_x = U32.add_mod x 1ul in
  rst_frame
    (array_resource p)
    (fun _ -> array_resource p)
    ( fun _ -> upd p 0ul new_x)
