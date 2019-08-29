module Steel.Array.Test

module P = LowStar.Permissions
open Steel.RST
module A = Steel.Array

#reset-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1 --z3cliopt smt.qi.eager_threshold=1000"
#restart-solver
let read_write_without_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 2ul 42ul in
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 1ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 1ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 1ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 1ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  A.free b;
  ()

#set-options "--z3rlimit 20"
let read_write_with_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = rst_frame
    empty_resource
    (fun b -> A.array_resource b)
    (fun _ -> A.alloc 2ul 42ul)
  in
  let x1 = rst_frame
    (A.array_resource b)
    (fun _ -> A.array_resource b)
    (fun _ -> A.index b 0ul)
  in

  // We need to let-bind this variable for unification to work correctly in rst_frame
  // According to NS, this is due to the $ quantifier in the type of f for rst_frame
  // Because of additional constraints if this parameter is inlined, the RST
  // definition needs to be unfolded to STATE, and then type unification is lost
  // This should be solved with effect layering
  let v =   FStar.UInt32.(x1 +%^ 1ul) in

  rst_frame
    (A.array_resource b)
    (fun _ -> A.array_resource b)
    (fun _ -> A.upd #FStar.UInt32.t b 0ul v);

  let b1 = rst_frame
    (A.array_resource b)
    (fun b1 -> A.array_resource b <*> A.array_resource b1)
    (fun _ -> A.share b)
  in
  let x1 =
    rst_frame
      (A.array_resource b <*> A.array_resource b1)
      (fun _ -> A.array_resource b <*> A.array_resource b1)
      (fun _ -> A.index b 0ul)
  in
  let h_presplit = get  (A.array_resource b <*> A.array_resource b1) in
  let b_first, b_second = rst_frame
    (A.array_resource b <*> A.array_resource b1)
    (fun p -> A.array_resource (fst p) <*> A.array_resource (snd p) <*> A.array_resource b1)
    (fun _ -> A.split #FStar.UInt32.t b 1ul)
  in

  let h0 =
    get (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in

  // This assertion is needed to conclude the commented assertion just below with
  // focus_rmem_equality SMTPat
  // TODO: Understand why this does not kick in with the postcondition of rst_frame
  assert ((focus_rmem h0 (A.array_resource b1)) (A.array_resource b1) ==
          (focus_rmem h_presplit (A.array_resource b1)) (A.array_resource b1));
  // assert (h0 (A.array_resource b1) == h00 (A.array_resource b1));

  let x2 = rst_frame
    (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
    (fun _ -> (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> A.index b_second 0ul)
  in

  let h1 =
    get (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in

  // Again, need to add a assertion about focus_rmem to trigger SMTPats
  assert (h0 (A.array_resource b_first) ==
    (focus_rmem h0 (A.array_resource b_first <*> A.array_resource b1)) (A.array_resource b_first));

  rst_frame
    ((A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> (A.array_resource b <*> A.array_resource b1))
    (fun _ -> A.glue b b_first b_second);

  let h2 = get (A.array_resource b <*> A.array_resource b1) in

  // Again, need assertions to trigger SMTPats to prove
  // h0 (A.array_resource b1) == h2 (A.array_resource b1)
  assert (h0 (A.array_resource b1) ==
    (focus_rmem h0 (A.array_resource b_first <*> A.array_resource b1)) (A.array_resource b1));
  assert (h2 (A.array_resource b1) ==
    (focus_rmem h2 (A.array_resource b1)) (A.array_resource b1));

  A.gather b b1;
  A.free b
