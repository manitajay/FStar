module ParDiv.Memory

friend Steel.Resource

let interp_extensionality_explicit x y h = ()

let heap = HS.mem

let hm : comm_monoid heap =
  { r = resource;
    equals = equals;
    emp = empty_resource;
    star = (<*>) ;
    interp = interp;
    laws = laws }

let hm_affine r0 r1 h = ()

let ref = fun a -> HS.mreference a (fun _ _ -> True)

let ptr_view (r:ref 'a) : GTot ( view 'a) = admit()
//  { fp = admit(); inv = (fun h -> HS.contains h r /\ True); sel = fun h -> HS.sel h r  }

let ptr_live (r:ref 'a) = { t = 'a; view = ptr_view r }
