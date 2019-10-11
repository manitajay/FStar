module Param

open FStar.Tactics

let rec param (bvmap : bv -> Tac (binder & binder & binder)) (t:term) : Tac term =
  let _replace_by (b:bool) (t:term) : Tac term =
       match inspect t with
       | Tv_Var bv ->
         let (x, y, _) = bvmap bv in
         let bv = if b then fst (inspect_binder y) else fst (inspect_binder x) in
         pack (Tv_Var bv)
       | _ -> t
  in
  let replace_by b t = visit_tm (_replace_by b) t in
  match inspect t with
  | Tv_Type () ->
    `(fun (s t : Type) -> s -> t -> Type0)
  | Tv_Var bv ->
    let (_, _, r) = bvmap bv in
    r
  | Tv_Arrow b c ->
    let (bv, q) = inspect_binder b in
    begin match inspect_comp c with
    | C_Total t2 _ ->
      let t1 = (inspect_bv bv).bv_sort in
      // bv:t1 -> t2

      let app t1 t2 = `((`#t1) (`#t2)) in
      let abs b t : Tac term = pack (Tv_Abs b t) in
      let bf0 = fresh_binder_named "f0" (replace_by false t) in
      let bf1 = fresh_binder_named "f1" (replace_by true t) in
      let bx0 = fresh_binder_named "x0" (replace_by false t1) in
      let bx1 = fresh_binder_named "x1" (replace_by true t1) in
      let brx = fresh_binder_named "xR" (`(`#(param bvmap t1)) (`#bx0) (`#bx1)) in
      let bvmap' bv' : Tac (binder & binder & binder) =
        if (compare_bv bv' bv) = Order.Eq
        then (bx0, bx1, brx)
        else bvmap bv'
      in
      let res = `((`#(param bvmap' t2)) (`#(app bf0 bx0)) (`#(app bf1 bx1))) in
      abs bf0 (abs bf1 (mk_tot_arr [bx0; bx1; brx] res))
    | _ -> fail "we don't support effects"  
    end
  | _ -> t

let param' t = param (fun _ -> fail "not found!") t
    
    
let param_0 : Type -> Type -> Type = _ by (exact (param' (`Type)))

let param_1 : (Type -> Type) -> (Type -> Type) -> Type =
            _ by (exact (param' (`(Type -> Type))))

//let _ =
// assert True by
//    (let tm = param' (`(xxs:Type -> Type -> xxs)) in
//     let tm = norm_term [] tm in
//     dump ("tm = " ^ term_to_string tm))
     
//let param_2 : (synth_by_tactic #Type (fun () -> exact (param' (`Type)))) = magic ()

