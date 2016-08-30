
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Inline
| NoInline
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars 
 and steps =
step Prims.list


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iota = (fun _discr_ -> (match (_discr_) with
| Iota (_) -> begin
true
end
| _ -> begin
false
end))


let is_Zeta = (fun _discr_ -> (match (_discr_) with
| Zeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exclude = (fun _discr_ -> (match (_discr_) with
| Exclude (_) -> begin
true
end
| _ -> begin
false
end))


let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoInline = (fun _discr_ -> (match (_discr_) with
| NoInline (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reify = (fun _discr_ -> (match (_discr_) with
| Reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_CompressUvars = (fun _discr_ -> (match (_discr_) with
| CompressUvars (_) -> begin
true
end
| _ -> begin
false
end))


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_53_8) -> begin
_53_8
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_11) -> begin
_53_11
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list


let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))


let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_53_14) -> begin
_53_14
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_17) -> begin
_53_17
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_20, t, _53_23, _53_25) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_29 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level)


let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))


let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Steps = (fun _discr_ -> (match (_discr_) with
| Steps (_) -> begin
true
end
| _ -> begin
false
end))


let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_53_36) -> begin
_53_36
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_39) -> begin
_53_39
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_42) -> begin
_53_42
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_45) -> begin
_53_45
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_48) -> begin
_53_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_51) -> begin
_53_51
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_54) -> begin
_53_54
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_57) -> begin
_53_57
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_53_60) -> begin
_53_60
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_66) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _146_213 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _146_213 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_73, _53_75) -> begin
(closure_to_string c)
end
| MemoLazy (_53_79) -> begin
"MemoLazy"
end
| Abs (_53_82, bs, _53_85, _53_87, _53_89) -> begin
(let _146_216 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _146_216))
end
| _53_93 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _146_219 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _146_219 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_100 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_107 -> begin
(let _146_235 = (let _146_234 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _146_234))
in (FStar_All.failwith _146_235))
end)


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _146_240 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _146_240 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_120 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_120) with
| (binders, cdef) -> begin
(

let inst = (let _146_244 = (let _146_243 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_243)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_124 _53_128 -> (match (((_53_124), (_53_128))) with
| ((x, _53_123), (t, _53_127)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _146_244))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _53_131 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_131.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_131.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_131.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid) then begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid) then begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end else begin
None
end
end
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _53_153 = (FStar_List.fold_left (fun _53_144 u -> (match (_53_144) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_148 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_148) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_153) with
| (_53_150, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| _53_170 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_163 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(FStar_All.failwith "Universe variable not found")
end
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_261 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _146_261 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_263 = (aux u)
in (FStar_List.map (fun _146_262 -> FStar_Syntax_Syntax.U_succ (_146_262)) _146_263))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (

let _53_201 = (log cfg (fun _53_200 -> (match (()) with
| () -> begin
(let _146_287 = (FStar_Syntax_Print.tag_of_term t)
in (let _146_286 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _146_287 _146_286)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_205 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_208) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_221) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _146_292 = (let _146_291 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_146_291))
in (mk _146_292 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _146_293 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _146_293))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_232) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_239) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _53_255 = (closures_as_binders_delayed cfg env bs)
in (match (_53_255) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _146_296 = (let _146_295 = (let _146_294 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_146_294)))
in FStar_Syntax_Syntax.Tm_abs (_146_295))
in (mk _146_296 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_263 = (closures_as_binders_delayed cfg env bs)
in (match (_53_263) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_271 = (let _146_298 = (let _146_297 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_297)::[])
in (closures_as_binders_delayed cfg env _146_298))
in (match (_53_271) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _146_302 = (let _146_301 = (let _146_300 = (let _146_299 = (FStar_List.hd x)
in (FStar_All.pipe_right _146_299 Prims.fst))
in ((_146_300), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_146_301))
in (mk _146_302 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _146_308 = (let _146_307 = (let _146_306 = (closure_as_term_delayed cfg env t1)
in (let _146_305 = (let _146_304 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _146_303 -> FStar_Util.Inl (_146_303)) _146_304))
in ((_146_306), (_146_305), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_146_307))
in (mk _146_308 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _146_314 = (let _146_313 = (let _146_312 = (closure_as_term_delayed cfg env t1)
in (let _146_311 = (let _146_310 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _146_309 -> FStar_Util.Inr (_146_309)) _146_310))
in ((_146_312), (_146_311), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_146_313))
in (mk _146_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _146_319 = (let _146_318 = (let _146_317 = (closure_as_term_delayed cfg env t')
in (let _146_316 = (let _146_315 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_146_315))
in ((_146_317), (_146_316))))
in FStar_Syntax_Syntax.Tm_meta (_146_318))
in (mk _146_319 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _146_325 = (let _146_324 = (let _146_323 = (closure_as_term_delayed cfg env t')
in (let _146_322 = (let _146_321 = (let _146_320 = (closure_as_term_delayed cfg env tbody)
in ((m), (_146_320)))
in FStar_Syntax_Syntax.Meta_monadic (_146_321))
in ((_146_323), (_146_322))))
in FStar_Syntax_Syntax.Tm_meta (_146_324))
in (mk _146_325 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _146_328 = (let _146_327 = (let _146_326 = (closure_as_term_delayed cfg env t')
in ((_146_326), (m)))
in FStar_Syntax_Syntax.Tm_meta (_146_327))
in (mk _146_328 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_310 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_316) -> begin
body
end
| FStar_Util.Inl (_53_319) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_322 = lb
in {FStar_Syntax_Syntax.lbname = _53_322.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_322.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_322.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_326, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_335 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_339 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_343 = lb
in (let _146_340 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _146_339 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_343.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_343.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _146_340; FStar_Syntax_Syntax.lbeff = _53_343.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _146_339}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_346 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_361 -> (match (_53_361) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_366) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_376 = (norm_pat env hd)
in (match (_53_376) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _146_352 = (norm_pat env p)
in (Prims.fst _146_352)))))
in (((

let _53_379 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_379.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_379.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_396 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_387 _53_390 -> (match (((_53_387), (_53_390))) with
| ((pats, env), (p, b)) -> begin
(

let _53_393 = (norm_pat env p)
in (match (_53_393) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_396) with
| (pats, env) -> begin
(((

let _53_397 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_397.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_397.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_401 = x
in (let _146_355 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_401.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_401.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_355}))
in (((

let _53_404 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_404.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_404.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_408 = x
in (let _146_356 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_408.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_408.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_356}))
in (((

let _53_411 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_411.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_411.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_417 = x
in (let _146_357 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_357}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_421 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_421.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_421.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_425 = (norm_pat env pat)
in (match (_53_425) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_358 = (closure_as_term cfg env w)
in Some (_146_358))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _146_361 = (let _146_360 = (let _146_359 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_146_359)))
in FStar_Syntax_Syntax.Tm_match (_146_360))
in (mk _146_361 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_436 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_442 -> begin
(FStar_List.map (fun _53_445 -> (match (_53_445) with
| (x, imp) -> begin
(let _146_369 = (closure_as_term_delayed cfg env x)
in ((_146_369), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_461 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_451 _53_454 -> (match (((_53_451), (_53_454))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_455 = b
in (let _146_375 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_375}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_461) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_467 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _146_379 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _146_379))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _146_380 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _146_380))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _146_382 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_146_382))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let _53_481 = c
in {FStar_Syntax_Syntax.effect_name = _53_481.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_total_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
end
| _53_490 -> begin
lopt
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_495 = t
in {FStar_Syntax_Syntax.n = _53_495.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_495.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_495.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_504 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_582 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| _53_625 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_652))::((_53_643, (arg, _53_646)))::[] -> begin
arg
end
| _53_656 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_660))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_666))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_670 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _146_396 = (FStar_Syntax_Subst.compress t)
in _146_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_688)::[], body, _53_692) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_700 -> begin
tm
end)
end
| _53_702 -> begin
tm
end)
end
| _53_704 -> begin
tm
end)
end else begin
tm
end
end
end
end
end
end
| _53_706 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_713 = (log cfg (fun _53_712 -> (match (()) with
| () -> begin
(let _146_429 = (FStar_Syntax_Print.tag_of_term t)
in (let _146_428 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _146_429 _146_428)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_716) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_758; FStar_Syntax_Syntax.pos = _53_756; FStar_Syntax_Syntax.vars = _53_754}, ((steps, _53_768))::((tm, _53_764))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_ty) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::[]
in (

let cfg' = (

let _53_774 = cfg
in {steps = s; tcenv = _53_774.tcenv; delta_level = FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)})
in (

let stack' = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_783; FStar_Syntax_Syntax.pos = _53_781; FStar_Syntax_Syntax.vars = _53_779}, (a1)::(a2)::rest) -> begin
(

let _53_797 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_797) with
| (hd, _53_796) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_805; FStar_Syntax_Syntax.pos = _53_803; FStar_Syntax_Syntax.vars = _53_801}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_816 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_816) with
| (reify_head, _53_815) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _146_433 = (FStar_Syntax_Subst.compress e)
in _146_433.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_836 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_836) with
| (_53_834, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _146_438 = (let _146_437 = (let _146_436 = (let _146_434 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_434)::[])
in (let _146_435 = (FStar_Syntax_Util.mk_reify body)
in ((_146_436), (_146_435), (None))))
in FStar_Syntax_Syntax.Tm_abs (_146_437))
in (FStar_Syntax_Syntax.mk _146_438 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _146_452 = (let _146_451 = (let _146_450 = (let _146_449 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _146_448 = (let _146_447 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _146_446 = (let _146_445 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _146_444 = (let _146_443 = (FStar_Syntax_Syntax.as_arg head)
in (let _146_442 = (let _146_441 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _146_440 = (let _146_439 = (FStar_Syntax_Syntax.as_arg body)
in (_146_439)::[])
in (_146_441)::_146_440))
in (_146_443)::_146_442))
in (_146_445)::_146_444))
in (_146_447)::_146_446))
in (_146_449)::_146_448))
in ((bind_repr), (_146_450)))
in FStar_Syntax_Syntax.Tm_app (_146_451))
in (FStar_Syntax_Syntax.mk _146_452 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_843) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_846) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_849 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_858)); FStar_Syntax_Syntax.tk = _53_856; FStar_Syntax_Syntax.pos = _53_854; FStar_Syntax_Syntax.vars = _53_852}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_874 -> (match (_53_874) with
| (pat, wopt, tm) -> begin
(let _146_454 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_146_454)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_878 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _146_455 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _146_455)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _146_457 = (let _146_456 = (FStar_List.map (norm_universe cfg env) us)
in ((_146_456), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_146_457))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (match (cfg.delta_level) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.OnlyInline -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end)
in if (not (should_delta)) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_903 = (log cfg (fun _53_902 -> (match (()) with
| () -> begin
(let _146_460 = (FStar_Syntax_Print.term_to_string t0)
in (let _146_459 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _146_460 _146_459)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_909))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_917 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_919 -> begin
(let _146_464 = (let _146_463 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _146_463))
in (FStar_All.failwith _146_464))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_923) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _53_937 = (log cfg (fun _53_936 -> (match (()) with
| () -> begin
(let _146_467 = (FStar_Syntax_Print.term_to_string t)
in (let _146_466 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _146_467 _146_466)))
end)))
in (match ((let _146_468 = (FStar_Syntax_Subst.compress t')
in _146_468.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_940) -> begin
(norm cfg env stack t')
end
| _53_943 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end)
end else begin
(norm cfg env stack t0)
end
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (Meta (_53_953))::_53_951 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_959))::_53_957 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_965))::_53_963 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_971, _53_973))::stack_rest -> begin
(match (c) with
| Univ (_53_978) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_981 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_984)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_988 = (log cfg (fun _53_987 -> (match (()) with
| () -> begin
(let _146_470 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _146_470))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_994 = (log cfg (fun _53_993 -> (match (()) with
| () -> begin
(let _146_472 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _146_472))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1000 = (log cfg (fun _53_999 -> (match (()) with
| () -> begin
(let _146_474 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _146_474))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1003 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1005 -> begin
(

let cfg = (

let _53_1006 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1006.tcenv; delta_level = _53_1006.delta_level})
in (let _146_475 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_475)))
end)
end
| (_53_1011)::tl -> begin
(

let _53_1014 = (log cfg (fun _53_1013 -> (match (()) with
| () -> begin
(let _146_477 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _146_477))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1023 = cfg
in {steps = s; tcenv = _53_1023.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1029 = (set_memo r ((env), (t)))
in (

let _53_1032 = (log cfg (fun _53_1031 -> (match (()) with
| () -> begin
(let _146_479 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _146_479))
end)))
in (norm cfg env stack t)))
end
| ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _146_480 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_480))
end else begin
(

let _53_1056 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1056) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _146_486 = (let _146_484 = (let _146_482 = (let _146_481 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _146_481))
in (FStar_All.pipe_right _146_482 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _146_484 (fun _146_483 -> FStar_Util.Inl (_146_483))))
in (FStar_All.pipe_right _146_486 (fun _146_485 -> Some (_146_485))))
end
| _53_1061 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1064 -> (Dummy)::env) env))
in (

let _53_1068 = (log cfg (fun _53_1067 -> (match (()) with
| () -> begin
(let _146_490 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _146_490))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1076 stack -> (match (_53_1076) with
| (a, aq) -> begin
(let _146_497 = (let _146_496 = (let _146_495 = (let _146_494 = (let _146_493 = (FStar_Util.mk_ref None)
in ((env), (a), (_146_493), (false)))
in Clos (_146_494))
in ((_146_495), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_146_496))
in (_146_497)::stack)
end)) args))
in (

let _53_1080 = (log cfg (fun _53_1079 -> (match (()) with
| () -> begin
(let _146_499 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _146_499))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let _53_1090 = x
in {FStar_Syntax_Syntax.ppname = _53_1090.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1090.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1094 -> begin
(let _146_500 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_500))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1098 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1098) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _146_503 = (let _146_502 = (let _146_501 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1100 = x
in {FStar_Syntax_Syntax.ppname = _53_1100.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1100.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_146_501)))
in FStar_Syntax_Syntax.Tm_refine (_146_502))
in (mk _146_503 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _146_504 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_504))
end else begin
(

let _53_1109 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1109) with
| (bs, c) -> begin
(

let c = (let _146_507 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1111 -> (Dummy)::env) env))
in (norm_comp cfg _146_507 c))
in (

let t = (let _146_508 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _146_508 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1139 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1142 = (log cfg (fun _53_1141 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _146_510 = (norm cfg env [] t)
in FStar_Util.Inl (_146_510))
end
| FStar_Util.Inr (c) -> begin
(let _146_511 = (norm_comp cfg env c)
in FStar_Util.Inr (_146_511))
end)
in (let _146_512 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _146_512)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1155, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1167); FStar_Syntax_Syntax.lbunivs = _53_1165; FStar_Syntax_Syntax.lbtyp = _53_1163; FStar_Syntax_Syntax.lbeff = _53_1161; FStar_Syntax_Syntax.lbdef = _53_1159})::_53_1157), _53_1173) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _146_515 = (let _146_514 = (let _146_513 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_146_513), (false)))
in Clos (_146_514))
in (_146_515)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1187 = (let _146_518 = (let _146_517 = (let _146_516 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _146_516 FStar_Syntax_Syntax.mk_binder))
in (_146_517)::[])
in (FStar_Syntax_Subst.open_term _146_518 body))
in (match (_53_1187) with
| (bs, body) -> begin
(

let lb = (

let _53_1188 = lb
in (let _146_524 = (let _146_521 = (let _146_519 = (FStar_List.hd bs)
in (FStar_All.pipe_right _146_519 Prims.fst))
in (FStar_All.pipe_right _146_521 (fun _146_520 -> FStar_Util.Inl (_146_520))))
in (let _146_523 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _146_522 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _146_524; FStar_Syntax_Syntax.lbunivs = _53_1188.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _146_523; FStar_Syntax_Syntax.lbeff = _53_1188.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _146_522}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1192 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _146_527 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_527))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1218 = (FStar_List.fold_right (fun lb _53_1207 -> (match (_53_1207) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _146_530 = (

let _53_1208 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1208.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1208.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _146_530))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1218) with
| (rec_env, memos, _53_1217) -> begin
(

let _53_1221 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _146_537 = (let _146_536 = (let _146_535 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_146_535), (false)))
in Clos (_146_536))
in (_146_537)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_1233)::_53_1231 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1238) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let t = (norm cfg env [] t)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1250 -> begin
(norm cfg env stack head)
end)
end
| _53_1252 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _146_538 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_146_538))
end
| _53_1257 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1265 -> (match (_53_1265) with
| (a, imp) -> begin
(let _146_543 = (norm cfg env [] a)
in ((_146_543), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _53_1272 = comp
in (let _146_548 = (let _146_547 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_146_547))
in {FStar_Syntax_Syntax.n = _146_548; FStar_Syntax_Syntax.tk = _53_1272.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1272.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1272.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _53_1276 = comp
in (let _146_550 = (let _146_549 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_146_549))
in {FStar_Syntax_Syntax.n = _146_550; FStar_Syntax_Syntax.tk = _53_1276.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1276.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1276.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1284 -> (match (_53_1284) with
| (a, i) -> begin
(let _146_554 = (norm cfg env [] a)
in ((_146_554), (i)))
end)))))
in (

let _53_1285 = comp
in (let _146_558 = (let _146_557 = (

let _53_1287 = ct
in (let _146_556 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _146_555 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1287.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _146_556; FStar_Syntax_Syntax.effect_args = _146_555; FStar_Syntax_Syntax.flags = _53_1287.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_146_557))
in {FStar_Syntax_Syntax.n = _146_558; FStar_Syntax_Syntax.tk = _53_1285.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1285.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1285.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1294 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1294.tcenv; delta_level = _53_1294.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _146_566 = (norm t)
in (FStar_Syntax_Util.non_informative _146_566)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1299) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(

let _53_1303 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_1303.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1303.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1303.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1310 = ct
in {FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1310.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1310.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1310.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1314 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1314.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1314.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1314.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1317 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1317.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1317.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1317.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1320 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1325 -> (match (_53_1325) with
| (x, imp) -> begin
(let _146_571 = (

let _53_1326 = x
in (let _146_570 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1326.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1326.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_570}))
in ((_146_571), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1339 = (FStar_List.fold_left (fun _53_1333 b -> (match (_53_1333) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1339) with
| (nbs, _53_1338) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _146_582 = (let _146_581 = (let _146_580 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _146_580))
in FStar_Util.Inl (_146_581))
in Some (_146_582))
end else begin
(let _146_585 = (let _146_584 = (let _146_583 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _146_583))
in FStar_Util.Inl (_146_584))
in Some (_146_585))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1348 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1360 = cfg
in {steps = s; tcenv = _53_1360.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1373 = (set_memo r ((env), (t)))
in (

let _53_1376 = (log cfg (fun _53_1375 -> (match (()) with
| () -> begin
(let _146_591 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _146_591))
end)))
in (rebuild cfg env stack t)))
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _146_592 = (

let _53_1399 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1399.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1399.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1399.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _146_592))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1435), aq, r))::stack -> begin
(

let _53_1444 = (log cfg (fun _53_1443 -> (match (()) with
| () -> begin
(let _146_594 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _146_594))
end)))
in if (FStar_List.contains (Exclude (Iota)) cfg.steps) then begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1454, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _146_595 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _146_595)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1475 = (log cfg (fun _53_1474 -> (match (()) with
| () -> begin
(let _146_597 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _146_597))
end)))
in (

let norm_and_rebuild_match = (fun _53_1478 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1480 = cfg
in (let _146_600 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1480.tcenv; delta_level = _146_600}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1490) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1500 = (norm_pat env hd)
in (match (_53_1500) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _146_610 = (norm_pat env p)
in (Prims.fst _146_610)))))
in (((

let _53_1503 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1503.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1503.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1520 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1511 _53_1514 -> (match (((_53_1511), (_53_1514))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1517 = (norm_pat env p)
in (match (_53_1517) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1520) with
| (pats, env) -> begin
(((

let _53_1521 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1521.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1521.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1525 = x
in (let _146_613 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1525.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1525.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_613}))
in (((

let _53_1528 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1528.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1528.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1532 = x
in (let _146_614 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1532.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1532.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_614}))
in (((

let _53_1535 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1535.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1535.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1541 = x
in (let _146_615 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1541.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1541.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_615}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1545 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1545.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1545.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1549 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1554 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1554) with
| (p, wopt, e) -> begin
(

let _53_1557 = (norm_pat env p)
in (match (_53_1557) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_617 = (norm_or_whnf env w)
in Some (_146_617))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _146_618 = (mk (FStar_Syntax_Syntax.Tm_match (((t), (branches)))) r)
in (rebuild cfg env stack _146_618)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1568) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1593 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((t), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun t p -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_1610 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1610) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1616) -> begin
Some (m)
end
| FStar_Util.Inr (true) -> begin
Some (m)
end
| FStar_Util.Inr (false) -> begin
None
end))))
in (match (mopt) with
| None -> begin
FStar_Util.Inr (false)
end
| Some (m) -> begin
m
end))
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
FStar_Util.Inl ((t)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (_53_1633) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1640 -> begin
(let _146_635 = (not ((is_cons head)))
in FStar_Util.Inr (_146_635))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _146_636 = (FStar_Syntax_Util.un_uinst head)
in _146_636.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1648 -> begin
(let _146_637 = (not ((is_cons head)))
in FStar_Util.Inr (_146_637))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1658))::rest_a, ((p, _53_1664))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1672 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun t p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inr (false) -> begin
(matches t rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _53_1690 = (log cfg (fun _53_1689 -> (match (()) with
| () -> begin
(let _146_648 = (FStar_Syntax_Print.pat_to_string p)
in (let _146_647 = (let _146_646 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _146_646 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _146_648 _146_647)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _146_653 = (let _146_652 = (let _146_651 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_146_651), (false)))
in Clos (_146_652))
in (_146_653)::env)) env s)
in (let _146_654 = (guard_when_clause wopt b rest)
in (norm cfg env stack _146_654))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches t branches)
end))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (match ((FStar_Util.find_map s (fun _53_5 -> (match (_53_5) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1701 -> begin
None
end)))) with
| Some (k) -> begin
FStar_TypeChecker_Env.Unfold (k)
end
| None -> begin
if (FStar_List.contains Inline s) then begin
FStar_TypeChecker_Env.OnlyInline
end else begin
FStar_TypeChecker_Env.NoDelta
end
end)
in {steps = s; tcenv = e; delta_level = d}))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _146_666 = (config s e)
in (norm _146_666 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _146_673 = (config s e)
in (norm_comp _146_673 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _146_678 = (config [] env)
in (norm_universe _146_678 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_683 = (config [] env)
in (ghost_to_pure_aux _146_683 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _146_690 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _146_690)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1723 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1723.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1723.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1725 -> (match (()) with
| () -> begin
(let _146_692 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _146_692))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _146_697 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _146_697)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _146_703 = (let _146_702 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _146_702 [] c))
in (FStar_Syntax_Print.comp_to_string _146_703)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _146_714 = (let _146_713 = (let _146_712 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_146_712)))
in FStar_Syntax_Syntax.Tm_refine (_146_713))
in (mk _146_714 t0.FStar_Syntax_Syntax.pos))
end
| _53_1748 -> begin
t
end))
end
| _53_1750 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1757 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1757) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1760 -> begin
(

let _53_1763 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1763) with
| (binders, args) -> begin
(let _146_725 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _146_724 = (let _146_723 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _146_721 -> FStar_Util.Inl (_146_721)))
in (FStar_All.pipe_right _146_723 (fun _146_722 -> Some (_146_722))))
in (FStar_Syntax_Util.abs binders _146_725 _146_724)))
end))
end)
end)))
in (match ((let _146_726 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_146_726), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1767) -> begin
(let _146_727 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _146_727))
end
| (_53_1770, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1775 -> begin
(

let _53_1778 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1778) with
| (head, args) -> begin
(match ((let _146_728 = (FStar_Syntax_Subst.compress head)
in _146_728.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1780, thead) -> begin
(

let _53_1786 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1786) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1794 = (env.FStar_TypeChecker_Env.type_of (

let _53_1787 = env
in {FStar_TypeChecker_Env.solver = _53_1787.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1787.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1787.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1787.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1787.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1787.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1787.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1787.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1787.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1787.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1787.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1787.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1787.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1787.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1787.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1787.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1787.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1787.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1787.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1787.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1794) with
| (_53_1790, ty, _53_1793) -> begin
(expand ty)
end))
end
end))
end
| _53_1796 -> begin
(

let _53_1804 = (env.FStar_TypeChecker_Env.type_of (

let _53_1797 = env
in {FStar_TypeChecker_Env.solver = _53_1797.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1797.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1797.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1797.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1797.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1797.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1797.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1797.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1797.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1797.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1797.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1797.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1797.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1797.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1797.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1797.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1797.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1797.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1797.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1797.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1804) with
| (_53_1800, ty, _53_1803) -> begin
(expand ty)
end))
end)
end))
end)))




