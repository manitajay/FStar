
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____7 = (FStar_Options.reuse_hint_for ())
in (match (uu____7) with
| Some (l) -> begin
(

let lid = (let _0_235 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _0_235 l))
in (

let uu___96_11 = env
in {FStar_TypeChecker_Env.solver = uu___96_11.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_11.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_11.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_11.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_11.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_11.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_11.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_11.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_11.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_11.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_11.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_11.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_11.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_11.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_11.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_11.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_11.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_11.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_11.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_11.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_11.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_11.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_11.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _0_238 = (FStar_TypeChecker_Env.current_module env)
in (let _0_237 = (let _0_236 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _0_236 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _0_238 _0_237)))
end
| (l)::uu____18 -> begin
l
end)
in (

let uu___97_20 = env
in {FStar_TypeChecker_Env.solver = uu___97_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___97_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___97_20.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___97_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___97_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___97_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_20.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_20.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___97_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_20.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _0_239 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_239))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____35 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____35) with
| (t, c, g) -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
t;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____57 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____57) with
| true -> begin
(let _0_240 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _0_240))
end
| uu____58 -> begin
()
end));
(

let uu____59 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____59) with
| (t', uu____64, uu____65) -> begin
((

let uu____67 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____67) with
| true -> begin
(let _0_241 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _0_241))
end
| uu____68 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _0_242 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _0_242)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _0_243 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_0_243)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____112 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____112) with
| (tps, env, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((tps), (env), (us));
)
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____145 -> (Prims.raise (FStar_Errors.Error ((let _0_244 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((_0_244), ((FStar_Ident.range_of_lid m))))))))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____173))::((wp, uu____175))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____184 -> begin
(fail ())
end))
end
| uu____185 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____215 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____215) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| uu____231 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let uu____238 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____238) with
| (uvs, t') -> begin
(

let uu____249 = (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
in (match (uu____249) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| uu____273 -> begin
(failwith "Impossible")
end))
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____342 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____342) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____349 = (tc_tparams env0 effect_params_un)
in (match (uu____349) with
| (effect_params, env, uu____355) -> begin
(

let uu____356 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____356) with
| (signature, uu____360) -> begin
(

let ed = (

let uu___98_362 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___98_362.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___98_362.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_362.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_362.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___98_362.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___98_362.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___98_362.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___98_362.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___98_362.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___98_362.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___98_362.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___98_362.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___98_362.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___98_362.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___98_362.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___98_362.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___98_362.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___98_362.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| uu____366 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1))))
in (

let uu___99_384 = ed
in (let _0_260 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_259 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_258 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_257 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_256 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _0_255 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _0_254 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _0_253 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _0_252 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _0_251 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _0_250 = (Prims.snd (op (([]), (ed.FStar_Syntax_Syntax.repr))))
in (let _0_249 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _0_248 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_247 = (FStar_List.map (fun a -> (

let uu___100_388 = a
in (let _0_246 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_defn))))
in (let _0_245 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_typ))))
in {FStar_Syntax_Syntax.action_name = uu___100_388.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___100_388.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___100_388.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_246; FStar_Syntax_Syntax.action_typ = _0_245})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___99_384.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___99_384.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___99_384.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___99_384.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___99_384.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___99_384.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _0_260; FStar_Syntax_Syntax.bind_wp = _0_259; FStar_Syntax_Syntax.if_then_else = _0_258; FStar_Syntax_Syntax.ite_wp = _0_257; FStar_Syntax_Syntax.stronger = _0_256; FStar_Syntax_Syntax.close_wp = _0_255; FStar_Syntax_Syntax.assert_p = _0_254; FStar_Syntax_Syntax.assume_p = _0_253; FStar_Syntax_Syntax.null_wp = _0_252; FStar_Syntax_Syntax.trivial = _0_251; FStar_Syntax_Syntax.repr = _0_250; FStar_Syntax_Syntax.return_repr = _0_249; FStar_Syntax_Syntax.bind_repr = _0_248; FStar_Syntax_Syntax.actions = _0_247}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (Prims.raise (FStar_Errors.Error ((let _0_261 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((_0_261), ((FStar_Ident.range_of_lid mname))))))))
in (

let uu____419 = (FStar_Syntax_Subst.compress signature).FStar_Syntax_Syntax.n
in (match (uu____419) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____442))::((wp, uu____444))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____453 -> begin
(fail signature)
end))
end
| uu____454 -> begin
(fail signature)
end))))
in (

let uu____455 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (uu____455) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____473 -> (

let uu____474 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____474) with
| (signature, uu____482) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end)))
in (

let env = (let _0_262 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _0_262))
in ((

let uu____485 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____485) with
| true -> begin
(let _0_267 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_266 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _0_265 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _0_264 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Syntax.bv_to_name a))
in (let _0_263 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _0_267 _0_266 _0_265 _0_264 _0_263))))))
end
| uu____486 -> begin
()
end));
(

let check_and_gen' = (fun env uu____498 k -> (match (uu____498) with
| (uu____503, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _0_272 = (let _0_270 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_269 = (let _0_268 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_268)::[])
in (_0_270)::_0_269))
in (let _0_271 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _0_272 _0_271)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____512 = (fresh_effect_signature ())
in (match (uu____512) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_275 = (let _0_273 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_273)::[])
in (let _0_274 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_275 _0_274)))
in (

let expected_k = (let _0_286 = (let _0_284 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _0_283 = (let _0_282 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_281 = (let _0_280 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_279 = (let _0_278 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_277 = (let _0_276 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_0_276)::[])
in (_0_278)::_0_277))
in (_0_280)::_0_279))
in (_0_282)::_0_281))
in (_0_284)::_0_283))
in (let _0_285 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_286 _0_285)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _0_288 = (let _0_287 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_287 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_288))
in (

let expected_k = (let _0_297 = (let _0_295 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_294 = (let _0_293 = (FStar_Syntax_Syntax.mk_binder p)
in (let _0_292 = (let _0_291 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_290 = (let _0_289 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_289)::[])
in (_0_291)::_0_290))
in (_0_293)::_0_292))
in (_0_295)::_0_294))
in (let _0_296 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_297 _0_296)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _0_302 = (let _0_300 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_299 = (let _0_298 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_298)::[])
in (_0_300)::_0_299))
in (let _0_301 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_302 _0_301)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____541 = (FStar_Syntax_Util.type_u ())
in (match (uu____541) with
| (t, uu____545) -> begin
(

let expected_k = (let _0_309 = (let _0_307 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_306 = (let _0_305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_304 = (let _0_303 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_303)::[])
in (_0_305)::_0_304))
in (_0_307)::_0_306))
in (let _0_308 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _0_309 _0_308)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _0_311 = (let _0_310 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_310 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_311))
in (

let b_wp_a = (let _0_314 = (let _0_312 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name b))
in (_0_312)::[])
in (let _0_313 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_314 _0_313)))
in (

let expected_k = (let _0_321 = (let _0_319 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_318 = (let _0_317 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_316 = (let _0_315 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_0_315)::[])
in (_0_317)::_0_316))
in (_0_319)::_0_318))
in (let _0_320 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_321 _0_320)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _0_329 = (let _0_327 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_326 = (let _0_325 = (FStar_Syntax_Syntax.null_binder (let _0_322 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_322 Prims.fst)))
in (let _0_324 = (let _0_323 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_323)::[])
in (_0_325)::_0_324))
in (_0_327)::_0_326))
in (let _0_328 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_329 _0_328)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _0_337 = (let _0_335 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_334 = (let _0_333 = (FStar_Syntax_Syntax.null_binder (let _0_330 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_330 Prims.fst)))
in (let _0_332 = (let _0_331 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_331)::[])
in (_0_333)::_0_332))
in (_0_335)::_0_334))
in (let _0_336 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_337 _0_336)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _0_340 = (let _0_338 = (FStar_Syntax_Syntax.mk_binder a)
in (_0_338)::[])
in (let _0_339 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_340 _0_339)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____576 = (FStar_Syntax_Util.type_u ())
in (match (uu____576) with
| (t, uu____580) -> begin
(

let expected_k = (let _0_345 = (let _0_343 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_342 = (let _0_341 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_341)::[])
in (_0_343)::_0_342))
in (let _0_344 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_345 _0_344)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____584 = (

let uu____590 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
in (match (uu____590) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| uu____597 -> begin
(

let repr = (

let uu____599 = (FStar_Syntax_Util.type_u ())
in (match (uu____599) with
| (t, uu____603) -> begin
(

let expected_k = (let _0_350 = (let _0_348 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_347 = (let _0_346 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_346)::[])
in (_0_348)::_0_347))
in (let _0_349 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_350 _0_349)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_354 = (let _0_353 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_352 = (let _0_351 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_351)::[])
in (_0_353)::_0_352))
in ((repr), (_0_354)))))) None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _0_355 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _0_355 wp)))
in (

let destruct_repr = (fun t -> (

let uu____645 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____645) with
| FStar_Syntax_Syntax.Tm_app (uu____652, ((t, uu____654))::((wp, uu____656))::[]) -> begin
((t), (wp))
end
| uu____690 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (let _0_356 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _0_356 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____699 = (fresh_effect_signature ())
in (match (uu____699) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_359 = (let _0_357 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_357)::[])
in (let _0_358 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_359 _0_358)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _0_360 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_360))
in (

let wp_g_x = ((let _0_364 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _0_363 = (let _0_362 = (let _0_361 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_361))
in (_0_362)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_364 _0_363))) None FStar_Range.dummyRange)
in (

let res = (

let wp = ((let _0_376 = (let _0_365 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _0_365 Prims.snd))
in (let _0_375 = (let _0_374 = (let _0_373 = (let _0_372 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_371 = (let _0_370 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _0_369 = (let _0_368 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _0_367 = (let _0_366 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_0_366)::[])
in (_0_368)::_0_367))
in (_0_370)::_0_369))
in (_0_372)::_0_371))
in (r)::_0_373)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_374))
in (FStar_Syntax_Syntax.mk_Tm_app _0_376 _0_375))) None FStar_Range.dummyRange)
in (mk_repr b wp))
in (

let expected_k = (let _0_394 = (let _0_392 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_391 = (let _0_390 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_389 = (let _0_388 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _0_387 = (let _0_386 = (FStar_Syntax_Syntax.null_binder (let _0_377 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _0_377)))
in (let _0_385 = (let _0_384 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _0_383 = (let _0_382 = (FStar_Syntax_Syntax.null_binder (let _0_381 = (let _0_378 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_378)::[])
in (let _0_380 = (let _0_379 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_379))
in (FStar_Syntax_Util.arrow _0_381 _0_380))))
in (_0_382)::[])
in (_0_384)::_0_383))
in (_0_386)::_0_385))
in (_0_388)::_0_387))
in (_0_390)::_0_389))
in (_0_392)::_0_391))
in (let _0_393 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_394 _0_393)))
in (

let uu____738 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____738) with
| (expected_k, uu____743, uu____744) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let uu___101_748 = env
in {FStar_TypeChecker_Env.solver = uu___101_748.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_748.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_748.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_748.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___101_748.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_748.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_748.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_748.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_748.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_748.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_748.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_748.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_748.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_748.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_748.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_748.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_748.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_748.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___101_748.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___101_748.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_748.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_748.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___101_748.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _0_395 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_395))
in (

let res = (

let wp = ((let _0_402 = (let _0_396 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _0_396 Prims.snd))
in (let _0_401 = (let _0_400 = (let _0_399 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_398 = (let _0_397 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_0_397)::[])
in (_0_399)::_0_398))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_400))
in (FStar_Syntax_Syntax.mk_Tm_app _0_402 _0_401))) None FStar_Range.dummyRange)
in (mk_repr a wp))
in (

let expected_k = (let _0_407 = (let _0_405 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_404 = (let _0_403 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_403)::[])
in (_0_405)::_0_404))
in (let _0_406 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_407 _0_406)))
in (

let uu____770 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____770) with
| (expected_k, uu____778, uu____779) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____782 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (uu____782) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| uu____794 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____805 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (uu____805) with
| (act_typ, uu____810, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in ((

let uu____814 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____814) with
| true -> begin
(let _0_409 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _0_408 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _0_409 _0_408)))
end
| uu____815 -> begin
()
end));
(

let uu____816 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____816) with
| (act_defn, uu____821, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu____825 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____843 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____843) with
| (bs, uu____849) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _0_410 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _0_410))
in (

let uu____856 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____856) with
| (k, uu____863, g) -> begin
((k), (g))
end))))
end))
end
| uu____865 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_413 = (let _0_412 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _0_411 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _0_412 _0_411)))
in ((_0_413), (act_defn.FStar_Syntax_Syntax.pos))))))
end))
in (match (uu____825) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in ((let _0_416 = (let _0_415 = (let _0_414 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _0_414))
in (FStar_TypeChecker_Rel.conj_guard g_a _0_415))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_416));
(

let act_typ = (

let uu____875 = (FStar_Syntax_Subst.compress expected_k).FStar_Syntax_Syntax.n
in (match (uu____875) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____890 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____890) with
| (bs, c) -> begin
(

let uu____897 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (uu____897) with
| (a, wp) -> begin
(

let c = (let _0_420 = (let _0_417 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_0_417)::[])
in (let _0_419 = (let _0_418 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_418)::[])
in {FStar_Syntax_Syntax.comp_univs = _0_420; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _0_419; FStar_Syntax_Syntax.flags = []}))
in (let _0_421 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _0_421)))
end))
end))
end
| uu____917 -> begin
(failwith "")
end))
in (

let uu____920 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (uu____920) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu___102_926 = act
in {FStar_Syntax_Syntax.action_name = uu___102_926.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___102_926.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____584) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _0_422 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _0_422))
in (

let uu____942 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____942) with
| (univs, t) -> begin
(

let signature = (

let uu____948 = (let _0_423 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((effect_params), (_0_423)))
in (match (uu____948) with
| ([], uu____951) -> begin
t
end
| (uu____957, FStar_Syntax_Syntax.Tm_arrow (uu____958, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____970 -> begin
(failwith "Impossible")
end))
in (

let close = (fun n ts -> (

let ts = (let _0_424 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _0_424))
in (

let m = (FStar_List.length (Prims.fst ts))
in ((

let uu____985 = (((n >= (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && (m <> n))
in (match (uu____985) with
| true -> begin
(

let error = (match ((m < n)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____993 -> begin
"too universe-polymorphic"
end)
in (failwith (let _0_426 = (FStar_Util.string_of_int n)
in (let _0_425 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error _0_426 _0_425)))))
end
| uu____994 -> begin
()
end));
ts;
))))
in (

let close_action = (fun act -> (

let uu____999 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____999) with
| (univs, defn) -> begin
(

let uu____1004 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1004) with
| (univs', typ) -> begin
(

let uu___103_1010 = act
in {FStar_Syntax_Syntax.action_name = uu___103_1010.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___103_1010.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___104_1015 = ed
in (let _0_440 = (close (Prims.parse_int "0") return_wp)
in (let _0_439 = (close (Prims.parse_int "1") bind_wp)
in (let _0_438 = (close (Prims.parse_int "0") if_then_else)
in (let _0_437 = (close (Prims.parse_int "0") ite_wp)
in (let _0_436 = (close (Prims.parse_int "0") stronger)
in (let _0_435 = (close (Prims.parse_int "1") close_wp)
in (let _0_434 = (close (Prims.parse_int "0") assert_p)
in (let _0_433 = (close (Prims.parse_int "0") assume_p)
in (let _0_432 = (close (Prims.parse_int "0") null_wp)
in (let _0_431 = (close (Prims.parse_int "0") trivial_wp)
in (let _0_430 = (Prims.snd (close (Prims.parse_int "0") (([]), (repr))))
in (let _0_429 = (close (Prims.parse_int "0") return_repr)
in (let _0_428 = (close (Prims.parse_int "1") bind_repr)
in (let _0_427 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___104_1015.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___104_1015.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___104_1015.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _0_440; FStar_Syntax_Syntax.bind_wp = _0_439; FStar_Syntax_Syntax.if_then_else = _0_438; FStar_Syntax_Syntax.ite_wp = _0_437; FStar_Syntax_Syntax.stronger = _0_436; FStar_Syntax_Syntax.close_wp = _0_435; FStar_Syntax_Syntax.assert_p = _0_434; FStar_Syntax_Syntax.assume_p = _0_433; FStar_Syntax_Syntax.null_wp = _0_432; FStar_Syntax_Syntax.trivial = _0_431; FStar_Syntax_Syntax.repr = _0_430; FStar_Syntax_Syntax.return_repr = _0_429; FStar_Syntax_Syntax.bind_repr = _0_428; FStar_Syntax_Syntax.actions = _0_427})))))))))))))))
in ((

let uu____1019 = ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED"))))
in (match (uu____1019) with
| true -> begin
(FStar_Util.print_string (FStar_Syntax_Print.eff_decl_to_string false ed))
end
| uu____1020 -> begin
()
end));
ed;
))))))
end)))
end)))))))))))));
)))
end)))))
end))
end))
end)))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let uu____1023 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1023) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1033 = (tc_tparams env effect_binders_un)
in (match (uu____1033) with
| (effect_binders, env, uu____1044) -> begin
(

let uu____1045 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____1045) with
| (signature, uu____1054) -> begin
(

let effect_binders = (FStar_List.map (fun uu____1063 -> (match (uu____1063) with
| (bv, qual) -> begin
(let _0_442 = (

let uu___105_1070 = bv
in (let _0_441 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_1070.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_1070.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_441}))
in ((_0_442), (qual)))
end)) effect_binders)
in (

let uu____1071 = (

let uu____1076 = (FStar_Syntax_Subst.compress signature_un).FStar_Syntax_Syntax.n
in (match (uu____1076) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1082))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1097 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1071) with
| (a, effect_marker) -> begin
(

let a = (

let uu____1114 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1114) with
| true -> begin
(let _0_443 = Some ((FStar_Syntax_Syntax.range_of_bv a))
in (FStar_Syntax_Syntax.gen_bv "a" _0_443 a.FStar_Syntax_Syntax.sort))
end
| uu____1115 -> begin
a
end))
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let uu____1124 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____1124) with
| (t, comp, uu____1132) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1143 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (uu____1143) with
| (repr, _comp) -> begin
((

let uu____1154 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1154) with
| true -> begin
(let _0_444 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _0_444))
end
| uu____1155 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _0_449 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_448 = (let _0_447 = (let _0_446 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_445 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_446), (_0_445))))
in (_0_447)::[])
in ((wp_type), (_0_448))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _0_449))
in (

let effect_signature = (

let binders = (let _0_454 = (let _0_450 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_0_450)))
in (let _0_453 = (let _0_452 = (let _0_451 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _0_451 FStar_Syntax_Syntax.mk_binder))
in (_0_452)::[])
in (_0_454)::_0_453))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let uu____1206 = item
in (match (uu____1206) with
| (u_item, item) -> begin
(

let uu____1218 = (open_and_check item)
in (match (uu____1218) with
| (item, item_comp) -> begin
((

let uu____1228 = (not ((FStar_Syntax_Util.is_total_lcomp item_comp)))
in (match (uu____1228) with
| true -> begin
(Prims.raise (FStar_Errors.Err ((let _0_456 = (FStar_Syntax_Print.term_to_string item)
in (let _0_455 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _0_456 _0_455))))))
end
| uu____1229 -> begin
()
end));
(

let uu____1230 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (uu____1230) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end));
)
end))
end)))
in (

let uu____1243 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1243) with
| (dmff_env, uu____1254, bind_wp, bind_elab) -> begin
(

let uu____1257 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1257) with
| (dmff_env, uu____1268, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (

let uu____1272 = (FStar_Syntax_Subst.compress return_wp).FStar_Syntax_Syntax.n
in (match (uu____1272) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1308 = (

let uu____1316 = (let _0_457 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _0_457))
in (match (uu____1316) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| uu____1357 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1308) with
| (b1, b2, body) -> begin
(

let env0 = (let _0_458 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders _0_458 ((b1)::(b2)::[])))
in (

let wp_b1 = (let _0_463 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_462 = (let _0_461 = (let _0_460 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _0_459 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_460), (_0_459))))
in (_0_461)::[])
in ((wp_type), (_0_462))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _0_463))
in (

let uu____1393 = (let _0_465 = (let _0_464 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _0_464))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _0_465))
in (match (uu____1393) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = ((let _0_469 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _0_468 = (let _0_467 = (let _0_466 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_0_466), (None)))
in (_0_467)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_469 _0_468))) None FStar_Range.dummyRange)
in (let _0_473 = (let _0_471 = (let _0_470 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_470)::[])
in (b1)::_0_471)
in (let _0_472 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _0_473 _0_472 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| uu____1461 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp = (

let uu____1463 = (FStar_Syntax_Subst.compress return_wp).FStar_Syntax_Syntax.n
in (match (uu____1463) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _0_474 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _0_474 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| uu____1514 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp = (

let uu____1516 = (FStar_Syntax_Subst.compress bind_wp).FStar_Syntax_Syntax.n
in (match (uu____1516) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _0_477 = (let _0_476 = (let _0_475 = (FStar_Syntax_Syntax.null_binder (mk (FStar_Syntax_Syntax.Tm_fvar (r))))
in (_0_475)::[])
in (FStar_List.append _0_476 binders))
in (FStar_Syntax_Util.abs _0_477 body what)))
end
| uu____1543 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1560 -> begin
(let _0_479 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_478 = (Prims.snd (FStar_Syntax_Util.args_of_binders effect_binders))
in ((t), (_0_478))))))
in (FStar_Syntax_Subst.close effect_binders _0_479))
end))
in (

let register = (fun name item -> (

let uu____1579 = (let _0_481 = (mk_lid name)
in (let _0_480 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _0_481 _0_480)))
in (match (uu____1579) with
| (sigelt, fv) -> begin
((let _0_483 = (let _0_482 = (FStar_ST.read sigelts)
in (sigelt)::_0_482)
in (FStar_ST.write sigelts _0_483));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((let _0_485 = (let _0_484 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_484)
in (FStar_ST.write sigelts _0_485));
(

let return_elab = (register "return_elab" return_elab)
in ((let _0_487 = (let _0_486 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_486)
in (FStar_ST.write sigelts _0_487));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((let _0_489 = (let _0_488 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_488)
in (FStar_ST.write sigelts _0_489));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((let _0_491 = (let _0_490 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_490)
in (FStar_ST.write sigelts _0_491));
(

let uu____1629 = (FStar_List.fold_left (fun uu____1636 action -> (match (uu____1636) with
| (dmff_env, actions) -> begin
(

let uu____1648 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1648) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _0_495 = (let _0_494 = (

let uu___106_1665 = action
in (let _0_493 = (apply_close action_elab)
in (let _0_492 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___106_1665.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___106_1665.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___106_1665.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_493; FStar_Syntax_Syntax.action_typ = _0_492})))
in (_0_494)::actions)
in ((dmff_env), (_0_495)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____1629) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _0_498 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_497 = (let _0_496 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_496)::[])
in (_0_498)::_0_497))
in (let _0_505 = (let _0_504 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_502 = (let _0_501 = (let _0_500 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_499 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_500), (_0_499))))
in (_0_501)::[])
in ((repr), (_0_502))))))
in (let _0_503 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _0_504 _0_503)))
in (FStar_Syntax_Util.abs binders _0_505 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____1696 = (

let uu____1701 = (let _0_506 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_506)).FStar_Syntax_Syntax.n
in (match (uu____1701) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____1709) -> begin
(

let uu____1736 = (

let uu____1745 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____1745) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____1776 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____1736) with
| (type_param, effect_param, arrow) -> begin
(

let uu____1804 = (let _0_507 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_507)).FStar_Syntax_Syntax.n
in (match (uu____1804) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____1821 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____1821) with
| (wp_binders, c) -> begin
(

let uu____1830 = (FStar_List.partition (fun uu____1841 -> (match (uu____1841) with
| (bv, uu____1845) -> begin
(let _0_509 = (let _0_508 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_508 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _0_509 Prims.op_Negation))
end)) wp_binders)
in (match (uu____1830) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____1877 -> begin
(failwith (let _0_510 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _0_510)))
end)
in (let _0_512 = (FStar_Syntax_Util.arrow pre_args c)
in (let _0_511 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_0_512), (_0_511)))))
end))
end))
end
| uu____1892 -> begin
(failwith (let _0_513 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _0_513)))
end))
end))
end
| uu____1897 -> begin
(failwith (let _0_514 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _0_514)))
end))
in (match (uu____1696) with
| (pre, post) -> begin
((Prims.ignore (register "pre" pre));
(Prims.ignore (register "post" post));
(Prims.ignore (register "wp" wp_type));
(

let ed = (

let uu___107_1917 = ed
in (let _0_525 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _0_524 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _0_523 = (let _0_515 = (apply_close return_wp)
in (([]), (_0_515)))
in (let _0_522 = (let _0_516 = (apply_close bind_wp)
in (([]), (_0_516)))
in (let _0_521 = (apply_close repr)
in (let _0_520 = (let _0_517 = (apply_close return_elab)
in (([]), (_0_517)))
in (let _0_519 = (let _0_518 = (apply_close bind_elab)
in (([]), (_0_518)))
in {FStar_Syntax_Syntax.qualifiers = uu___107_1917.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___107_1917.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___107_1917.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___107_1917.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _0_525; FStar_Syntax_Syntax.signature = _0_524; FStar_Syntax_Syntax.ret_wp = _0_523; FStar_Syntax_Syntax.bind_wp = _0_522; FStar_Syntax_Syntax.if_then_else = uu___107_1917.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___107_1917.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___107_1917.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___107_1917.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___107_1917.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___107_1917.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___107_1917.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___107_1917.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _0_521; FStar_Syntax_Syntax.return_repr = _0_520; FStar_Syntax_Syntax.bind_repr = _0_519; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____1930 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____1930) with
| (sigelts', ed) -> begin
((

let uu____1941 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1941) with
| true -> begin
(FStar_Util.print_string (FStar_Syntax_Print.eff_decl_to_string true ed))
end
| uu____1942 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (let _0_527 = Some ((let _0_526 = (apply_close lift_from_pure_wp)
in (([]), (_0_526))))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _0_527; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____1959 -> begin
None
end)
in (let _0_529 = (let _0_528 = (FStar_List.rev (FStar_ST.read sigelts))
in (FStar_List.append _0_528 sigelts'))
in ((_0_529), (ed), (lift_from_pure_opt))));
)
end)));
)
end))))))
end));
));
));
));
))))))))
end))
end)))))))))));
)
end)))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____1981, uu____1982, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_530, [], uu____1987, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_531, [], uu____1992, r2))::[] when (((_0_530 = (Prims.parse_int "0")) && (_0_531 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t), ((u)::[]), ([]), (t), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]), (r)))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_532 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_532), ((FStar_Syntax_Syntax.U_name (utop))::[])))))) None r1)
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _0_533 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_533))
in (

let hd = (let _0_534 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_534))
in (

let tl = (let _0_536 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_535 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_535), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_536))
in (

let res = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_537 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_537), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))))) None r2)
in (let _0_538 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _0_538))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in FStar_Syntax_Syntax.Sig_bundle ((let _0_539 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_0_539)))))))))))))))))
end
| uu____2114 -> begin
(failwith (let _0_540 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _0_540)))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2126 = (FStar_Syntax_Util.type_u ())
in (match (uu____2126) with
| (k, uu____2130) -> begin
(

let phi = (let _0_541 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _0_541 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _0_543 = (let _0_542 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _0_542))
in (FStar_Errors.diag r _0_543)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
((warn_positivity tc r);
(

let uu____2184 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____2184) with
| (tps, k) -> begin
(

let uu____2193 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____2193) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____2206 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____2206) with
| (indices, t) -> begin
(

let uu____2230 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____2230) with
| (indices, env', guard_indices, us') -> begin
(

let uu____2243 = (

let uu____2246 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____2246) with
| (t, uu____2253, g) -> begin
(let _0_546 = (let _0_545 = (let _0_544 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _0_544))
in (FStar_TypeChecker_Rel.discharge_guard env' _0_545))
in ((t), (_0_546)))
end))
in (match (uu____2243) with
| (t, guard) -> begin
(

let k = (let _0_547 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _0_547))
in (

let uu____2264 = (FStar_Syntax_Util.type_u ())
in (match (uu____2264) with
| (t_type, u) -> begin
((let _0_548 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _0_548));
(

let t_tc = (let _0_549 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _0_549))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _0_550 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_0_550), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end));
)
end
| uu____2289 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun uu____2299 l -> ())
in (

let tc_data = (fun env tcs uu___83_2315 -> (match (uu___83_2315) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____2334 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____2348 -> (match (uu____2348) with
| (se, u_tc) -> begin
(

let uu____2357 = (let _0_551 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _0_551))
in (match (uu____2357) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2366, uu____2367, tps, uu____2369, uu____2370, uu____2371, uu____2372, uu____2373) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2394 -> (match (uu____2394) with
| (x, uu____2401) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in Some ((let _0_552 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_0_552), (tps), (u_tc))))))
end
| uu____2407 -> begin
(failwith "Impossible")
end)
end
| uu____2412 -> begin
None
end))
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid)) with
| true -> begin
((env), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____2437 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____2334) with
| (env, tps, u_tc) -> begin
(

let uu____2446 = (

let uu____2454 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2454) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____2474 = (FStar_Util.first_N ntps bs)
in (match (uu____2474) with
| (uu____2492, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____2524 -> (match (uu____2524) with
| (x, uu____2528) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (FStar_Syntax_Util.arrow_formals (FStar_Syntax_Subst.subst subst t))))
end))
end
| uu____2529 -> begin
(([]), (t))
end))
in (match (uu____2446) with
| (arguments, result) -> begin
((

let uu____2550 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2550) with
| true -> begin
(let _0_555 = (FStar_Syntax_Print.lid_to_string c)
in (let _0_554 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _0_553 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _0_555 _0_554 _0_553))))
end
| uu____2551 -> begin
()
end));
(

let uu____2552 = (tc_tparams env arguments)
in (match (uu____2552) with
| (arguments, env', us) -> begin
(

let uu____2561 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____2561) with
| (result, res_lcomp) -> begin
((

let uu____2569 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____2569) with
| FStar_Syntax_Syntax.Tm_type (uu____2570) -> begin
()
end
| ty -> begin
(Prims.raise (FStar_Errors.Error ((let _0_558 = (let _0_557 = (FStar_Syntax_Print.term_to_string result)
in (let _0_556 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _0_557 _0_556)))
in ((_0_558), (r))))))
end));
(

let uu____2572 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____2572) with
| (head, uu____2585) -> begin
((

let uu____2601 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2601) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____2603 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_561 = (let _0_560 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _0_559 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _0_560 _0_559)))
in ((_0_561), (r))))))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____2608 u_x -> (match (uu____2608) with
| (x, uu____2613) -> begin
(

let _0_562 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _0_562))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _0_565 = (let _0_563 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2630 -> (match (uu____2630) with
| (x, uu____2637) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _0_563 arguments))
in (let _0_564 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _0_565 _0_564)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____2644 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___84_2673 -> (match (uu___84_2673) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2674, uu____2675, tps, k, uu____2678, uu____2679, uu____2680, uu____2681) -> begin
(FStar_Syntax_Syntax.null_binder (let _0_566 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _0_566)))
end
| uu____2692 -> begin
(failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___85_2697 -> (match (uu___85_2697) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2698, uu____2699, t, uu____2701, uu____2702, uu____2703, uu____2704, uu____2705) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____2710 -> begin
(failwith "Impossible")
end))))
in (

let t = (let _0_567 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _0_567))
in ((

let uu____2715 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2715) with
| true -> begin
(let _0_568 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _0_568))
end
| uu____2716 -> begin
()
end));
(

let uu____2717 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____2717) with
| (uvs, t) -> begin
((

let uu____2727 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2727) with
| true -> begin
(let _0_571 = (let _0_569 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _0_569 (FStar_String.concat ", ")))
in (let _0_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _0_571 _0_570)))
end
| uu____2732 -> begin
()
end));
(

let uu____2733 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____2733) with
| (uvs, t) -> begin
(

let uu____2742 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2742) with
| (args, uu____2755) -> begin
(

let uu____2766 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____2766) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____2801 se -> (match (uu____2801) with
| (x, uu____2806) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2808, tps, uu____2810, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____2822 = (

let uu____2830 = (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n
in (match (uu____2830) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2850 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____2850) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____2893 -> begin
(let _0_572 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _0_572 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____2914 -> begin
(([]), (ty))
end))
in (match (uu____2822) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____2940 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____2944 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_573 -> FStar_Syntax_Syntax.U_name (_0_573))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___86_2961 -> (match (uu___86_2961) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2966, uu____2967, uu____2968, uu____2969, uu____2970, uu____2971, uu____2972) -> begin
((tc), (uvs_universes))
end
| uu____2980 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____2986 d -> (match (uu____2986) with
| (t, uu____2991) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____2993, uu____2994, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _0_574 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_574 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____3007 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end));
)
end));
))));
))
in (

let uu____3010 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___87_3020 -> (match (uu___87_3020) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3021) -> begin
true
end
| uu____3033 -> begin
false
end))))
in (match (uu____3010) with
| (tys, datas) -> begin
((

let uu____3045 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___88_3047 -> (match (uu___88_3047) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3048) -> begin
false
end
| uu____3059 -> begin
true
end))))
in (match (uu____3045) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_575 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_0_575))))))
end
| uu____3060 -> begin
()
end));
(

let env0 = env
in (

let uu____3062 = (FStar_List.fold_right (fun tc uu____3076 -> (match (uu____3076) with
| (env, all_tcs, g) -> begin
(

let uu____3098 = (tc_tycon env tc)
in (match (uu____3098) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3115 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3115) with
| true -> begin
(let _0_576 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _0_576))
end
| uu____3116 -> begin
()
end));
(let _0_578 = (let _0_577 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _0_577))
in ((env), ((((tc), (tc_u)))::all_tcs), (_0_578)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3062) with
| (env, tcs, g) -> begin
(

let uu____3140 = (FStar_List.fold_right (fun se uu____3148 -> (match (uu____3148) with
| (datas, g) -> begin
(

let uu____3159 = (tc_data env tcs se)
in (match (uu____3159) with
| (data, g') -> begin
(let _0_579 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_0_579)))
end))
end)) datas (([]), (g)))
in (match (uu____3140) with
| (datas, g) -> begin
(

let uu____3177 = (let _0_580 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _0_580 datas))
in (match (uu____3177) with
| (tcs, datas) -> begin
(

let sig_bndle = FStar_Syntax_Syntax.Sig_bundle ((let _0_581 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_581))))
in (

let data_ops_ses = (let _0_582 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right _0_582 FStar_List.flatten))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3208, uu____3209, t, uu____3211, uu____3212, uu____3213, uu____3214, uu____3215) -> begin
t
end
| uu____3220 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun uu____3226 -> (

let haseq_ty = (fun usubst us acc ty -> (

let uu____3270 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3282, bs, t, uu____3285, d_lids, uu____3287, uu____3288) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____3296 -> begin
(failwith "Impossible!")
end)
in (match (uu____3270) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_583 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_583 t))
in (

let uu____3326 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____3326) with
| (bs, t) -> begin
(

let ibs = (

let uu____3346 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3346) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3351) -> begin
ibs
end
| uu____3362 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_585 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_584 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_585 _0_584)))
in (

let ind = ((let _0_587 = (FStar_List.map (fun uu____3379 -> (match (uu____3379) with
| (bv, aq) -> begin
(let _0_586 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_586), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_587)) None dr)
in (

let ind = ((let _0_589 = (FStar_List.map (fun uu____3397 -> (match (uu____3397) with
| (bv, aq) -> begin
(let _0_588 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_588), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_589)) None dr)
in (

let haseq_ind = ((let _0_591 = (let _0_590 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_590)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_591)) None dr)
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____3420 = acc
in (match (uu____3420) with
| (uu____3428, en, uu____3430, uu____3431) -> begin
(

let opt = (let _0_592 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _0_592 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____3440) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _0_595 = ((let _0_594 = (let _0_593 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name (Prims.fst b)))
in (_0_593)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_594)) None dr)
in (FStar_Syntax_Util.mk_conj t _0_595))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___108_3454 = fml
in (let _0_599 = FStar_Syntax_Syntax.Tm_meta ((let _0_598 = FStar_Syntax_Syntax.Meta_pattern ((let _0_597 = (let _0_596 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_596)::[])
in (_0_597)::[]))
in ((fml), (_0_598))))
in {FStar_Syntax_Syntax.n = _0_599; FStar_Syntax_Syntax.tk = uu___108_3454.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___108_3454.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_3454.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_602 = (let _0_601 = (FStar_Syntax_Syntax.as_arg (let _0_600 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_600 None)))
in (_0_601)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_602)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_605 = (let _0_604 = (FStar_Syntax_Syntax.as_arg (let _0_603 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_603 None)))
in (_0_604)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_605)) None dr)) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____3506 = acc
in (match (uu____3506) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3540, uu____3541, uu____3542, t_lid, uu____3544, uu____3545, uu____3546, uu____3547) -> begin
(t_lid = lid)
end
| uu____3552 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____3559 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3559) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3561) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_606 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_606 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = ((let _0_608 = (let _0_607 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_607)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_608)) None dr)
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _0_610 = (let _0_609 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _0_609))
in (FStar_TypeChecker_Util.label _0_610 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> ((let _0_613 = (let _0_612 = (FStar_Syntax_Syntax.as_arg (let _0_611 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_611 None)))
in (_0_612)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_613)) None dr)) dbs cond)))))
end
| uu____3622 -> begin
FStar_Syntax_Util.t_true
end)))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _0_614 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _0_614))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _0_616 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _0_615 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_0_616), (_0_615))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3642, us, uu____3644, uu____3645, uu____3646, uu____3647, uu____3648, uu____3649) -> begin
us
end
| uu____3656 -> begin
(failwith "Impossible!")
end))
in (

let uu____3657 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3657) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____3673 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____3673) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____3705 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____3705) with
| (phi, uu____3710) -> begin
((

let uu____3712 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____3712) with
| true -> begin
(let _0_617 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_617))
end
| uu____3713 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____3720 -> (match (uu____3720) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
ses;
));
)
end)))
end)));
))
end)))))
in (

let unoptimized_haseq_scheme = (fun uu____3733 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3739, uu____3740, uu____3741, uu____3742, uu____3743, uu____3744, uu____3745) -> begin
lid
end
| uu____3752 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let uu____3772 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3784, bs, t, uu____3787, d_lids, uu____3789, uu____3790) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____3798 -> begin
(failwith "Impossible!")
end)
in (match (uu____3772) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_618 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_618 t))
in (

let uu____3819 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____3819) with
| (bs, t) -> begin
(

let ibs = (

let uu____3830 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3830) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3835) -> begin
ibs
end
| uu____3846 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_620 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_619 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_620 _0_619)))
in (

let ind = ((let _0_622 = (FStar_List.map (fun uu____3863 -> (match (uu____3863) with
| (bv, aq) -> begin
(let _0_621 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_621), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_622)) None dr)
in (

let ind = ((let _0_624 = (FStar_List.map (fun uu____3881 -> (match (uu____3881) with
| (bv, aq) -> begin
(let _0_623 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_623), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_624)) None dr)
in (

let haseq_ind = ((let _0_626 = (let _0_625 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_625)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_626)) None dr)
in (

let rec is_mutual = (fun t -> (

let uu____3905 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3905) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____3913) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____3940 = (is_mutual t')
in (match (uu____3940) with
| true -> begin
true
end
| uu____3941 -> begin
(exists_mutual (FStar_List.map Prims.fst args))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____3951) -> begin
(is_mutual t')
end
| uu____3956 -> begin
false
end)))
and exists_mutual = (fun uu___89_3957 -> (match (uu___89_3957) with
| [] -> begin
false
end
| (hd)::tl -> begin
((is_mutual hd) || (exists_mutual tl))
end))
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____3983 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3983) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3987) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_627 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_627 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = ((let _0_629 = (let _0_628 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_628)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_629)) None dr)
in (

let haseq_sort = (

let uu____4030 = (is_mutual sort)
in (match (uu____4030) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____4031 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> ((let _0_632 = (let _0_631 = (FStar_Syntax_Syntax.as_arg (let _0_630 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_630 None)))
in (_0_631)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_632)) None dr)) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____4053 -> begin
acc
end)))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4057, uu____4058, uu____4059, t_lid, uu____4061, uu____4062, uu____4063, uu____4064) -> begin
(t_lid = lid)
end
| uu____4069 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___109_4075 = fml
in (let _0_636 = FStar_Syntax_Syntax.Tm_meta ((let _0_635 = FStar_Syntax_Syntax.Meta_pattern ((let _0_634 = (let _0_633 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_633)::[])
in (_0_634)::[]))
in ((fml), (_0_635))))
in {FStar_Syntax_Syntax.n = _0_636; FStar_Syntax_Syntax.tk = uu___109_4075.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___109_4075.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_4075.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_639 = (let _0_638 = (FStar_Syntax_Syntax.as_arg (let _0_637 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_637 None)))
in (_0_638)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_639)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_642 = (let _0_641 = (FStar_Syntax_Syntax.as_arg (let _0_640 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_640 None)))
in (_0_641)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_642)) None dr)) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let uu____4124 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____4132, uu____4133, uu____4134, uu____4135, uu____4136, uu____4137) -> begin
((lid), (us))
end
| uu____4144 -> begin
(failwith "Impossible!")
end))
in (match (uu____4124) with
| (lid, us) -> begin
(

let uu____4150 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4150) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _0_643 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _0_643 fml [] dr))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end)))))
in (

let skip_prims_type = (fun uu____4172 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4176, uu____4177, uu____4178, uu____4179, uu____4180, uu____4181, uu____4182) -> begin
lid
end
| uu____4189 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____4195 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____4195) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____4204 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(unoptimized_haseq_scheme ())
end
| uu____4210 -> begin
(optimized_haseq_scheme ())
end)
in (let _0_646 = (let _0_645 = FStar_Syntax_Syntax.Sig_bundle ((let _0_644 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_644))))
in (_0_645)::ses)
in ((_0_646), (data_ops_ses)))))
end))))))))))
end))
end))
end)));
)
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env se);
(match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _0_647 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_0_647), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4263 = (tc_inductive env ses quals lids)
in (match (uu____4263) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____4293 = (FStar_Options.set_options t s)
in (match (uu____4293) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____4301 -> begin
()
end);
(((se)::[]), (env), ([]));
)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
((set_options FStar_Options.Set o);
(((se)::[]), (env), ([]));
)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((let _0_648 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _0_648 Prims.ignore));
(match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(((se)::[]), (env), ([]));
)
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____4316) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let uu____4329 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____4340 a -> (match (uu____4340) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (let _0_649 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_0_649), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____4329) with
| (env, ses) -> begin
(((se)::[]), (env), ([]))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let uu____4370 = (let _0_650 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_650))
in (match (uu____4370) with
| (a, wp_a_src) -> begin
(

let uu____4386 = (let _0_651 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _0_651))
in (match (uu____4386) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _0_654 = (let _0_653 = FStar_Syntax_Syntax.NT ((let _0_652 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_0_652))))
in (_0_653)::[])
in (FStar_Syntax_Subst.subst _0_654 wp_b_tgt))
in (

let expected_k = (let _0_659 = (let _0_657 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_656 = (let _0_655 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_0_655)::[])
in (_0_657)::_0_656))
in (let _0_658 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _0_659 _0_658)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (Prims.raise (FStar_Errors.Error ((let _0_661 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _0_660 = (FStar_TypeChecker_Env.get_range env)
in ((_0_661), (_0_660))))))))
in (

let uu____4426 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____4426) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____4433 = (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))))
in (match (uu____4433) with
| true -> begin
(no_reify eff_name)
end
| uu____4437 -> begin
(let _0_666 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_665 = (let _0_664 = (FStar_Syntax_Syntax.as_arg a)
in (let _0_663 = (let _0_662 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_662)::[])
in (_0_664)::_0_663))
in ((repr), (_0_665)))))) None _0_666))
end)))
end))))
in (

let uu____4447 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____4462, lift_wp)) -> begin
(let _0_667 = (check_and_gen env lift_wp expected_k)
in ((lift), (_0_667)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____4489 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____4489) with
| (uu____4496, lift_wp, lift_elab) -> begin
(

let uu____4499 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____4500 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____4447) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___110_4524 = env
in {FStar_TypeChecker_Env.solver = uu___110_4524.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_4524.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_4524.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_4524.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_4524.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_4524.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_4524.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_4524.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_4524.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_4524.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_4524.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_4524.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_4524.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_4524.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_4524.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_4524.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_4524.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_4524.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_4524.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_4524.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_4524.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_4524.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_4524.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____4528, lift) -> begin
(

let uu____4535 = (let _0_668 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_668))
in (match (uu____4535) with
| (a, wp_a_src) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env (Prims.snd lift_wp))
in (

let lift_wp_a = (let _0_673 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_672 = (let _0_671 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _0_670 = (let _0_669 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_0_669)::[])
in (_0_671)::_0_670))
in ((lift_wp), (_0_672)))))) None _0_673))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _0_680 = (let _0_678 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_677 = (let _0_676 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _0_675 = (let _0_674 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_0_674)::[])
in (_0_676)::_0_675))
in (_0_678)::_0_677))
in (let _0_679 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _0_680 _0_679)))
in (

let uu____4573 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____4573) with
| (expected_k, uu____4579, uu____4580) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___111_4583 = env
in {FStar_TypeChecker_Env.solver = uu___111_4583.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_4583.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_4583.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_4583.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_4583.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_4583.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_4583.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_4583.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_4583.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_4583.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_4583.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_4583.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_4583.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_4583.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_4583.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_4583.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_4583.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_4583.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___111_4583.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_4583.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_4583.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_4583.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_4583.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___112_4585 = sub
in {FStar_Syntax_Syntax.source = uu___112_4585.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___112_4585.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])))))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, flags, r) -> begin
(

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4604 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____4604) with
| (tps, c) -> begin
(

let uu____4614 = (tc_tparams env tps)
in (match (uu____4614) with
| (tps, env, us) -> begin
(

let uu____4626 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____4626) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____4641 = (let _0_681 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _0_681))
in (match (uu____4641) with
| (uvs, t) -> begin
(

let uu____4659 = (

let uu____4667 = (let _0_682 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((tps), (_0_682)))
in (match (uu____4667) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____4677, c)) -> begin
(([]), (c))
end
| (uu____4701, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____4719 -> begin
(failwith "Impossible")
end))
in (match (uu____4659) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____4749 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____4749) with
| (uu____4752, t) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_686 = (let _0_685 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_684 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _0_683 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _0_685 _0_684 _0_683))))
in ((_0_686), (r))))))
end))
end
| uu____4756 -> begin
()
end);
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (flags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env), ([]))));
)
end))
end))));
)
end))
end))
end))))
end
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___90_4785 -> (match (uu___90_4785) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____4786 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4797 = (match ((uvs = [])) with
| true -> begin
(let _0_687 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (check_and_gen env t _0_687))
end
| uu____4798 -> begin
(

let uu____4799 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____4799) with
| (uvs, t) -> begin
(let _0_690 = (let _0_689 = (let _0_688 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (tc_check_trivial_guard env t _0_688))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_689))
in ((uvs), (_0_690)))
end))
end)
in (match (uu____4797) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let uu____4833 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____4833) with
| (e, c, g1) -> begin
(

let uu____4845 = (let _0_693 = Some ((FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r))
in (let _0_692 = (let _0_691 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_0_691)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _0_693 _0_692)))
in (match (uu____4845) with
| (e, uu____4857, g) -> begin
((let _0_694 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_694));
(

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals, attrs) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
(

let uu____4901 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____4901) with
| true -> begin
Some (q)
end
| uu____4909 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_698 = (let _0_697 = (FStar_Syntax_Print.lid_to_string l)
in (let _0_696 = (FStar_Syntax_Print.quals_to_string q)
in (let _0_695 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _0_697 _0_696 _0_695))))
in ((_0_698), (r))))))
end))
end))
in (

let uu____4912 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____4933 lb -> (match (uu____4933) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4957 = (

let uu____4963 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4963) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____4988 -> begin
((gen), (lb), (quals_opt))
end)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in ((match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| uu____5015 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____5022 -> begin
()
end);
(let _0_699 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_0_699), (quals_opt)));
))
end))
in (match (uu____4957) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____5053 -> begin
Some (quals)
end)))))
in (match (uu____4912) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____5076 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___91_5078 -> (match (uu___91_5078) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____5079 -> begin
false
end))))
in (match (uu____5076) with
| true -> begin
q
end
| uu____5081 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_700 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_0_700)))))) None r)
in (

let uu____5110 = (

let uu____5116 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___113_5120 = env
in {FStar_TypeChecker_Env.solver = uu___113_5120.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_5120.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_5120.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_5120.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_5120.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_5120.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_5120.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_5120.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_5120.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_5120.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_5120.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___113_5120.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___113_5120.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_5120.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_5120.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_5120.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_5120.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_5120.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_5120.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_5120.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_5120.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_5120.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____5116) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____5128; FStar_Syntax_Syntax.pos = uu____5129; FStar_Syntax_Syntax.vars = uu____5130}, uu____5131, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5150, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____5155 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____5165 -> begin
(failwith "impossible")
end))
in (match (uu____5110) with
| (se, lbs) -> begin
((

let uu____5188 = (log env)
in (match (uu____5188) with
| true -> begin
(let _0_705 = (let _0_704 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____5195 = (let _0_701 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (FStar_TypeChecker_Env.try_lookup_val_decl env _0_701))
in (match (uu____5195) with
| None -> begin
true
end
| uu____5207 -> begin
false
end))
in (match (should_log) with
| true -> begin
(let _0_703 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_702 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _0_703 _0_702)))
end
| uu____5212 -> begin
""
end)))))
in (FStar_All.pipe_right _0_704 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _0_705))
end
| uu____5213 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])));
)
end)))))
end))))
end);
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___92_5240 -> (match (uu___92_5240) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____5241 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____5249 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____5254) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____5267, r) -> begin
(

let uu____5275 = (is_abstract quals)
in (match (uu____5275) with
| true -> begin
(FStar_List.fold_right (fun se uu____5285 -> (match (uu____5285) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____5308, uu____5309, quals, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((let _0_707 = (let _0_706 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _0_706))
in ((l), (us), (_0_707), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r))))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____5327, uu____5328, uu____5329, uu____5330, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____5340 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____5345 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____5348, uu____5349, quals, uu____5351) -> begin
(

let uu____5354 = (is_abstract quals)
in (match (uu____5354) with
| true -> begin
(([]), (hidden))
end
| uu____5361 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____5371 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____5371) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____5380 -> begin
(

let uu____5381 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___93_5383 -> (match (uu___93_5383) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____5386 -> begin
false
end))))
in (match (uu____5381) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____5393 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____5396) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____5408, uu____5409, quals, uu____5411) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5429 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____5429) with
| true -> begin
(([]), (hidden))
end
| uu____5437 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____5453) -> begin
(

let uu____5460 = (is_abstract quals)
in (match (uu____5460) with
| true -> begin
(let _0_709 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> FStar_Syntax_Syntax.Sig_declare_typ ((let _0_708 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in ((_0_708), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))))))
in ((_0_709), (hidden)))
end
| uu____5479 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____5516 se -> (match (uu____5516) with
| (ses, exports, env, hidden) -> begin
((

let uu____5547 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5547) with
| true -> begin
(let _0_710 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _0_710))
end
| uu____5548 -> begin
()
end));
(

let uu____5549 = (tc_decl env se)
in (match (uu____5549) with
| (ses', env, ses_elaborated) -> begin
((

let uu____5571 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____5571) with
| true -> begin
(let _0_713 = (FStar_List.fold_left (fun s se -> (let _0_712 = (let _0_711 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _0_711 "\n"))
in (Prims.strcat s _0_712))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _0_713))
end
| uu____5574 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____5577 = (FStar_List.fold_left (fun uu____5586 se -> (match (uu____5586) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____5577) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____5642 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____5679 = acc
in (match (uu____5679) with
| (uu____5696, uu____5697, env, uu____5699) -> begin
(

let uu____5708 = (cps_and_elaborate env ne)
in (match (uu____5708) with
| (ses, ne, lift_from_pure_opt) -> begin
(

let ses = (match (lift_from_pure_opt) with
| Some (lift) -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::(lift)::[]))
end
| None -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
end)
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| uu____5741 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____5642) with
| (ses, exports, env, uu____5755) -> begin
(let _0_714 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_0_714), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____5783 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5785 -> begin
"implementation"
end)
in ((

let uu____5787 = (FStar_Options.debug_any ())
in (match (uu____5787) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____5788 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5790 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___114_5793 = env
in {FStar_TypeChecker_Env.solver = uu___114_5793.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_5793.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_5793.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_5793.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_5793.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_5793.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_5793.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_5793.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_5793.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_5793.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_5793.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_5793.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_5793.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_5793.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_5793.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_5793.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___114_5793.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_5793.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_5793.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_5793.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_5793.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_5793.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____5796 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____5796) with
| (ses, exports, env) -> begin
(((

let uu___115_5814 = modul
in {FStar_Syntax_Syntax.name = uu___115_5814.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___115_5814.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___115_5814.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____5830 = (tc_decls env decls)
in (match (uu____5830) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___116_5848 = modul
in {FStar_Syntax_Syntax.name = uu___116_5848.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___116_5848.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___116_5848.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___117_5862 = env
in {FStar_TypeChecker_Env.solver = uu___117_5862.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_5862.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_5862.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_5862.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_5862.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_5862.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_5862.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_5862.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_5862.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_5862.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_5862.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_5862.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_5862.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___117_5862.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_5862.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_5862.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_5862.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___117_5862.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_5862.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_5862.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_5862.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____5873 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____5873) with
| (univs, t) -> begin
((

let uu____5879 = (let _0_715 = (FStar_TypeChecker_Env.debug (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name))
in (FStar_All.pipe_left _0_715 (FStar_Options.Other ("Exports"))))
in (match (uu____5879) with
| true -> begin
(let _0_719 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_718 = (let _0_716 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _0_716 (FStar_String.concat ", ")))
in (let _0_717 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _0_719 _0_718 _0_717))))
end
| uu____5883 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _0_720 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _0_720 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((FStar_Errors.message_prefix.FStar_Errors.set_prefix (let _0_722 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _0_721 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _0_722 _0_721))));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___94_5904 -> (match (uu___94_5904) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____5907, uu____5908) -> begin
(

let uu____5915 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5915) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____5918 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____5923, uu____5924, uu____5925, r) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_723 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_0_723)))))) None r)
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____5947, uu____5948, uu____5949, uu____5950, uu____5951) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____5960) -> begin
(

let uu____5963 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5963) with
| true -> begin
(check_term l univs t)
end
| uu____5965 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____5966, lbs), uu____5968, uu____5969, quals, uu____5971) -> begin
(

let uu____5983 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5983) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____5992 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____6004 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6004) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____6017 -> begin
()
end))
end
| (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
()
end))
in (match ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
()
end
| uu____6024 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___118_6037 = modul
in {FStar_Syntax_Syntax.name = uu___118_6037.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___118_6037.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____6040 = (not ((FStar_Options.lax ())))
in (match (uu____6040) with
| true -> begin
(check_exports env modul exports)
end
| uu____6041 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____6046 = (not ((FStar_Options.interactive ())))
in (match (uu____6046) with
| true -> begin
(let _0_724 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _0_724 Prims.ignore))
end
| uu____6047 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____6056 = (tc_partial_modul env modul)
in (match (uu____6056) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____6077 = (FStar_Options.debug_any ())
in (match (uu____6077) with
| true -> begin
(let _0_725 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____6078 -> begin
"module"
end) _0_725))
end
| uu____6079 -> begin
()
end));
(

let env = (

let uu___119_6081 = env
in (let _0_726 = (not ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = uu___119_6081.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_6081.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_6081.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_6081.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_6081.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_6081.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_6081.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_6081.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_6081.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_6081.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_6081.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_6081.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_6081.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_6081.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_6081.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_6081.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_6081.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_6081.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _0_726; FStar_TypeChecker_Env.lax_universes = uu___119_6081.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_6081.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_6081.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_6081.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_6081.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6082 = (tc_modul env m)
in (match (uu____6082) with
| (m, env) -> begin
((

let uu____6090 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____6090) with
| true -> begin
(let _0_727 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _0_727))
end
| uu____6091 -> begin
()
end));
(

let uu____6093 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____6093) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___95_6097 -> (match (uu___95_6097) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____6124 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____6124) with
| (univnames, e) -> begin
(

let uu___120_6129 = lb
in (let _0_729 = (let _0_728 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n _0_728 e))
in {FStar_Syntax_Syntax.lbname = uu___120_6129.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___120_6129.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___120_6129.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___120_6129.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_729}))
end)))
in FStar_Syntax_Syntax.Sig_let ((let _0_731 = (let _0_730 = (FStar_List.map update lbs)
in ((b), (_0_730)))
in ((_0_731), (r), (ids), (qs), (attrs))))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___121_6139 = m
in (let _0_732 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___121_6139.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _0_732; FStar_Syntax_Syntax.exports = uu___121_6139.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___121_6139.FStar_Syntax_Syntax.is_interface}))
in (let _0_733 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" _0_733))))
end
| uu____6140 -> begin
()
end));
((m), (env));
)
end)));
))




