
open Prims
type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let uu___94_64 = a
in (

let uu____65 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___94_64.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___94_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____65}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in ((

let uu____73 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____73) with
| true -> begin
((d "Elaborating extra WP combinators");
(

let uu____75 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" uu____75));
)
end
| uu____76 -> begin
()
end));
(

let rec collect_binders = (fun t -> (

let uu____84 = (

let uu____85 = (

let uu____88 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____88))
in uu____85.FStar_Syntax_Syntax.n)
in (match (uu____84) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____110) -> begin
t
end
| uu____117 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (

let uu____120 = (collect_binders rest)
in (FStar_List.append bs uu____120)))
end
| FStar_Syntax_Syntax.Tm_type (uu____126) -> begin
[]
end
| uu____129 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (

let uu____141 = (collect_binders wp_a)
in (FStar_All.pipe_right uu____141 FStar_Syntax_Util.name_binders))
in ((

let uu____152 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____152) with
| true -> begin
(

let uu____153 = (

let uu____154 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" uu____154))
in (d uu____153))
end
| uu____155 -> begin
()
end));
(

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange))
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let register = (fun env lident def -> (

let uu____186 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (uu____186) with
| (sigelt, fv) -> begin
((

let uu____192 = (

let uu____194 = (FStar_ST.read sigelts)
in (sigelt)::uu____194)
in (FStar_ST.write sigelts uu____192));
fv;
)
end)))
in (

let binders_of_list = (FStar_List.map (fun uu____215 -> (match (uu____215) with
| (t, b) -> begin
(

let uu____222 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (uu____222)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (

let uu____239 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (uu____239)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (

let uu____252 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg uu____252))))
in (

let uu____253 = (

let uu____265 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (

let uu____285 = (f (FStar_Syntax_Syntax.bv_to_name t))
in (FStar_Syntax_Util.arrow gamma uu____285))
in (

let uu____288 = (

let uu____292 = (

let uu____296 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____297 = (

let uu____299 = (FStar_Syntax_Syntax.mk_binder t)
in (uu____299)::[])
in (uu____296)::uu____297))
in (FStar_List.append binders uu____292))
in (FStar_Syntax_Util.abs uu____288 body None)))))
in (

let uu____307 = (mk FStar_Syntax_Syntax.mk_Total)
in (

let uu____308 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((uu____307), (uu____308)))))
in (match (uu____265) with
| (ctx_def, gctx_def) -> begin
(

let ctx_lid = (mk_lid "ctx")
in (

let ctx_fv = (register env ctx_lid ctx_def)
in (

let gctx_lid = (mk_lid "gctx")
in (

let gctx_fv = (register env gctx_lid gctx_def)
in (

let mk_app = (fun fv t -> (

let uu____339 = (

let uu____340 = (

let uu____350 = (

let uu____354 = (FStar_List.map (fun uu____362 -> (match (uu____362) with
| (bv, uu____368) -> begin
(

let uu____369 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____370 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____369), (uu____370))))
end)) binders)
in (

let uu____371 = (

let uu____375 = (

let uu____378 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____379 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____378), (uu____379))))
in (

let uu____380 = (

let uu____384 = (

let uu____387 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (uu____387)))
in (uu____384)::[])
in (uu____375)::uu____380))
in (FStar_List.append uu____354 uu____371)))
in ((fv), (uu____350)))
in FStar_Syntax_Syntax.Tm_app (uu____340))
in (mk uu____339)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (uu____253) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (

let uu____433 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None uu____433))
in (

let ret = (

let uu____441 = (

let uu____447 = (

let uu____448 = (

let uu____451 = (

let uu____452 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx uu____452))
in (FStar_Syntax_Syntax.mk_Total uu____451))
in (FStar_Syntax_Util.lcomp_of_comp uu____448))
in FStar_Util.Inl (uu____447))
in Some (uu____441))
in (

let body = (

let uu____462 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma uu____462 ret))
in (

let uu____463 = (

let uu____467 = (mk_all_implicit binders)
in (

let uu____471 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append uu____467 uu____471)))
in (FStar_Syntax_Util.abs uu____463 body ret))))))
in (

let c_pure = (

let uu____486 = (mk_lid "pure")
in (register env uu____486 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (

let uu____491 = (

let uu____492 = (

let uu____493 = (

let uu____497 = (

let uu____498 = (

let uu____499 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None uu____499))
in (FStar_Syntax_Syntax.mk_binder uu____498))
in (uu____497)::[])
in (

let uu____500 = (

let uu____503 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____503))
in (FStar_Syntax_Util.arrow uu____493 uu____500)))
in (mk_gctx uu____492))
in (FStar_Syntax_Syntax.gen_bv "l" None uu____491))
in (

let r = (

let uu____505 = (

let uu____506 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____506))
in (FStar_Syntax_Syntax.gen_bv "r" None uu____505))
in (

let ret = (

let uu____514 = (

let uu____520 = (

let uu____521 = (

let uu____524 = (

let uu____525 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____525))
in (FStar_Syntax_Syntax.mk_Total uu____524))
in (FStar_Syntax_Util.lcomp_of_comp uu____521))
in FStar_Util.Inl (uu____520))
in Some (uu____514))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (

let uu____540 = (FStar_Syntax_Syntax.bv_to_name l)
in (

let uu____543 = (

let uu____549 = (

let uu____551 = (

let uu____552 = (

let uu____553 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app uu____553 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg uu____552))
in (uu____551)::[])
in (FStar_List.append gamma_as_args uu____549))
in (FStar_Syntax_Util.mk_app uu____540 uu____543)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (

let uu____556 = (

let uu____560 = (mk_all_implicit binders)
in (

let uu____564 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append uu____560 uu____564)))
in (FStar_Syntax_Util.abs uu____556 outer_body ret))))))))
in (

let c_app = (

let uu____583 = (mk_lid "app")
in (register env uu____583 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____590 = (

let uu____594 = (

let uu____595 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____595))
in (uu____594)::[])
in (

let uu____596 = (

let uu____599 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____599))
in (FStar_Syntax_Util.arrow uu____590 uu____596)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (

let uu____602 = (

let uu____603 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____603))
in (FStar_Syntax_Syntax.gen_bv "a1" None uu____602))
in (

let ret = (

let uu____611 = (

let uu____617 = (

let uu____618 = (

let uu____621 = (

let uu____622 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____622))
in (FStar_Syntax_Syntax.mk_Total uu____621))
in (FStar_Syntax_Util.lcomp_of_comp uu____618))
in FStar_Util.Inl (uu____617))
in Some (uu____611))
in (

let uu____631 = (

let uu____635 = (mk_all_implicit binders)
in (

let uu____639 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append uu____635 uu____639)))
in (

let uu____657 = (

let uu____658 = (

let uu____664 = (

let uu____666 = (

let uu____669 = (

let uu____675 = (

let uu____677 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____677)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____675))
in (FStar_Syntax_Util.mk_app c_pure uu____669))
in (

let uu____678 = (

let uu____682 = (FStar_Syntax_Syntax.bv_to_name a1)
in (uu____682)::[])
in (uu____666)::uu____678))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____664))
in (FStar_Syntax_Util.mk_app c_app uu____658))
in (FStar_Syntax_Util.abs uu____631 uu____657 ret)))))))))
in (

let c_lift1 = (

let uu____686 = (mk_lid "lift1")
in (register env uu____686 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____694 = (

let uu____698 = (

let uu____699 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____699))
in (

let uu____700 = (

let uu____702 = (

let uu____703 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder uu____703))
in (uu____702)::[])
in (uu____698)::uu____700))
in (

let uu____704 = (

let uu____707 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal uu____707))
in (FStar_Syntax_Util.arrow uu____694 uu____704)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (

let uu____710 = (

let uu____711 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____711))
in (FStar_Syntax_Syntax.gen_bv "a1" None uu____710))
in (

let a2 = (

let uu____713 = (

let uu____714 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____714))
in (FStar_Syntax_Syntax.gen_bv "a2" None uu____713))
in (

let ret = (

let uu____722 = (

let uu____728 = (

let uu____729 = (

let uu____732 = (

let uu____733 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx uu____733))
in (FStar_Syntax_Syntax.mk_Total uu____732))
in (FStar_Syntax_Util.lcomp_of_comp uu____729))
in FStar_Util.Inl (uu____728))
in Some (uu____722))
in (

let uu____742 = (

let uu____746 = (mk_all_implicit binders)
in (

let uu____750 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append uu____746 uu____750)))
in (

let uu____772 = (

let uu____773 = (

let uu____779 = (

let uu____781 = (

let uu____784 = (

let uu____790 = (

let uu____792 = (

let uu____795 = (

let uu____801 = (

let uu____803 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____803)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____801))
in (FStar_Syntax_Util.mk_app c_pure uu____795))
in (

let uu____804 = (

let uu____808 = (FStar_Syntax_Syntax.bv_to_name a1)
in (uu____808)::[])
in (uu____792)::uu____804))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____790))
in (FStar_Syntax_Util.mk_app c_app uu____784))
in (

let uu____811 = (

let uu____815 = (FStar_Syntax_Syntax.bv_to_name a2)
in (uu____815)::[])
in (uu____781)::uu____811))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____779))
in (FStar_Syntax_Util.mk_app c_app uu____773))
in (FStar_Syntax_Util.abs uu____742 uu____772 ret)))))))))))
in (

let c_lift2 = (

let uu____819 = (mk_lid "lift2")
in (register env uu____819 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____826 = (

let uu____830 = (

let uu____831 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____831))
in (uu____830)::[])
in (

let uu____832 = (

let uu____835 = (

let uu____836 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____836))
in (FStar_Syntax_Syntax.mk_Total uu____835))
in (FStar_Syntax_Util.arrow uu____826 uu____832)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (

let uu____845 = (

let uu____851 = (

let uu____852 = (

let uu____855 = (

let uu____856 = (

let uu____857 = (

let uu____861 = (

let uu____862 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____862))
in (uu____861)::[])
in (

let uu____863 = (

let uu____866 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____866))
in (FStar_Syntax_Util.arrow uu____857 uu____863)))
in (mk_ctx uu____856))
in (FStar_Syntax_Syntax.mk_Total uu____855))
in (FStar_Syntax_Util.lcomp_of_comp uu____852))
in FStar_Util.Inl (uu____851))
in Some (uu____845))
in (

let e1 = (

let uu____876 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None uu____876))
in (

let body = (

let uu____878 = (

let uu____882 = (

let uu____886 = (FStar_Syntax_Syntax.mk_binder e1)
in (uu____886)::[])
in (FStar_List.append gamma uu____882))
in (

let uu____889 = (

let uu____890 = (FStar_Syntax_Syntax.bv_to_name f)
in (

let uu____893 = (

let uu____899 = (

let uu____900 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg uu____900))
in (

let uu____901 = (args_of_binders gamma)
in (uu____899)::uu____901))
in (FStar_Syntax_Util.mk_app uu____890 uu____893)))
in (FStar_Syntax_Util.abs uu____878 uu____889 ret)))
in (

let uu____903 = (

let uu____907 = (mk_all_implicit binders)
in (

let uu____911 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append uu____907 uu____911)))
in (FStar_Syntax_Util.abs uu____903 body ret)))))))))
in (

let c_push = (

let uu____928 = (mk_lid "push")
in (register env uu____928 c_push))
in (

let ret_tot_wp_a = (

let uu____936 = (

let uu____942 = (

let uu____943 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp uu____943))
in FStar_Util.Inl (uu____942))
in Some (uu____936))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____971 = (

let uu____972 = (

let uu____982 = (args_of_binders binders)
in ((c), (uu____982)))
in FStar_Syntax_Syntax.Tm_app (uu____972))
in (mk uu____971))
end
| uu____987 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (

let uu____990 = (

let uu____991 = (

let uu____995 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____996 = (

let uu____998 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____998)::[])
in (uu____995)::uu____996))
in (

let uu____999 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____991 uu____999)))
in (FStar_Syntax_Syntax.mk_Total uu____990))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (

let uu____1003 = (

let uu____1007 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders uu____1007))
in (

let uu____1013 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (

let uu____1015 = (

let uu____1018 = (

let uu____1024 = (

let uu____1026 = (

let uu____1029 = (

let uu____1035 = (

let uu____1036 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg uu____1036))
in (uu____1035)::[])
in (FStar_Syntax_Util.mk_app l_ite uu____1029))
in (uu____1026)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1024))
in (FStar_Syntax_Util.mk_app c_lift2 uu____1018))
in (FStar_Syntax_Util.ascribe uu____1015 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs uu____1003 uu____1013 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (

let uu____1052 = (mk_lid "wp_if_then_else")
in (register env uu____1052 wp_if_then_else))
in (

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (

let uu____1063 = (

let uu____1069 = (

let uu____1071 = (

let uu____1074 = (

let uu____1080 = (

let uu____1082 = (

let uu____1085 = (

let uu____1091 = (

let uu____1092 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1092))
in (uu____1091)::[])
in (FStar_Syntax_Util.mk_app l_and uu____1085))
in (uu____1082)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1080))
in (FStar_Syntax_Util.mk_app c_pure uu____1074))
in (

let uu____1097 = (

let uu____1101 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1101)::[])
in (uu____1071)::uu____1097))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1069))
in (FStar_Syntax_Util.mk_app c_app uu____1063))
in (

let uu____1104 = (

let uu____1108 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1108))
in (FStar_Syntax_Util.abs uu____1104 body ret_tot_wp_a))))))
in (

let wp_assert = (

let uu____1115 = (mk_lid "wp_assert")
in (register env uu____1115 wp_assert))
in (

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (

let uu____1126 = (

let uu____1132 = (

let uu____1134 = (

let uu____1137 = (

let uu____1143 = (

let uu____1145 = (

let uu____1148 = (

let uu____1154 = (

let uu____1155 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1155))
in (uu____1154)::[])
in (FStar_Syntax_Util.mk_app l_imp uu____1148))
in (uu____1145)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1143))
in (FStar_Syntax_Util.mk_app c_pure uu____1137))
in (

let uu____1160 = (

let uu____1164 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1164)::[])
in (uu____1134)::uu____1160))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1132))
in (FStar_Syntax_Util.mk_app c_app uu____1126))
in (

let uu____1167 = (

let uu____1171 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1171))
in (FStar_Syntax_Util.abs uu____1167 body ret_tot_wp_a))))))
in (

let wp_assume = (

let uu____1178 = (mk_lid "wp_assume")
in (register env uu____1178 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1187 = (

let uu____1191 = (

let uu____1192 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1192))
in (uu____1191)::[])
in (

let uu____1193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1187 uu____1193)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (

let uu____1200 = (

let uu____1206 = (

let uu____1208 = (

let uu____1211 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure uu____1211))
in (

let uu____1217 = (

let uu____1221 = (

let uu____1224 = (

let uu____1230 = (

let uu____1232 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1232)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1230))
in (FStar_Syntax_Util.mk_app c_push uu____1224))
in (uu____1221)::[])
in (uu____1208)::uu____1217))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1206))
in (FStar_Syntax_Util.mk_app c_app uu____1200))
in (

let uu____1239 = (

let uu____1243 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders uu____1243))
in (FStar_Syntax_Util.abs uu____1239 body ret_tot_wp_a))))))
in (

let wp_close = (

let uu____1250 = (mk_lid "wp_close")
in (register env uu____1250 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (

let uu____1261 = (

let uu____1267 = (

let uu____1268 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____1268))
in FStar_Util.Inl (uu____1267))
in Some (uu____1261))
in (

let ret_gtot_type = (

let uu____1288 = (

let uu____1294 = (

let uu____1295 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____1295))
in FStar_Util.Inl (uu____1294))
in Some (uu____1288))
in (

let mk_forall = (fun x body -> (

let uu____1315 = (

let uu____1318 = (

let uu____1319 = (

let uu____1329 = (

let uu____1331 = (

let uu____1332 = (

let uu____1333 = (

let uu____1337 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1337)::[])
in (FStar_Syntax_Util.abs uu____1333 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg uu____1332))
in (uu____1331)::[])
in ((FStar_Syntax_Util.tforall), (uu____1329)))
in FStar_Syntax_Syntax.Tm_app (uu____1319))
in (FStar_Syntax_Syntax.mk uu____1318))
in (uu____1315 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (

let uu____1351 = (

let uu____1352 = (FStar_Syntax_Subst.compress t)
in uu____1352.FStar_Syntax_Syntax.n)
in (match (uu____1351) with
| FStar_Syntax_Syntax.Tm_type (uu____1355) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____1370 -> (match (uu____1370) with
| (b, uu____1374) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____1375 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____1380 = (

let uu____1381 = (FStar_Syntax_Subst.compress t)
in uu____1381.FStar_Syntax_Syntax.n)
in (match (uu____1380) with
| FStar_Syntax_Syntax.Tm_type (uu____1384) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____1399 -> (match (uu____1399) with
| (b, uu____1403) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____1404 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____1456 = (

let uu____1457 = (FStar_Syntax_Subst.compress t)
in uu____1457.FStar_Syntax_Syntax.n)
in (match (uu____1456) with
| FStar_Syntax_Syntax.Tm_type (uu____1460) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____1506 = ((is_monotonic a) || (is_monotonic b))
in (match (uu____1506) with
| true -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (

let uu____1509 = (

let uu____1512 = (

let uu____1518 = (

let uu____1519 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1519))
in (uu____1518)::[])
in (FStar_Syntax_Util.mk_app x uu____1512))
in (

let uu____1520 = (

let uu____1523 = (

let uu____1529 = (

let uu____1530 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1530))
in (uu____1529)::[])
in (FStar_Syntax_Util.mk_app y uu____1523))
in (mk_rel b uu____1509 uu____1520)))
in (mk_forall a1 body)))
end
| uu____1531 -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (

let uu____1535 = (

let uu____1536 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____1539 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a uu____1536 uu____1539)))
in (

let uu____1542 = (

let uu____1543 = (

let uu____1546 = (

let uu____1552 = (

let uu____1553 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1553))
in (uu____1552)::[])
in (FStar_Syntax_Util.mk_app x uu____1546))
in (

let uu____1554 = (

let uu____1557 = (

let uu____1563 = (

let uu____1564 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg uu____1564))
in (uu____1563)::[])
in (FStar_Syntax_Util.mk_app y uu____1557))
in (mk_rel b uu____1543 uu____1554)))
in (FStar_Syntax_Util.mk_imp uu____1535 uu____1542)))
in (

let uu____1565 = (mk_forall a2 body)
in (mk_forall a1 uu____1565)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let uu___95_1586 = t
in (

let uu____1587 = (

let uu____1588 = (

let uu____1596 = (

let uu____1597 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total uu____1597))
in (((binder)::[]), (uu____1596)))
in FStar_Syntax_Syntax.Tm_arrow (uu____1588))
in {FStar_Syntax_Syntax.n = uu____1587; FStar_Syntax_Syntax.tk = uu___95_1586.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___95_1586.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___95_1586.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1609) -> begin
(failwith "unhandled arrow")
end
| uu____1617 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end)))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let rec mk_stronger = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____1632 = (

let uu____1633 = (FStar_Syntax_Subst.compress t)
in uu____1633.FStar_Syntax_Syntax.n)
in (match (uu____1632) with
| FStar_Syntax_Syntax.Tm_type (uu____1636) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (

let uu____1653 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor uu____1653)) -> begin
(

let project = (fun i tuple -> (

let projector = (

let uu____1668 = (

let uu____1669 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env uu____1669 i))
in (FStar_Syntax_Syntax.fvar uu____1668 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let uu____1690 = (

let uu____1694 = (FStar_List.mapi (fun i uu____1699 -> (match (uu____1699) with
| (t, q) -> begin
(

let uu____1704 = (project i x)
in (

let uu____1705 = (project i y)
in (mk_stronger t uu____1704 uu____1705)))
end)) args)
in (match (uu____1694) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____1690) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____1761 -> (match (uu____1761) with
| (bv, q) -> begin
(

let uu____1766 = (

let uu____1767 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____1767))
in (FStar_Syntax_Syntax.gen_bv uu____1766 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (

let uu____1771 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____1771))) bvs)
in (

let body = (

let uu____1773 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____1774 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____1773 uu____1774)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| uu____1777 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (

let uu____1779 = (FStar_Syntax_Util.unascribe wp_a)
in (

let uu____1780 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (

let uu____1781 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger uu____1779 uu____1780 uu____1781))))
in (

let uu____1782 = (

let uu____1786 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders uu____1786))
in (FStar_Syntax_Util.abs uu____1782 body ret_tot_type))))))
in (

let stronger = (

let uu____1801 = (mk_lid "stronger")
in (register env uu____1801 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1807 = (FStar_Util.prefix gamma)
in (match (uu____1807) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (

let uu____1833 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm uu____1833))
in (

let uu____1836 = (FStar_Syntax_Util.destruct_typ_as_formula eq)
in (match (uu____1836) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (

let uu____1844 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm uu____1844))
in (

let guard_free = (

let uu____1851 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1851))
in (

let pat = (

let uu____1855 = (

let uu____1861 = (FStar_Syntax_Syntax.as_arg k_app)
in (uu____1861)::[])
in (FStar_Syntax_Util.mk_app guard_free uu____1855))
in (

let pattern_guarded_body = (

let uu____1865 = (

let uu____1866 = (

let uu____1871 = (

let uu____1872 = (

let uu____1879 = (

let uu____1881 = (FStar_Syntax_Syntax.as_arg pat)
in (uu____1881)::[])
in (uu____1879)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____1872))
in ((body), (uu____1871)))
in FStar_Syntax_Syntax.Tm_meta (uu____1866))
in (mk uu____1865))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| uu____1884 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (

let uu____1887 = (

let uu____1888 = (

let uu____1889 = (

let uu____1890 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1893 = (

let uu____1899 = (args_of_binders wp_args)
in (

let uu____1901 = (

let uu____1903 = (

let uu____1904 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg uu____1904))
in (uu____1903)::[])
in (FStar_List.append uu____1899 uu____1901)))
in (FStar_Syntax_Util.mk_app uu____1890 uu____1893)))
in (FStar_Syntax_Util.mk_imp equiv uu____1889))
in (FStar_Syntax_Util.mk_forall k uu____1888))
in (FStar_Syntax_Util.abs gamma uu____1887 ret_gtot_type))
in (

let uu____1905 = (

let uu____1909 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders uu____1909))
in (FStar_Syntax_Util.abs uu____1905 body ret_gtot_type)))))
end)))
in (

let wp_ite = (

let uu____1916 = (mk_lid "wp_ite")
in (register env uu____1916 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1922 = (FStar_Util.prefix gamma)
in (match (uu____1922) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (

let uu____1946 = (

let uu____1947 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (

let uu____1950 = (

let uu____1956 = (

let uu____1957 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____1957))
in (uu____1956)::[])
in (FStar_Syntax_Util.mk_app uu____1947 uu____1950)))
in (FStar_Syntax_Util.mk_forall x uu____1946))
in (

let uu____1958 = (

let uu____1962 = (

let uu____1966 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append uu____1966 gamma))
in (FStar_List.append binders uu____1962))
in (FStar_Syntax_Util.abs uu____1958 body ret_gtot_type))))
end)))
in (

let null_wp = (

let uu____1975 = (mk_lid "null_wp")
in (register env uu____1975 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (

let uu____1984 = (

let uu____1990 = (

let uu____1992 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1993 = (

let uu____1995 = (

let uu____1998 = (

let uu____2004 = (

let uu____2005 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg uu____2005))
in (uu____2004)::[])
in (FStar_Syntax_Util.mk_app null_wp uu____1998))
in (

let uu____2006 = (

let uu____2010 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____2010)::[])
in (uu____1995)::uu____2006))
in (uu____1992)::uu____1993))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1990))
in (FStar_Syntax_Util.mk_app stronger uu____1984))
in (

let uu____2013 = (

let uu____2017 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders uu____2017))
in (FStar_Syntax_Util.abs uu____2013 body ret_tot_type))))
in (

let wp_trivial = (

let uu____2024 = (mk_lid "wp_trivial")
in (register env uu____2024 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in ((

let uu____2029 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____2029) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____2030 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (

let uu____2034 = (

let uu____2036 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2036))
in (

let uu____2041 = (

let uu___96_2042 = ed
in (

let uu____2043 = (

let uu____2044 = (c wp_if_then_else)
in (([]), (uu____2044)))
in (

let uu____2046 = (

let uu____2047 = (c wp_ite)
in (([]), (uu____2047)))
in (

let uu____2049 = (

let uu____2050 = (c stronger)
in (([]), (uu____2050)))
in (

let uu____2052 = (

let uu____2053 = (c wp_close)
in (([]), (uu____2053)))
in (

let uu____2055 = (

let uu____2056 = (c wp_assert)
in (([]), (uu____2056)))
in (

let uu____2058 = (

let uu____2059 = (c wp_assume)
in (([]), (uu____2059)))
in (

let uu____2061 = (

let uu____2062 = (c null_wp)
in (([]), (uu____2062)))
in (

let uu____2064 = (

let uu____2065 = (c wp_trivial)
in (([]), (uu____2065)))
in {FStar_Syntax_Syntax.qualifiers = uu___96_2042.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___96_2042.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___96_2042.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___96_2042.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___96_2042.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___96_2042.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___96_2042.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___96_2042.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu____2043; FStar_Syntax_Syntax.ite_wp = uu____2046; FStar_Syntax_Syntax.stronger = uu____2049; FStar_Syntax_Syntax.close_wp = uu____2052; FStar_Syntax_Syntax.assert_p = uu____2055; FStar_Syntax_Syntax.assume_p = uu____2058; FStar_Syntax_Syntax.null_wp = uu____2061; FStar_Syntax_Syntax.trivial = uu____2064; FStar_Syntax_Syntax.repr = uu___96_2042.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___96_2042.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___96_2042.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___96_2042.FStar_Syntax_Syntax.actions})))))))))
in ((uu____2034), (uu____2041)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____2081 -> begin
false
end))


let __proj__N__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| N (_0) -> begin
_0
end))


let uu___is_M : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| M (_0) -> begin
true
end
| uu____2093 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun uu___83_2103 -> (match (uu___83_2103) with
| FStar_Syntax_Syntax.Total (t, uu____2105) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___82_2114 -> (match (uu___82_2114) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2115 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let uu____2117 = (

let uu____2118 = (

let uu____2119 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2119))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2118))
in (failwith uu____2117))
end
| FStar_Syntax_Syntax.GTotal (uu____2120) -> begin
(failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___84_2128 -> (match (uu___84_2128) with
| N (t) -> begin
(

let uu____2130 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" uu____2130))
end
| M (t) -> begin
(

let uu____2132 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" uu____2132))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2136, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = uu____2138; FStar_Syntax_Syntax.pos = uu____2139; FStar_Syntax_Syntax.vars = uu____2140}) -> begin
(nm_of_comp n)
end
| uu____2151 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (

let uu____2163 = (nm_of_comp c.FStar_Syntax_Syntax.n)
in (match (uu____2163) with
| M (uu____2164) -> begin
true
end
| N (uu____2165) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____2169 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ -> (

let uu____2179 = (

let uu____2183 = (

let uu____2184 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2184))
in (uu____2183)::[])
in (

let uu____2185 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____2179 uu____2185))))
in (

let uu____2188 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once uu____2188))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (mk (

let uu____2223 = (

let uu____2231 = (

let uu____2235 = (

let uu____2238 = (

let uu____2239 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv uu____2239))
in (

let uu____2240 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2238), (uu____2240))))
in (uu____2235)::[])
in (

let uu____2245 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____2231), (uu____2245))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2223))))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____2278) -> begin
(

let binders = (FStar_List.map (fun uu____2297 -> (match (uu____2297) with
| (bv, aqual) -> begin
(

let uu____2304 = (

let uu___97_2305 = bv
in (

let uu____2306 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___97_2305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___97_2305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2306}))
in ((uu____2304), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2309, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____2311); FStar_Syntax_Syntax.tk = uu____2312; FStar_Syntax_Syntax.pos = uu____2313; FStar_Syntax_Syntax.vars = uu____2314}) -> begin
(

let uu____2331 = (

let uu____2332 = (

let uu____2340 = (

let uu____2341 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal uu____2341))
in ((binders), (uu____2340)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2332))
in (mk uu____2331))
end
| uu____2345 -> begin
(

let uu____2346 = (is_monadic_arrow t.FStar_Syntax_Syntax.n)
in (match (uu____2346) with
| N (hn) -> begin
(

let uu____2348 = (

let uu____2349 = (

let uu____2357 = (

let uu____2358 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total uu____2358))
in ((binders), (uu____2357)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2349))
in (mk uu____2348))
end
| M (a) -> begin
(

let uu____2363 = (

let uu____2364 = (

let uu____2372 = (

let uu____2376 = (

let uu____2380 = (

let uu____2383 = (

let uu____2384 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv uu____2384))
in (

let uu____2385 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2383), (uu____2385))))
in (uu____2380)::[])
in (FStar_List.append binders uu____2376))
in (

let uu____2392 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____2372), (uu____2392))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2364))
in (mk uu____2363))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let debug = (fun t s -> (

let string_of_set = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(

let uu____2443 = (f x)
in (FStar_Util.string_builder_append strb uu____2443));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2447 = (f x)
in (FStar_Util.string_builder_append strb uu____2447));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (

let uu____2449 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2450 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" uu____2449 uu____2450)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (

let uu____2458 = (

let uu____2459 = (FStar_Syntax_Subst.compress ty)
in uu____2459.FStar_Syntax_Syntax.n)
in (match (uu____2458) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2474 = (

let uu____2475 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (not (uu____2475)))
in (match (uu____2474) with
| true -> begin
false
end
| uu____2476 -> begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (

let uu____2489 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect uu____2489 s))
in (

let uu____2491 = (

let uu____2492 = (FStar_Util.set_is_empty sinter)
in (not (uu____2492)))
in (match (uu____2491) with
| true -> begin
((debug ty sinter);
(Prims.raise Not_found);
)
end
| uu____2494 -> begin
()
end))))
in (

let uu____2495 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2495) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s uu____2506 -> (match (uu____2506) with
| (bv, uu____2512) -> begin
((non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort);
(FStar_Util.set_add bv s);
)
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in ((non_dependent_or_raise s ct);
(

let k = (n - (FStar_List.length binders))
in (match ((k > (Prims.parse_int "0"))) with
| true -> begin
(is_non_dependent_arrow ct k)
end
| uu____2523 -> begin
true
end));
)))
end)))
end)
with
| Not_found -> begin
false
end
end))
end
| uu____2525 -> begin
((

let uu____2527 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" uu____2527));
false;
)
end)))
in (

let rec is_valid_application = (fun head -> (

let uu____2532 = (

let uu____2533 = (FStar_Syntax_Subst.compress head)
in uu____2533.FStar_Syntax_Syntax.n)
in (match (uu____2532) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (

let uu____2537 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor uu____2537))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____2550) -> begin
true
end
| uu____2560 -> begin
((

let uu____2562 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" uu____2562));
false;
)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2566) -> begin
(is_valid_application t)
end
| uu____2571 -> begin
false
end)))
in (

let uu____2572 = (is_valid_application head)
in (match (uu____2572) with
| true -> begin
(

let uu____2573 = (

let uu____2574 = (

let uu____2584 = (FStar_List.map (fun uu____2594 -> (match (uu____2594) with
| (t, qual) -> begin
(

let uu____2607 = (star_type' env t)
in ((uu____2607), (qual)))
end)) args)
in ((head), (uu____2584)))
in FStar_Syntax_Syntax.Tm_app (uu____2574))
in (mk uu____2573))
end
| uu____2613 -> begin
(

let uu____2614 = (

let uu____2615 = (

let uu____2616 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" uu____2616))
in FStar_Errors.Err (uu____2615))
in (Prims.raise uu____2614))
end)))))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____2646 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____2646) with
| (binders, repr) -> begin
(

let env = (

let uu___100_2652 = env
in (

let uu____2653 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = uu____2653; subst = uu___100_2652.subst; tc_const = uu___100_2652.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, t) when false -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv x)
in (

let sort = (star_type' env x.FStar_Syntax_Syntax.sort)
in (

let subst = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let t = (star_type' env t)
in (

let subst = (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___101_2670 = x
in {FStar_Syntax_Syntax.ppname = uu___101_2670.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_2670.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(

let uu____2677 = (

let uu____2678 = (

let uu____2683 = (star_type' env t)
in ((uu____2683), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2678))
in (mk uu____2677))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(

let uu____2705 = (

let uu____2706 = (

let uu____2719 = (star_type' env e)
in (

let uu____2720 = (

let uu____2725 = (star_type' env t)
in FStar_Util.Inl (uu____2725))
in ((uu____2719), (uu____2720), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2706))
in (mk uu____2705))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2733) -> begin
(

let uu____2746 = (

let uu____2747 = (

let uu____2748 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" uu____2748))
in FStar_Errors.Err (uu____2747))
in (Prims.raise uu____2746))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2749) -> begin
(

let uu____2754 = (

let uu____2755 = (

let uu____2756 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" uu____2756))
in FStar_Errors.Err (uu____2755))
in (Prims.raise uu____2754))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2757) -> begin
(

let uu____2762 = (

let uu____2763 = (

let uu____2764 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" uu____2764))
in FStar_Errors.Err (uu____2763))
in (Prims.raise uu____2762))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2765) -> begin
(

let uu____2766 = (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" uu____2768))
in FStar_Errors.Err (uu____2767))
in (Prims.raise uu____2766))
end
| FStar_Syntax_Syntax.Tm_match (uu____2769) -> begin
(

let uu____2785 = (

let uu____2786 = (

let uu____2787 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" uu____2787))
in FStar_Errors.Err (uu____2786))
in (Prims.raise uu____2785))
end
| FStar_Syntax_Syntax.Tm_let (uu____2788) -> begin
(

let uu____2796 = (

let uu____2797 = (

let uu____2798 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" uu____2798))
in FStar_Errors.Err (uu____2797))
in (Prims.raise uu____2796))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2799) -> begin
(

let uu____2808 = (

let uu____2809 = (

let uu____2810 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" uu____2810))
in FStar_Errors.Err (uu____2809))
in (Prims.raise uu____2808))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2811 = (

let uu____2812 = (

let uu____2813 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" uu____2813))
in FStar_Errors.Err (uu____2812))
in (Prims.raise uu____2811))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2814) -> begin
(failwith "impossible")
end)))))


let is_monadic = (fun uu___86_2847 -> (match (uu___86_2847) with
| None -> begin
(failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (_, flags))) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___85_2884 -> (match (uu___85_2884) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2885 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____2889 = (

let uu____2890 = (FStar_Syntax_Subst.compress t)
in uu____2890.FStar_Syntax_Syntax.n)
in (match (uu____2889) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (

let uu____2910 = (

let uu____2911 = (FStar_List.hd args)
in (Prims.fst uu____2911))
in (is_C uu____2910))
in (match (r) with
| true -> begin
((

let uu____2923 = (

let uu____2924 = (FStar_List.for_all (fun uu____2927 -> (match (uu____2927) with
| (h, uu____2931) -> begin
(is_C h)
end)) args)
in (not (uu____2924)))
in (match (uu____2923) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____2932 -> begin
()
end));
true;
)
end
| uu____2933 -> begin
((

let uu____2935 = (

let uu____2936 = (FStar_List.for_all (fun uu____2939 -> (match (uu____2939) with
| (h, uu____2943) -> begin
(

let uu____2944 = (is_C h)
in (not (uu____2944)))
end)) args)
in (not (uu____2936)))
in (match (uu____2935) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____2945 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____2958 = (nm_of_comp comp.FStar_Syntax_Syntax.n)
in (match (uu____2958) with
| M (t) -> begin
((

let uu____2961 = (is_C t)
in (match (uu____2961) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____2962 -> begin
()
end));
true;
)
end
| N (t) -> begin
(is_C t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_C t)
end
| uu____2988 -> begin
false
end)))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (

let uu____3019 = (

let uu____3020 = (

let uu____3030 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____3031 = (

let uu____3035 = (

let uu____3038 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (uu____3038)))
in (uu____3035)::[])
in ((uu____3030), (uu____3031))))
in FStar_Syntax_Syntax.Tm_app (uu____3020))
in (mk uu____3019))
in (

let uu____3046 = (

let uu____3050 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____3050)::[])
in (

let uu____3051 = (

let uu____3058 = (

let uu____3064 = (

let uu____3065 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.lcomp_of_comp uu____3065))
in FStar_Util.Inl (uu____3064))
in Some (uu____3058))
in (FStar_Syntax_Util.abs uu____3046 body uu____3051))))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___87_3078 -> (match (uu___87_3078) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____3079 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun uu____3223 -> (match (uu____3223) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> (

let uu____3244 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (

let uu____3245 = (

let uu____3246 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial uu____3246))
in (not (uu____3245))))
in (match (uu____3244) with
| true -> begin
(

let uu____3247 = (

let uu____3248 = (

let uu____3249 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3250 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____3251 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" uu____3249 uu____3250 uu____3251))))
in FStar_Errors.Err (uu____3248))
in (Prims.raise uu____3247))
end
| uu____3252 -> begin
()
end)))
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
((check t1 t2);
((rec_nm), (s_e), (u_e));
)
end
| (N (t1), M (t2)) -> begin
((check t1 t2);
(

let uu____3262 = (mk_return env t1 s_e)
in ((M (t1)), (uu____3262), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(

let uu____3265 = (

let uu____3266 = (

let uu____3267 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3268 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____3269 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" uu____3267 uu____3268 uu____3269))))
in FStar_Errors.Err (uu____3266))
in (Prims.raise uu____3265))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun uu___88_3295 -> (match (uu___88_3295) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____3305 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(

let uu____3316 = (

let uu____3317 = (

let uu____3320 = (

let uu____3321 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " uu____3321))
in ((uu____3320), (e2.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3317))
in (Prims.raise uu____3316))
end
| M (uu____3325) -> begin
(

let uu____3326 = (check env e2 context_nm)
in (strip_m uu____3326))
end)))
in (

let uu____3330 = (

let uu____3331 = (FStar_Syntax_Subst.compress e)
in uu____3331.FStar_Syntax_Syntax.n)
in (match (uu____3330) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(

let uu____3343 = (infer env e)
in (return_if uu____3343))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____3413) -> begin
(

let uu____3421 = (

let uu____3422 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" uu____3422))
in (failwith uu____3421))
end
| FStar_Syntax_Syntax.Tm_type (uu____3426) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3430) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____3441) -> begin
(

let uu____3446 = (

let uu____3447 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" uu____3447))
in (failwith uu____3446))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3451) -> begin
(

let uu____3460 = (

let uu____3461 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" uu____3461))
in (failwith uu____3460))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3465) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3489 = (

let uu____3490 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" uu____3490))
in (failwith uu____3489))
end))))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (

let uu____3512 = (

let uu____3513 = (FStar_Syntax_Subst.compress e)
in uu____3513.FStar_Syntax_Syntax.n)
in (match (uu____3512) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let body = (FStar_Syntax_Subst.subst subst body)
in (

let env = (

let uu___102_3553 = env
in (

let uu____3554 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = uu____3554; subst = uu___102_3553.subst; tc_const = uu___102_3553.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____3563 -> (match (uu____3563) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let uu___103_3571 = bv
in {FStar_Syntax_Syntax.ppname = uu___103_3571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_3571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let uu____3572 = (FStar_List.fold_left (fun uu____3581 uu____3582 -> (match (((uu____3581), (uu____3582))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____3610 = (is_C c)
in (match (uu____3610) with
| true -> begin
(

let xw = (

let uu____3615 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None uu____3615))
in (

let x = (

let uu___104_3617 = bv
in (

let uu____3618 = (

let uu____3621 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c uu____3621))
in {FStar_Syntax_Syntax.ppname = uu___104_3617.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_3617.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3618}))
in (

let env = (

let uu___105_3623 = env
in (

let uu____3624 = (

let uu____3626 = (

let uu____3627 = (

let uu____3632 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (uu____3632)))
in FStar_Syntax_Syntax.NT (uu____3627))
in (uu____3626)::env.subst)
in {env = uu___105_3623.env; subst = uu____3624; tc_const = uu___105_3623.tc_const}))
in (

let uu____3633 = (

let uu____3635 = (FStar_Syntax_Syntax.mk_binder x)
in (

let uu____3636 = (

let uu____3638 = (FStar_Syntax_Syntax.mk_binder xw)
in (uu____3638)::acc)
in (uu____3635)::uu____3636))
in ((env), (uu____3633))))))
end
| uu____3640 -> begin
(

let x = (

let uu___106_3642 = bv
in (

let uu____3643 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___106_3642.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_3642.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3643}))
in (

let uu____3646 = (

let uu____3648 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3648)::acc)
in ((env), (uu____3646))))
end)))
end)) ((env), ([])) binders)
in (match (uu____3572) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let uu____3660 = (

let check_what = (

let uu____3672 = (is_monadic what)
in (match (uu____3672) with
| true -> begin
check_m
end
| uu____3680 -> begin
check_n
end))
in (

let uu____3681 = (check_what env body)
in (match (uu____3681) with
| (t, s_body, u_body) -> begin
(

let uu____3691 = (

let uu____3692 = (

let uu____3693 = (is_monadic what)
in (match (uu____3693) with
| true -> begin
M (t)
end
| uu____3694 -> begin
N (t)
end))
in (comp_of_nm uu____3692))
in ((uu____3691), (s_body), (u_body)))
end)))
in (match (uu____3660) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____3736 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___89_3738 -> (match (uu___89_3738) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____3739 -> begin
false
end))))
in (match (uu____3736) with
| true -> begin
(

let double_starred_comp = (

let uu____3747 = (

let uu____3748 = (

let uu____3749 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result uu____3749))
in (FStar_All.pipe_left double_star uu____3748))
in (FStar_Syntax_Syntax.mk_Total uu____3747))
in (

let flags = (FStar_List.filter (fun uu___90_3754 -> (match (uu___90_3754) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____3755 -> begin
true
end)) lc.FStar_Syntax_Syntax.cflags)
in (

let uu____3756 = (

let uu____3762 = (

let uu____3763 = (FStar_Syntax_Util.comp_set_flags double_starred_comp flags)
in (FStar_Syntax_Util.lcomp_of_comp uu____3763))
in FStar_Util.Inl (uu____3762))
in Some (uu____3756))))
end
| uu____3774 -> begin
Some (FStar_Util.Inl ((

let uu___107_3783 = lc
in {FStar_Syntax_Syntax.eff_name = uu___107_3783.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___107_3783.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___107_3783.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3784 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ))))})))
end))
end
| Some (FStar_Util.Inr (lid, flags)) -> begin
(

let uu____3801 = (

let uu____3807 = (

let uu____3811 = (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___91_3813 -> (match (uu___91_3813) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____3814 -> begin
false
end))))
in (match (uu____3811) with
| true -> begin
(

let uu____3818 = (FStar_List.filter (fun uu___92_3820 -> (match (uu___92_3820) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____3821 -> begin
true
end)) flags)
in ((FStar_Syntax_Const.effect_Tot_lid), (uu____3818)))
end
| uu____3823 -> begin
((lid), (flags))
end))
in FStar_Util.Inr (uu____3807))
in Some (uu____3801))
end)
in (

let uu____3833 = (

let comp = (

let uu____3845 = (is_monadic what)
in (

let uu____3846 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) uu____3845 uu____3846)))
in (

let uu____3847 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((uu____3847), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (uu____3833) with
| (u_body, u_what) -> begin
(

let s_body = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (mk (FStar_Syntax_Syntax.Tm_abs (((s_binders), (s_body), (s_what)))))
in (

let u_body = (FStar_Syntax_Subst.close u_binders u_body)
in (

let u_binders = (FStar_Syntax_Subst.close_binders u_binders)
in (

let u_term = (mk (FStar_Syntax_Syntax.Tm_abs (((u_binders), (u_body), (u_what)))))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = uu____3916; FStar_Syntax_Syntax.p = uu____3917}; FStar_Syntax_Syntax.fv_delta = uu____3918; FStar_Syntax_Syntax.fv_qual = uu____3919}) -> begin
(

let uu____3925 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (uu____3925) with
| (uu____3931, t) -> begin
(

let uu____3933 = (

let uu____3934 = (normalize t)
in N (uu____3934))
in ((uu____3933), (e), (e)))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____3951 = (check_n env head)
in (match (uu____3951) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____3965 = (

let uu____3966 = (FStar_Syntax_Subst.compress t)
in uu____3966.FStar_Syntax_Syntax.n)
in (match (uu____3965) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3969) -> begin
true
end
| uu____3977 -> begin
false
end)))
in (

let rec flatten = (fun t -> (

let uu____3989 = (

let uu____3990 = (FStar_Syntax_Subst.compress t)
in uu____3990.FStar_Syntax_Syntax.n)
in (match (uu____3989) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, uu____4002); FStar_Syntax_Syntax.tk = uu____4003; FStar_Syntax_Syntax.pos = uu____4004; FStar_Syntax_Syntax.vars = uu____4005}) when (is_arrow t) -> begin
(

let uu____4022 = (flatten t)
in (match (uu____4022) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____4074, uu____4075) -> begin
(flatten e)
end
| uu____4094 -> begin
(

let uu____4095 = (

let uu____4096 = (

let uu____4097 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" uu____4097))
in FStar_Errors.Err (uu____4096))
in (Prims.raise uu____4095))
end)))
in (

let uu____4105 = (flatten t_head)
in (match (uu____4105) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(

let uu____4150 = (

let uu____4151 = (

let uu____4152 = (FStar_Util.string_of_int n)
in (

let uu____4156 = (FStar_Util.string_of_int (n' - n))
in (

let uu____4162 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." uu____4152 uu____4156 uu____4162))))
in FStar_Errors.Err (uu____4151))
in (Prims.raise uu____4150))
end
| uu____4166 -> begin
()
end);
(

let uu____4167 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____4167) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst uu____4194 args -> (match (uu____4194) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(

let uu____4237 = (

let uu____4238 = (FStar_Syntax_Subst.subst_comp subst comp)
in uu____4238.FStar_Syntax_Syntax.n)
in (nm_of_comp uu____4237))
end
| (binders, []) -> begin
(

let uu____4257 = (

let uu____4258 = (

let uu____4261 = (

let uu____4262 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst uu____4262))
in (FStar_Syntax_Subst.compress uu____4261))
in uu____4258.FStar_Syntax_Syntax.n)
in (match (uu____4257) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____4278 = (

let uu____4279 = (

let uu____4280 = (

let uu____4288 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (uu____4288)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4280))
in (mk uu____4279))
in N (uu____4278))
end
| uu____4292 -> begin
(failwith "wat?")
end))
end
| ([], (uu____4293)::uu____4294) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____4319))::binders, ((arg, uu____4322))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let uu____4356 = (FStar_List.splitAt n' binders)
in (match (uu____4356) with
| (binders, uu____4373) -> begin
(

let uu____4386 = (

let uu____4396 = (FStar_List.map2 (fun uu____4416 uu____4417 -> (match (((uu____4416), (uu____4417))) with
| ((bv, uu____4434), (arg, q)) -> begin
(

let uu____4441 = (

let uu____4442 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in uu____4442.FStar_Syntax_Syntax.n)
in (match (uu____4441) with
| FStar_Syntax_Syntax.Tm_type (uu____4452) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| uu____4465 -> begin
(

let uu____4466 = (check_n env arg)
in (match (uu____4466) with
| (uu____4477, s_arg, u_arg) -> begin
(

let uu____4480 = (

let uu____4484 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____4484) with
| true -> begin
(

let uu____4488 = (

let uu____4491 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((uu____4491), (q)))
in (uu____4488)::(((u_arg), (q)))::[])
end
| uu____4498 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (uu____4480)))
end))
end))
end)) binders args)
in (FStar_List.split uu____4396))
in (match (uu____4386) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (

let uu____4538 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (

let uu____4544 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (uu____4538), (uu____4544)))))
end))
end))))
end));
)))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 infer check_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches infer)
end
| (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(infer env e)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____4617 = (

let uu____4618 = (env.tc_const c)
in N (uu____4618))
in ((uu____4617), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (uu____4619) -> begin
(

let uu____4627 = (

let uu____4628 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" uu____4628))
in (failwith uu____4627))
end
| FStar_Syntax_Syntax.Tm_type (uu____4632) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____4636) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____4647) -> begin
(

let uu____4652 = (

let uu____4653 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" uu____4653))
in (failwith uu____4652))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____4657) -> begin
(

let uu____4666 = (

let uu____4667 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4667))
in (failwith uu____4666))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____4671) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____4695 = (

let uu____4696 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4696))
in (failwith uu____4695))
end)))))
and mk_match : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let uu____4734 = (check_n env e0)
in (match (uu____4734) with
| (uu____4741, s_e0, u_e0) -> begin
(

let uu____4744 = (

let uu____4762 = (FStar_List.map (fun b -> (

let uu____4795 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4795) with
| (pat, None, body) -> begin
(

let env = (

let uu___108_4827 = env
in (

let uu____4828 = (

let uu____4829 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env uu____4829))
in {env = uu____4828; subst = uu___108_4827.subst; tc_const = uu___108_4827.tc_const}))
in (

let uu____4831 = (f env body)
in (match (uu____4831) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| uu____4880 -> begin
(Prims.raise (FStar_Errors.Err ("No when clauses in the definition language")))
end))) branches)
in (FStar_List.split uu____4762))
in (match (uu____4744) with
| (nms, branches) -> begin
(

let t1 = (

let uu____4945 = (FStar_List.hd nms)
in (match (uu____4945) with
| (M (t1)) | (N (t1)) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___93_4948 -> (match (uu___93_4948) with
| M (uu____4949) -> begin
true
end
| uu____4950 -> begin
false
end)) nms)
in (

let uu____4951 = (

let uu____4974 = (FStar_List.map2 (fun nm uu____5026 -> (match (uu____5026) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let uu____5122 = (check env original_body (M (t2)))
in (match (uu____5122) with
| (uu____5145, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (uu____5174), false) -> begin
(failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 uu____4974))
in (match (uu____4951) with
| (nms, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun uu____5293 -> (match (uu____5293) with
| (pat, guard, s_body) -> begin
(

let s_body = (

let uu____5334 = (

let uu____5335 = (

let uu____5345 = (

let uu____5349 = (

let uu____5352 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5353 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5352), (uu____5353))))
in (uu____5349)::[])
in ((s_body), (uu____5345)))
in FStar_Syntax_Syntax.Tm_app (uu____5335))
in (mk uu____5334))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (

let uu____5375 = (

let uu____5379 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____5379)::[])
in (

let uu____5380 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (

let uu____5382 = (

let uu____5389 = (

let uu____5395 = (

let uu____5396 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.lcomp_of_comp uu____5396))
in FStar_Util.Inl (uu____5395))
in Some (uu____5389))
in (FStar_Syntax_Util.abs uu____5375 uu____5380 uu____5382))))
in (

let t1_star = (

let uu____5410 = (

let uu____5414 = (

let uu____5415 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____5415))
in (uu____5414)::[])
in (

let uu____5416 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5410 uu____5416)))
in (

let uu____5419 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (

let uu____5433 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (uu____5419), (uu____5433)))))))))))
end
| uu____5441 -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (

let uu____5447 = (

let uu____5450 = (

let uu____5451 = (

let uu____5464 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((uu____5464), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5451))
in (mk uu____5450))
in (

let uu____5477 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (uu____5447), (uu____5477)))))))
end)
end))))
end))
end))))
and mk_let : env_  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.term  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env binding e2 proceed ensure_m -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos))
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (

let uu____5520 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5520)::[])
in (

let uu____5521 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____5521) with
| (x_binders, e2) -> begin
(

let uu____5529 = (infer env e1)
in (match (uu____5529) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____5540 = (is_C t1)
in (match (uu____5540) with
| true -> begin
(

let uu___109_5541 = binding
in (

let uu____5542 = (

let uu____5545 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 uu____5545))
in {FStar_Syntax_Syntax.lbname = uu___109_5541.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___109_5541.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5542; FStar_Syntax_Syntax.lbeff = uu___109_5541.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___109_5541.FStar_Syntax_Syntax.lbdef}))
end
| uu____5546 -> begin
binding
end))
in (

let env = (

let uu___110_5548 = env
in (

let uu____5549 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___111_5550 = x
in {FStar_Syntax_Syntax.ppname = uu___111_5550.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_5550.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____5549; subst = uu___110_5548.subst; tc_const = uu___110_5548.tc_const}))
in (

let uu____5551 = (proceed env e2)
in (match (uu____5551) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___112_5562 = binding
in (

let uu____5563 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___112_5562.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___112_5562.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5563; FStar_Syntax_Syntax.lbeff = uu___112_5562.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___112_5562.FStar_Syntax_Syntax.lbdef}))
in (

let uu____5566 = (

let uu____5569 = (

let uu____5570 = (

let uu____5578 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let uu___113_5583 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___113_5583.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___113_5583.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___113_5583.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___113_5583.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (uu____5578)))
in FStar_Syntax_Syntax.Tm_let (uu____5570))
in (mk uu____5569))
in (

let uu____5584 = (

let uu____5587 = (

let uu____5588 = (

let uu____5596 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___114_5601 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___114_5601.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___114_5601.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___114_5601.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___114_5601.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (uu____5596)))
in FStar_Syntax_Syntax.Tm_let (uu____5588))
in (mk uu____5587))
in ((nm_rec), (uu____5566), (uu____5584)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___115_5610 = binding
in {FStar_Syntax_Syntax.lbname = uu___115_5610.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___115_5610.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___115_5610.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let uu___116_5612 = env
in (

let uu____5613 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___117_5614 = x
in {FStar_Syntax_Syntax.ppname = uu___117_5614.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_5614.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____5613; subst = uu___116_5612.subst; tc_const = uu___116_5612.tc_const}))
in (

let uu____5615 = (ensure_m env e2)
in (match (uu____5615) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (

let uu____5632 = (

let uu____5633 = (

let uu____5643 = (

let uu____5647 = (

let uu____5650 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5651 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5650), (uu____5651))))
in (uu____5647)::[])
in ((s_e2), (uu____5643)))
in FStar_Syntax_Syntax.Tm_app (uu____5633))
in (mk uu____5632))
in (

let s_e2 = (

let uu____5660 = (

let uu____5667 = (

let uu____5673 = (

let uu____5674 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.lcomp_of_comp uu____5674))
in FStar_Util.Inl (uu____5673))
in Some (uu____5667))
in (FStar_Syntax_Util.abs x_binders s_e2 uu____5660))
in (

let body = (

let uu____5688 = (

let uu____5689 = (

let uu____5699 = (

let uu____5703 = (

let uu____5706 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (uu____5706)))
in (uu____5703)::[])
in ((s_e1), (uu____5699)))
in FStar_Syntax_Syntax.Tm_app (uu____5689))
in (mk uu____5688))
in (

let uu____5714 = (

let uu____5715 = (

let uu____5719 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____5719)::[])
in (

let uu____5720 = (

let uu____5727 = (

let uu____5733 = (

let uu____5734 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.lcomp_of_comp uu____5734))
in FStar_Util.Inl (uu____5733))
in Some (uu____5727))
in (FStar_Syntax_Util.abs uu____5715 body uu____5720)))
in (

let uu____5745 = (

let uu____5748 = (

let uu____5749 = (

let uu____5757 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___118_5762 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___118_5762.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___118_5762.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___118_5762.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___118_5762.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (uu____5757)))
in FStar_Syntax_Syntax.Tm_let (uu____5749))
in (mk uu____5748))
in ((M (t2)), (uu____5714), (uu____5745)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____5771 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (uu____5771))
in (

let uu____5776 = (check env e mn)
in (match (uu____5776) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____5786 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____5799 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (uu____5799))
in (

let uu____5804 = (check env e mn)
in (match (uu____5804) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____5814 -> begin
(failwith "[check_m]: impossible")
end))))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> ((

let uu____5836 = (

let uu____5837 = (is_C c)
in (not (uu____5837)))
in (match (uu____5836) with
| true -> begin
(failwith "not a C")
end
| uu____5838 -> begin
()
end));
(

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (

let uu____5849 = (

let uu____5850 = (FStar_Syntax_Subst.compress c)
in uu____5850.FStar_Syntax_Syntax.n)
in (match (uu____5849) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____5869 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____5869) with
| (wp_head, wp_args) -> begin
((

let uu____5896 = ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (

let uu____5909 = (

let uu____5910 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head uu____5910))
in (not (uu____5909))))
in (match (uu____5896) with
| true -> begin
(failwith "mismatch")
end
| uu____5918 -> begin
()
end));
(

let uu____5919 = (

let uu____5920 = (

let uu____5930 = (FStar_List.map2 (fun uu____5940 uu____5941 -> (match (((uu____5940), (uu____5941))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> (

let uu____5964 = (FStar_Syntax_Syntax.is_implicit q)
in (match (uu____5964) with
| true -> begin
"implicit"
end
| uu____5965 -> begin
"explicit"
end)))
in ((match ((q <> q')) with
| true -> begin
(

let uu____5967 = (print_implicit q)
in (

let uu____5968 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" uu____5967 uu____5968)))
end
| uu____5969 -> begin
()
end);
(

let uu____5970 = (trans_F_ env arg wp_arg)
in ((uu____5970), (q)));
))
end)) args wp_args)
in ((head), (uu____5930)))
in FStar_Syntax_Syntax.Tm_app (uu____5920))
in (mk uu____5919));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let uu____5992 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____5992) with
| (binders_orig, comp) -> begin
(

let uu____5997 = (

let uu____6005 = (FStar_List.map (fun uu____6019 -> (match (uu____6019) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____6032 = (is_C h)
in (match (uu____6032) with
| true -> begin
(

let w' = (

let uu____6039 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None uu____6039))
in (

let uu____6040 = (

let uu____6044 = (

let uu____6048 = (

let uu____6051 = (

let uu____6052 = (

let uu____6053 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h uu____6053))
in (FStar_Syntax_Syntax.null_bv uu____6052))
in ((uu____6051), (q)))
in (uu____6048)::[])
in (((w'), (q)))::uu____6044)
in ((w'), (uu____6040))))
end
| uu____6063 -> begin
(

let x = (

let uu____6065 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None uu____6065))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig)
in (FStar_List.split uu____6005))
in (match (uu____5997) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (

let uu____6095 = (

let uu____6097 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig uu____6097))
in (FStar_Syntax_Subst.subst_comp uu____6095 comp))
in (

let app = (

let uu____6101 = (

let uu____6102 = (

let uu____6112 = (FStar_List.map (fun bv -> (

let uu____6119 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____6120 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____6119), (uu____6120))))) bvs)
in ((wp), (uu____6112)))
in FStar_Syntax_Syntax.Tm_app (uu____6102))
in (mk uu____6101))
in (

let comp = (

let uu____6125 = (type_of_comp comp)
in (

let uu____6126 = (is_monadic_comp comp)
in (trans_G env uu____6125 uu____6126 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____6128, uu____6129) -> begin
(trans_F_ env e wp)
end
| uu____6148 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in (match (is_monadic) with
| true -> begin
(

let uu____6163 = (

let uu____6164 = (star_type' env h)
in (

let uu____6167 = (

let uu____6173 = (

let uu____6176 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (uu____6176)))
in (uu____6173)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu____6164; FStar_Syntax_Syntax.effect_args = uu____6167; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____6163))
end
| uu____6181 -> begin
(

let uu____6182 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total uu____6182))
end)))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____6193 = (n env.env t)
in (star_type' env uu____6193)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (

let uu____6205 = (n env.env t)
in (check_n env uu____6205)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let uu____6215 = (n env.env c)
in (

let uu____6216 = (n env.env wp)
in (trans_F_ env uu____6215 uu____6216))))




