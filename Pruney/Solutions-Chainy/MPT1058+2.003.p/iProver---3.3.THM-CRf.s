%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:12 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 103 expanded)
%              Number of clauses        :   25 (  26 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 199 expanded)
%              Number of equality atoms :   66 ( 114 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4)
        & r1_tarski(k10_relat_1(X0,sK4),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f62,f61])).

fof(f101,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f105,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f77,f80,f80])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f97,f105])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f111,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f81,f105,f79])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f110,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f78,f79,f79])).

fof(f103,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f109,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f104,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1542,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1546,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1565,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1546,c_14])).

cnf(c_17084,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_1542,c_1565])).

cnf(c_13,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1543,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1557,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8216,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK4),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1543,c_1557])).

cnf(c_8240,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k6_subset_1(k10_relat_1(sK2,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8216,c_14])).

cnf(c_11,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_8241,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k10_relat_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_8240,c_11])).

cnf(c_9563,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_13,c_8241])).

cnf(c_17285,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_17084,c_9563])).

cnf(c_777,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1859,plain,
    ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_778,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1628,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
    | k10_relat_1(sK2,sK4) != X0
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1727,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_34,negated_conjecture,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17285,c_1859,c_1727,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.93/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/1.47  
% 6.93/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.93/1.47  
% 6.93/1.47  ------  iProver source info
% 6.93/1.47  
% 6.93/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.93/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.93/1.47  git: non_committed_changes: false
% 6.93/1.47  git: last_make_outside_of_git: false
% 6.93/1.47  
% 6.93/1.47  ------ 
% 6.93/1.47  
% 6.93/1.47  ------ Input Options
% 6.93/1.47  
% 6.93/1.47  --out_options                           all
% 6.93/1.47  --tptp_safe_out                         true
% 6.93/1.47  --problem_path                          ""
% 6.93/1.47  --include_path                          ""
% 6.93/1.47  --clausifier                            res/vclausify_rel
% 6.93/1.47  --clausifier_options                    ""
% 6.93/1.47  --stdin                                 false
% 6.93/1.47  --stats_out                             all
% 6.93/1.47  
% 6.93/1.47  ------ General Options
% 6.93/1.47  
% 6.93/1.47  --fof                                   false
% 6.93/1.47  --time_out_real                         305.
% 6.93/1.47  --time_out_virtual                      -1.
% 6.93/1.47  --symbol_type_check                     false
% 6.93/1.47  --clausify_out                          false
% 6.93/1.47  --sig_cnt_out                           false
% 6.93/1.47  --trig_cnt_out                          false
% 6.93/1.47  --trig_cnt_out_tolerance                1.
% 6.93/1.47  --trig_cnt_out_sk_spl                   false
% 6.93/1.47  --abstr_cl_out                          false
% 6.93/1.47  
% 6.93/1.47  ------ Global Options
% 6.93/1.47  
% 6.93/1.47  --schedule                              default
% 6.93/1.47  --add_important_lit                     false
% 6.93/1.47  --prop_solver_per_cl                    1000
% 6.93/1.47  --min_unsat_core                        false
% 6.93/1.47  --soft_assumptions                      false
% 6.93/1.47  --soft_lemma_size                       3
% 6.93/1.47  --prop_impl_unit_size                   0
% 6.93/1.47  --prop_impl_unit                        []
% 6.93/1.47  --share_sel_clauses                     true
% 6.93/1.47  --reset_solvers                         false
% 6.93/1.47  --bc_imp_inh                            [conj_cone]
% 6.93/1.47  --conj_cone_tolerance                   3.
% 6.93/1.47  --extra_neg_conj                        none
% 6.93/1.47  --large_theory_mode                     true
% 6.93/1.47  --prolific_symb_bound                   200
% 6.93/1.47  --lt_threshold                          2000
% 6.93/1.47  --clause_weak_htbl                      true
% 6.93/1.47  --gc_record_bc_elim                     false
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing Options
% 6.93/1.47  
% 6.93/1.47  --preprocessing_flag                    true
% 6.93/1.47  --time_out_prep_mult                    0.1
% 6.93/1.47  --splitting_mode                        input
% 6.93/1.47  --splitting_grd                         true
% 6.93/1.47  --splitting_cvd                         false
% 6.93/1.47  --splitting_cvd_svl                     false
% 6.93/1.47  --splitting_nvd                         32
% 6.93/1.47  --sub_typing                            true
% 6.93/1.47  --prep_gs_sim                           true
% 6.93/1.47  --prep_unflatten                        true
% 6.93/1.47  --prep_res_sim                          true
% 6.93/1.47  --prep_upred                            true
% 6.93/1.47  --prep_sem_filter                       exhaustive
% 6.93/1.47  --prep_sem_filter_out                   false
% 6.93/1.47  --pred_elim                             true
% 6.93/1.47  --res_sim_input                         true
% 6.93/1.47  --eq_ax_congr_red                       true
% 6.93/1.47  --pure_diseq_elim                       true
% 6.93/1.47  --brand_transform                       false
% 6.93/1.47  --non_eq_to_eq                          false
% 6.93/1.47  --prep_def_merge                        true
% 6.93/1.47  --prep_def_merge_prop_impl              false
% 6.93/1.47  --prep_def_merge_mbd                    true
% 6.93/1.47  --prep_def_merge_tr_red                 false
% 6.93/1.47  --prep_def_merge_tr_cl                  false
% 6.93/1.47  --smt_preprocessing                     true
% 6.93/1.47  --smt_ac_axioms                         fast
% 6.93/1.47  --preprocessed_out                      false
% 6.93/1.47  --preprocessed_stats                    false
% 6.93/1.47  
% 6.93/1.47  ------ Abstraction refinement Options
% 6.93/1.47  
% 6.93/1.47  --abstr_ref                             []
% 6.93/1.47  --abstr_ref_prep                        false
% 6.93/1.47  --abstr_ref_until_sat                   false
% 6.93/1.47  --abstr_ref_sig_restrict                funpre
% 6.93/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.93/1.47  --abstr_ref_under                       []
% 6.93/1.47  
% 6.93/1.47  ------ SAT Options
% 6.93/1.47  
% 6.93/1.47  --sat_mode                              false
% 6.93/1.47  --sat_fm_restart_options                ""
% 6.93/1.47  --sat_gr_def                            false
% 6.93/1.47  --sat_epr_types                         true
% 6.93/1.47  --sat_non_cyclic_types                  false
% 6.93/1.47  --sat_finite_models                     false
% 6.93/1.47  --sat_fm_lemmas                         false
% 6.93/1.47  --sat_fm_prep                           false
% 6.93/1.47  --sat_fm_uc_incr                        true
% 6.93/1.47  --sat_out_model                         small
% 6.93/1.47  --sat_out_clauses                       false
% 6.93/1.47  
% 6.93/1.47  ------ QBF Options
% 6.93/1.47  
% 6.93/1.47  --qbf_mode                              false
% 6.93/1.47  --qbf_elim_univ                         false
% 6.93/1.47  --qbf_dom_inst                          none
% 6.93/1.47  --qbf_dom_pre_inst                      false
% 6.93/1.47  --qbf_sk_in                             false
% 6.93/1.47  --qbf_pred_elim                         true
% 6.93/1.47  --qbf_split                             512
% 6.93/1.47  
% 6.93/1.47  ------ BMC1 Options
% 6.93/1.47  
% 6.93/1.47  --bmc1_incremental                      false
% 6.93/1.47  --bmc1_axioms                           reachable_all
% 6.93/1.47  --bmc1_min_bound                        0
% 6.93/1.47  --bmc1_max_bound                        -1
% 6.93/1.47  --bmc1_max_bound_default                -1
% 6.93/1.47  --bmc1_symbol_reachability              true
% 6.93/1.47  --bmc1_property_lemmas                  false
% 6.93/1.47  --bmc1_k_induction                      false
% 6.93/1.47  --bmc1_non_equiv_states                 false
% 6.93/1.47  --bmc1_deadlock                         false
% 6.93/1.47  --bmc1_ucm                              false
% 6.93/1.47  --bmc1_add_unsat_core                   none
% 6.93/1.47  --bmc1_unsat_core_children              false
% 6.93/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.93/1.47  --bmc1_out_stat                         full
% 6.93/1.47  --bmc1_ground_init                      false
% 6.93/1.47  --bmc1_pre_inst_next_state              false
% 6.93/1.47  --bmc1_pre_inst_state                   false
% 6.93/1.47  --bmc1_pre_inst_reach_state             false
% 6.93/1.47  --bmc1_out_unsat_core                   false
% 6.93/1.47  --bmc1_aig_witness_out                  false
% 6.93/1.47  --bmc1_verbose                          false
% 6.93/1.47  --bmc1_dump_clauses_tptp                false
% 6.93/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.93/1.47  --bmc1_dump_file                        -
% 6.93/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.93/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.93/1.47  --bmc1_ucm_extend_mode                  1
% 6.93/1.47  --bmc1_ucm_init_mode                    2
% 6.93/1.47  --bmc1_ucm_cone_mode                    none
% 6.93/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.93/1.47  --bmc1_ucm_relax_model                  4
% 6.93/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.93/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.93/1.47  --bmc1_ucm_layered_model                none
% 6.93/1.47  --bmc1_ucm_max_lemma_size               10
% 6.93/1.47  
% 6.93/1.47  ------ AIG Options
% 6.93/1.47  
% 6.93/1.47  --aig_mode                              false
% 6.93/1.47  
% 6.93/1.47  ------ Instantiation Options
% 6.93/1.47  
% 6.93/1.47  --instantiation_flag                    true
% 6.93/1.47  --inst_sos_flag                         true
% 6.93/1.47  --inst_sos_phase                        true
% 6.93/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.93/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.93/1.47  --inst_lit_sel_side                     num_symb
% 6.93/1.47  --inst_solver_per_active                1400
% 6.93/1.47  --inst_solver_calls_frac                1.
% 6.93/1.47  --inst_passive_queue_type               priority_queues
% 6.93/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.93/1.47  --inst_passive_queues_freq              [25;2]
% 6.93/1.47  --inst_dismatching                      true
% 6.93/1.47  --inst_eager_unprocessed_to_passive     true
% 6.93/1.47  --inst_prop_sim_given                   true
% 6.93/1.47  --inst_prop_sim_new                     false
% 6.93/1.47  --inst_subs_new                         false
% 6.93/1.47  --inst_eq_res_simp                      false
% 6.93/1.47  --inst_subs_given                       false
% 6.93/1.47  --inst_orphan_elimination               true
% 6.93/1.47  --inst_learning_loop_flag               true
% 6.93/1.47  --inst_learning_start                   3000
% 6.93/1.47  --inst_learning_factor                  2
% 6.93/1.47  --inst_start_prop_sim_after_learn       3
% 6.93/1.47  --inst_sel_renew                        solver
% 6.93/1.47  --inst_lit_activity_flag                true
% 6.93/1.47  --inst_restr_to_given                   false
% 6.93/1.47  --inst_activity_threshold               500
% 6.93/1.47  --inst_out_proof                        true
% 6.93/1.47  
% 6.93/1.47  ------ Resolution Options
% 6.93/1.47  
% 6.93/1.47  --resolution_flag                       true
% 6.93/1.47  --res_lit_sel                           adaptive
% 6.93/1.47  --res_lit_sel_side                      none
% 6.93/1.47  --res_ordering                          kbo
% 6.93/1.47  --res_to_prop_solver                    active
% 6.93/1.47  --res_prop_simpl_new                    false
% 6.93/1.47  --res_prop_simpl_given                  true
% 6.93/1.47  --res_passive_queue_type                priority_queues
% 6.93/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.93/1.47  --res_passive_queues_freq               [15;5]
% 6.93/1.47  --res_forward_subs                      full
% 6.93/1.47  --res_backward_subs                     full
% 6.93/1.47  --res_forward_subs_resolution           true
% 6.93/1.47  --res_backward_subs_resolution          true
% 6.93/1.47  --res_orphan_elimination                true
% 6.93/1.47  --res_time_limit                        2.
% 6.93/1.47  --res_out_proof                         true
% 6.93/1.47  
% 6.93/1.47  ------ Superposition Options
% 6.93/1.47  
% 6.93/1.47  --superposition_flag                    true
% 6.93/1.47  --sup_passive_queue_type                priority_queues
% 6.93/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.93/1.47  --sup_passive_queues_freq               [8;1;4]
% 6.93/1.47  --demod_completeness_check              fast
% 6.93/1.47  --demod_use_ground                      true
% 6.93/1.47  --sup_to_prop_solver                    passive
% 6.93/1.47  --sup_prop_simpl_new                    true
% 6.93/1.47  --sup_prop_simpl_given                  true
% 6.93/1.47  --sup_fun_splitting                     true
% 6.93/1.47  --sup_smt_interval                      50000
% 6.93/1.47  
% 6.93/1.47  ------ Superposition Simplification Setup
% 6.93/1.47  
% 6.93/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.93/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.93/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.93/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 6.93/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.93/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.93/1.47  --sup_immed_triv                        [TrivRules]
% 6.93/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_immed_bw_main                     []
% 6.93/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.93/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 6.93/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_input_bw                          []
% 6.93/1.47  
% 6.93/1.47  ------ Combination Options
% 6.93/1.47  
% 6.93/1.47  --comb_res_mult                         3
% 6.93/1.47  --comb_sup_mult                         2
% 6.93/1.47  --comb_inst_mult                        10
% 6.93/1.47  
% 6.93/1.47  ------ Debug Options
% 6.93/1.47  
% 6.93/1.47  --dbg_backtrace                         false
% 6.93/1.47  --dbg_dump_prop_clauses                 false
% 6.93/1.47  --dbg_dump_prop_clauses_file            -
% 6.93/1.47  --dbg_out_stat                          false
% 6.93/1.47  ------ Parsing...
% 6.93/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.93/1.47  ------ Proving...
% 6.93/1.47  ------ Problem Properties 
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  clauses                                 43
% 6.93/1.47  conjectures                             3
% 6.93/1.47  EPR                                     8
% 6.93/1.47  Horn                                    38
% 6.93/1.47  unary                                   14
% 6.93/1.47  binary                                  15
% 6.93/1.47  lits                                    88
% 6.93/1.47  lits eq                                 24
% 6.93/1.47  fd_pure                                 0
% 6.93/1.47  fd_pseudo                               0
% 6.93/1.47  fd_cond                                 1
% 6.93/1.47  fd_pseudo_cond                          7
% 6.93/1.47  AC symbols                              0
% 6.93/1.47  
% 6.93/1.47  ------ Schedule dynamic 5 is on 
% 6.93/1.47  
% 6.93/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  ------ 
% 6.93/1.47  Current options:
% 6.93/1.47  ------ 
% 6.93/1.47  
% 6.93/1.47  ------ Input Options
% 6.93/1.47  
% 6.93/1.47  --out_options                           all
% 6.93/1.47  --tptp_safe_out                         true
% 6.93/1.47  --problem_path                          ""
% 6.93/1.47  --include_path                          ""
% 6.93/1.47  --clausifier                            res/vclausify_rel
% 6.93/1.47  --clausifier_options                    ""
% 6.93/1.47  --stdin                                 false
% 6.93/1.47  --stats_out                             all
% 6.93/1.47  
% 6.93/1.47  ------ General Options
% 6.93/1.47  
% 6.93/1.47  --fof                                   false
% 6.93/1.47  --time_out_real                         305.
% 6.93/1.47  --time_out_virtual                      -1.
% 6.93/1.47  --symbol_type_check                     false
% 6.93/1.47  --clausify_out                          false
% 6.93/1.47  --sig_cnt_out                           false
% 6.93/1.47  --trig_cnt_out                          false
% 6.93/1.47  --trig_cnt_out_tolerance                1.
% 6.93/1.47  --trig_cnt_out_sk_spl                   false
% 6.93/1.47  --abstr_cl_out                          false
% 6.93/1.47  
% 6.93/1.47  ------ Global Options
% 6.93/1.47  
% 6.93/1.47  --schedule                              default
% 6.93/1.47  --add_important_lit                     false
% 6.93/1.47  --prop_solver_per_cl                    1000
% 6.93/1.47  --min_unsat_core                        false
% 6.93/1.47  --soft_assumptions                      false
% 6.93/1.47  --soft_lemma_size                       3
% 6.93/1.47  --prop_impl_unit_size                   0
% 6.93/1.47  --prop_impl_unit                        []
% 6.93/1.47  --share_sel_clauses                     true
% 6.93/1.47  --reset_solvers                         false
% 6.93/1.47  --bc_imp_inh                            [conj_cone]
% 6.93/1.47  --conj_cone_tolerance                   3.
% 6.93/1.47  --extra_neg_conj                        none
% 6.93/1.47  --large_theory_mode                     true
% 6.93/1.47  --prolific_symb_bound                   200
% 6.93/1.47  --lt_threshold                          2000
% 6.93/1.47  --clause_weak_htbl                      true
% 6.93/1.47  --gc_record_bc_elim                     false
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing Options
% 6.93/1.47  
% 6.93/1.47  --preprocessing_flag                    true
% 6.93/1.47  --time_out_prep_mult                    0.1
% 6.93/1.47  --splitting_mode                        input
% 6.93/1.47  --splitting_grd                         true
% 6.93/1.47  --splitting_cvd                         false
% 6.93/1.47  --splitting_cvd_svl                     false
% 6.93/1.47  --splitting_nvd                         32
% 6.93/1.47  --sub_typing                            true
% 6.93/1.47  --prep_gs_sim                           true
% 6.93/1.47  --prep_unflatten                        true
% 6.93/1.47  --prep_res_sim                          true
% 6.93/1.47  --prep_upred                            true
% 6.93/1.47  --prep_sem_filter                       exhaustive
% 6.93/1.47  --prep_sem_filter_out                   false
% 6.93/1.47  --pred_elim                             true
% 6.93/1.47  --res_sim_input                         true
% 6.93/1.47  --eq_ax_congr_red                       true
% 6.93/1.47  --pure_diseq_elim                       true
% 6.93/1.47  --brand_transform                       false
% 6.93/1.47  --non_eq_to_eq                          false
% 6.93/1.47  --prep_def_merge                        true
% 6.93/1.47  --prep_def_merge_prop_impl              false
% 6.93/1.47  --prep_def_merge_mbd                    true
% 6.93/1.47  --prep_def_merge_tr_red                 false
% 6.93/1.47  --prep_def_merge_tr_cl                  false
% 6.93/1.47  --smt_preprocessing                     true
% 6.93/1.47  --smt_ac_axioms                         fast
% 6.93/1.47  --preprocessed_out                      false
% 6.93/1.47  --preprocessed_stats                    false
% 6.93/1.47  
% 6.93/1.47  ------ Abstraction refinement Options
% 6.93/1.47  
% 6.93/1.47  --abstr_ref                             []
% 6.93/1.47  --abstr_ref_prep                        false
% 6.93/1.47  --abstr_ref_until_sat                   false
% 6.93/1.47  --abstr_ref_sig_restrict                funpre
% 6.93/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.93/1.47  --abstr_ref_under                       []
% 6.93/1.47  
% 6.93/1.47  ------ SAT Options
% 6.93/1.47  
% 6.93/1.47  --sat_mode                              false
% 6.93/1.47  --sat_fm_restart_options                ""
% 6.93/1.47  --sat_gr_def                            false
% 6.93/1.47  --sat_epr_types                         true
% 6.93/1.47  --sat_non_cyclic_types                  false
% 6.93/1.47  --sat_finite_models                     false
% 6.93/1.47  --sat_fm_lemmas                         false
% 6.93/1.47  --sat_fm_prep                           false
% 6.93/1.47  --sat_fm_uc_incr                        true
% 6.93/1.47  --sat_out_model                         small
% 6.93/1.47  --sat_out_clauses                       false
% 6.93/1.47  
% 6.93/1.47  ------ QBF Options
% 6.93/1.47  
% 6.93/1.47  --qbf_mode                              false
% 6.93/1.47  --qbf_elim_univ                         false
% 6.93/1.47  --qbf_dom_inst                          none
% 6.93/1.47  --qbf_dom_pre_inst                      false
% 6.93/1.47  --qbf_sk_in                             false
% 6.93/1.47  --qbf_pred_elim                         true
% 6.93/1.47  --qbf_split                             512
% 6.93/1.47  
% 6.93/1.47  ------ BMC1 Options
% 6.93/1.47  
% 6.93/1.47  --bmc1_incremental                      false
% 6.93/1.47  --bmc1_axioms                           reachable_all
% 6.93/1.47  --bmc1_min_bound                        0
% 6.93/1.47  --bmc1_max_bound                        -1
% 6.93/1.47  --bmc1_max_bound_default                -1
% 6.93/1.47  --bmc1_symbol_reachability              true
% 6.93/1.47  --bmc1_property_lemmas                  false
% 6.93/1.47  --bmc1_k_induction                      false
% 6.93/1.47  --bmc1_non_equiv_states                 false
% 6.93/1.47  --bmc1_deadlock                         false
% 6.93/1.47  --bmc1_ucm                              false
% 6.93/1.47  --bmc1_add_unsat_core                   none
% 6.93/1.47  --bmc1_unsat_core_children              false
% 6.93/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.93/1.47  --bmc1_out_stat                         full
% 6.93/1.47  --bmc1_ground_init                      false
% 6.93/1.47  --bmc1_pre_inst_next_state              false
% 6.93/1.47  --bmc1_pre_inst_state                   false
% 6.93/1.47  --bmc1_pre_inst_reach_state             false
% 6.93/1.47  --bmc1_out_unsat_core                   false
% 6.93/1.47  --bmc1_aig_witness_out                  false
% 6.93/1.47  --bmc1_verbose                          false
% 6.93/1.47  --bmc1_dump_clauses_tptp                false
% 6.93/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.93/1.47  --bmc1_dump_file                        -
% 6.93/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.93/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.93/1.47  --bmc1_ucm_extend_mode                  1
% 6.93/1.47  --bmc1_ucm_init_mode                    2
% 6.93/1.47  --bmc1_ucm_cone_mode                    none
% 6.93/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.93/1.47  --bmc1_ucm_relax_model                  4
% 6.93/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.93/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.93/1.47  --bmc1_ucm_layered_model                none
% 6.93/1.47  --bmc1_ucm_max_lemma_size               10
% 6.93/1.47  
% 6.93/1.47  ------ AIG Options
% 6.93/1.47  
% 6.93/1.47  --aig_mode                              false
% 6.93/1.47  
% 6.93/1.47  ------ Instantiation Options
% 6.93/1.47  
% 6.93/1.47  --instantiation_flag                    true
% 6.93/1.47  --inst_sos_flag                         true
% 6.93/1.47  --inst_sos_phase                        true
% 6.93/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.93/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.93/1.47  --inst_lit_sel_side                     none
% 6.93/1.47  --inst_solver_per_active                1400
% 6.93/1.47  --inst_solver_calls_frac                1.
% 6.93/1.47  --inst_passive_queue_type               priority_queues
% 6.93/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.93/1.47  --inst_passive_queues_freq              [25;2]
% 6.93/1.47  --inst_dismatching                      true
% 6.93/1.47  --inst_eager_unprocessed_to_passive     true
% 6.93/1.47  --inst_prop_sim_given                   true
% 6.93/1.47  --inst_prop_sim_new                     false
% 6.93/1.47  --inst_subs_new                         false
% 6.93/1.47  --inst_eq_res_simp                      false
% 6.93/1.47  --inst_subs_given                       false
% 6.93/1.47  --inst_orphan_elimination               true
% 6.93/1.47  --inst_learning_loop_flag               true
% 6.93/1.47  --inst_learning_start                   3000
% 6.93/1.47  --inst_learning_factor                  2
% 6.93/1.47  --inst_start_prop_sim_after_learn       3
% 6.93/1.47  --inst_sel_renew                        solver
% 6.93/1.47  --inst_lit_activity_flag                true
% 6.93/1.47  --inst_restr_to_given                   false
% 6.93/1.47  --inst_activity_threshold               500
% 6.93/1.47  --inst_out_proof                        true
% 6.93/1.47  
% 6.93/1.47  ------ Resolution Options
% 6.93/1.47  
% 6.93/1.47  --resolution_flag                       false
% 6.93/1.47  --res_lit_sel                           adaptive
% 6.93/1.47  --res_lit_sel_side                      none
% 6.93/1.47  --res_ordering                          kbo
% 6.93/1.47  --res_to_prop_solver                    active
% 6.93/1.47  --res_prop_simpl_new                    false
% 6.93/1.47  --res_prop_simpl_given                  true
% 6.93/1.47  --res_passive_queue_type                priority_queues
% 6.93/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.93/1.47  --res_passive_queues_freq               [15;5]
% 6.93/1.47  --res_forward_subs                      full
% 6.93/1.47  --res_backward_subs                     full
% 6.93/1.47  --res_forward_subs_resolution           true
% 6.93/1.47  --res_backward_subs_resolution          true
% 6.93/1.47  --res_orphan_elimination                true
% 6.93/1.47  --res_time_limit                        2.
% 6.93/1.47  --res_out_proof                         true
% 6.93/1.47  
% 6.93/1.47  ------ Superposition Options
% 6.93/1.47  
% 6.93/1.47  --superposition_flag                    true
% 6.93/1.47  --sup_passive_queue_type                priority_queues
% 6.93/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.93/1.47  --sup_passive_queues_freq               [8;1;4]
% 6.93/1.47  --demod_completeness_check              fast
% 6.93/1.47  --demod_use_ground                      true
% 6.93/1.47  --sup_to_prop_solver                    passive
% 6.93/1.47  --sup_prop_simpl_new                    true
% 6.93/1.47  --sup_prop_simpl_given                  true
% 6.93/1.47  --sup_fun_splitting                     true
% 6.93/1.47  --sup_smt_interval                      50000
% 6.93/1.47  
% 6.93/1.47  ------ Superposition Simplification Setup
% 6.93/1.47  
% 6.93/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.93/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.93/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.93/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 6.93/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.93/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.93/1.47  --sup_immed_triv                        [TrivRules]
% 6.93/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_immed_bw_main                     []
% 6.93/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.93/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 6.93/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.47  --sup_input_bw                          []
% 6.93/1.47  
% 6.93/1.47  ------ Combination Options
% 6.93/1.47  
% 6.93/1.47  --comb_res_mult                         3
% 6.93/1.47  --comb_sup_mult                         2
% 6.93/1.47  --comb_inst_mult                        10
% 6.93/1.47  
% 6.93/1.47  ------ Debug Options
% 6.93/1.47  
% 6.93/1.47  --dbg_backtrace                         false
% 6.93/1.47  --dbg_dump_prop_clauses                 false
% 6.93/1.47  --dbg_dump_prop_clauses_file            -
% 6.93/1.47  --dbg_out_stat                          false
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  ------ Proving...
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  % SZS status Theorem for theBenchmark.p
% 6.93/1.47  
% 6.93/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 6.93/1.47  
% 6.93/1.47  fof(f26,conjecture,(
% 6.93/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f27,negated_conjecture,(
% 6.93/1.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 6.93/1.47    inference(negated_conjecture,[],[f26])).
% 6.93/1.47  
% 6.93/1.47  fof(f47,plain,(
% 6.93/1.47    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.93/1.47    inference(ennf_transformation,[],[f27])).
% 6.93/1.47  
% 6.93/1.47  fof(f48,plain,(
% 6.93/1.47    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.93/1.47    inference(flattening,[],[f47])).
% 6.93/1.47  
% 6.93/1.47  fof(f62,plain,(
% 6.93/1.47    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4) & r1_tarski(k10_relat_1(X0,sK4),sK3))) )),
% 6.93/1.47    introduced(choice_axiom,[])).
% 6.93/1.47  
% 6.93/1.47  fof(f61,plain,(
% 6.93/1.47    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 6.93/1.47    introduced(choice_axiom,[])).
% 6.93/1.47  
% 6.93/1.47  fof(f63,plain,(
% 6.93/1.47    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 6.93/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f62,f61])).
% 6.93/1.47  
% 6.93/1.47  fof(f101,plain,(
% 6.93/1.47    v1_relat_1(sK2)),
% 6.93/1.47    inference(cnf_transformation,[],[f63])).
% 6.93/1.47  
% 6.93/1.47  fof(f22,axiom,(
% 6.93/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f41,plain,(
% 6.93/1.47    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 6.93/1.47    inference(ennf_transformation,[],[f22])).
% 6.93/1.47  
% 6.93/1.47  fof(f97,plain,(
% 6.93/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f41])).
% 6.93/1.47  
% 6.93/1.47  fof(f9,axiom,(
% 6.93/1.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f77,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f9])).
% 6.93/1.47  
% 6.93/1.47  fof(f12,axiom,(
% 6.93/1.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f80,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f12])).
% 6.93/1.47  
% 6.93/1.47  fof(f105,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.93/1.47    inference(definition_unfolding,[],[f77,f80,f80])).
% 6.93/1.47  
% 6.93/1.47  fof(f112,plain,(
% 6.93/1.47    ( ! [X2,X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.93/1.47    inference(definition_unfolding,[],[f97,f105])).
% 6.93/1.47  
% 6.93/1.47  fof(f13,axiom,(
% 6.93/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f81,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.93/1.47    inference(cnf_transformation,[],[f13])).
% 6.93/1.47  
% 6.93/1.47  fof(f11,axiom,(
% 6.93/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f79,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f11])).
% 6.93/1.47  
% 6.93/1.47  fof(f111,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 6.93/1.47    inference(definition_unfolding,[],[f81,f105,f79])).
% 6.93/1.47  
% 6.93/1.47  fof(f10,axiom,(
% 6.93/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f78,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f10])).
% 6.93/1.47  
% 6.93/1.47  fof(f110,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 6.93/1.47    inference(definition_unfolding,[],[f78,f79,f79])).
% 6.93/1.47  
% 6.93/1.47  fof(f103,plain,(
% 6.93/1.47    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 6.93/1.47    inference(cnf_transformation,[],[f63])).
% 6.93/1.47  
% 6.93/1.47  fof(f3,axiom,(
% 6.93/1.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f55,plain,(
% 6.93/1.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.93/1.47    inference(nnf_transformation,[],[f3])).
% 6.93/1.47  
% 6.93/1.47  fof(f71,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.93/1.47    inference(cnf_transformation,[],[f55])).
% 6.93/1.47  
% 6.93/1.47  fof(f106,plain,(
% 6.93/1.47    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 6.93/1.47    inference(definition_unfolding,[],[f71,f80])).
% 6.93/1.47  
% 6.93/1.47  fof(f7,axiom,(
% 6.93/1.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.93/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.93/1.47  
% 6.93/1.47  fof(f75,plain,(
% 6.93/1.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.93/1.47    inference(cnf_transformation,[],[f7])).
% 6.93/1.47  
% 6.93/1.47  fof(f109,plain,(
% 6.93/1.47    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 6.93/1.47    inference(definition_unfolding,[],[f75,f80])).
% 6.93/1.47  
% 6.93/1.47  fof(f104,plain,(
% 6.93/1.47    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 6.93/1.47    inference(cnf_transformation,[],[f63])).
% 6.93/1.47  
% 6.93/1.47  cnf(c_37,negated_conjecture,
% 6.93/1.47      ( v1_relat_1(sK2) ),
% 6.93/1.47      inference(cnf_transformation,[],[f101]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1542,plain,
% 6.93/1.47      ( v1_relat_1(sK2) = iProver_top ),
% 6.93/1.47      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_30,plain,
% 6.93/1.47      ( ~ v1_relat_1(X0)
% 6.93/1.47      | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 6.93/1.47      inference(cnf_transformation,[],[f112]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1546,plain,
% 6.93/1.47      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 6.93/1.47      | v1_relat_1(X1) != iProver_top ),
% 6.93/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_14,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 6.93/1.47      inference(cnf_transformation,[],[f111]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1565,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 6.93/1.47      | v1_relat_1(X1) != iProver_top ),
% 6.93/1.47      inference(demodulation,[status(thm)],[c_1546,c_14]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_17084,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 6.93/1.47      inference(superposition,[status(thm)],[c_1542,c_1565]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_13,plain,
% 6.93/1.47      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 6.93/1.47      inference(cnf_transformation,[],[f110]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_35,negated_conjecture,
% 6.93/1.47      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 6.93/1.47      inference(cnf_transformation,[],[f103]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1543,plain,
% 6.93/1.47      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
% 6.93/1.47      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_6,plain,
% 6.93/1.47      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 6.93/1.47      inference(cnf_transformation,[],[f106]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1557,plain,
% 6.93/1.47      ( k6_subset_1(X0,X1) = k1_xboole_0
% 6.93/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 6.93/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_8216,plain,
% 6.93/1.47      ( k6_subset_1(k10_relat_1(sK2,sK4),sK3) = k1_xboole_0 ),
% 6.93/1.47      inference(superposition,[status(thm)],[c_1543,c_1557]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_8240,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k6_subset_1(k10_relat_1(sK2,sK4),k1_xboole_0) ),
% 6.93/1.47      inference(superposition,[status(thm)],[c_8216,c_14]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_11,plain,
% 6.93/1.47      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 6.93/1.47      inference(cnf_transformation,[],[f109]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_8241,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k10_relat_1(sK2,sK4) ),
% 6.93/1.47      inference(demodulation,[status(thm)],[c_8240,c_11]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_9563,plain,
% 6.93/1.47      ( k1_setfam_1(k1_enumset1(sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
% 6.93/1.47      inference(superposition,[status(thm)],[c_13,c_8241]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_17285,plain,
% 6.93/1.47      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
% 6.93/1.47      inference(superposition,[status(thm)],[c_17084,c_9563]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_777,plain,( X0 = X0 ),theory(equality) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1859,plain,
% 6.93/1.47      ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
% 6.93/1.47      inference(instantiation,[status(thm)],[c_777]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_778,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1628,plain,
% 6.93/1.47      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
% 6.93/1.47      | k10_relat_1(sK2,sK4) != X0
% 6.93/1.47      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 6.93/1.47      inference(instantiation,[status(thm)],[c_778]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_1727,plain,
% 6.93/1.47      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
% 6.93/1.47      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 6.93/1.47      | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
% 6.93/1.47      inference(instantiation,[status(thm)],[c_1628]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(c_34,negated_conjecture,
% 6.93/1.47      ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 6.93/1.47      inference(cnf_transformation,[],[f104]) ).
% 6.93/1.47  
% 6.93/1.47  cnf(contradiction,plain,
% 6.93/1.47      ( $false ),
% 6.93/1.47      inference(minisat,[status(thm)],[c_17285,c_1859,c_1727,c_34]) ).
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 6.93/1.47  
% 6.93/1.47  ------                               Statistics
% 6.93/1.47  
% 6.93/1.47  ------ General
% 6.93/1.47  
% 6.93/1.47  abstr_ref_over_cycles:                  0
% 6.93/1.47  abstr_ref_under_cycles:                 0
% 6.93/1.47  gc_basic_clause_elim:                   0
% 6.93/1.47  forced_gc_time:                         0
% 6.93/1.47  parsing_time:                           0.011
% 6.93/1.47  unif_index_cands_time:                  0.
% 6.93/1.47  unif_index_add_time:                    0.
% 6.93/1.47  orderings_time:                         0.
% 6.93/1.47  out_proof_time:                         0.008
% 6.93/1.47  total_time:                             0.601
% 6.93/1.47  num_of_symbols:                         52
% 6.93/1.47  num_of_terms:                           31033
% 6.93/1.47  
% 6.93/1.47  ------ Preprocessing
% 6.93/1.47  
% 6.93/1.47  num_of_splits:                          0
% 6.93/1.47  num_of_split_atoms:                     0
% 6.93/1.47  num_of_reused_defs:                     0
% 6.93/1.47  num_eq_ax_congr_red:                    21
% 6.93/1.47  num_of_sem_filtered_clauses:            1
% 6.93/1.47  num_of_subtypes:                        0
% 6.93/1.47  monotx_restored_types:                  0
% 6.93/1.47  sat_num_of_epr_types:                   0
% 6.93/1.47  sat_num_of_non_cyclic_types:            0
% 6.93/1.47  sat_guarded_non_collapsed_types:        0
% 6.93/1.47  num_pure_diseq_elim:                    0
% 6.93/1.47  simp_replaced_by:                       0
% 6.93/1.47  res_preprocessed:                       154
% 6.93/1.47  prep_upred:                             0
% 6.93/1.47  prep_unflattend:                        16
% 6.93/1.47  smt_new_axioms:                         0
% 6.93/1.47  pred_elim_cands:                        4
% 6.93/1.47  pred_elim:                              1
% 6.93/1.47  pred_elim_cl:                           -6
% 6.93/1.47  pred_elim_cycles:                       2
% 6.93/1.47  merged_defs:                            6
% 6.93/1.47  merged_defs_ncl:                        0
% 6.93/1.47  bin_hyper_res:                          6
% 6.93/1.47  prep_cycles:                            3
% 6.93/1.47  pred_elim_time:                         0.006
% 6.93/1.47  splitting_time:                         0.
% 6.93/1.47  sem_filter_time:                        0.
% 6.93/1.47  monotx_time:                            0.
% 6.93/1.47  subtype_inf_time:                       0.
% 6.93/1.47  
% 6.93/1.47  ------ Problem properties
% 6.93/1.47  
% 6.93/1.47  clauses:                                43
% 6.93/1.47  conjectures:                            3
% 6.93/1.47  epr:                                    8
% 6.93/1.47  horn:                                   38
% 6.93/1.47  ground:                                 3
% 6.93/1.47  unary:                                  14
% 6.93/1.47  binary:                                 15
% 6.93/1.47  lits:                                   88
% 6.93/1.47  lits_eq:                                24
% 6.93/1.47  fd_pure:                                0
% 6.93/1.47  fd_pseudo:                              0
% 6.93/1.47  fd_cond:                                1
% 6.93/1.47  fd_pseudo_cond:                         7
% 6.93/1.47  ac_symbols:                             0
% 6.93/1.47  
% 6.93/1.47  ------ Propositional Solver
% 6.93/1.47  
% 6.93/1.47  prop_solver_calls:                      25
% 6.93/1.47  prop_fast_solver_calls:                 988
% 6.93/1.47  smt_solver_calls:                       0
% 6.93/1.47  smt_fast_solver_calls:                  0
% 6.93/1.47  prop_num_of_clauses:                    7480
% 6.93/1.47  prop_preprocess_simplified:             11344
% 6.93/1.47  prop_fo_subsumed:                       14
% 6.93/1.47  prop_solver_time:                       0.
% 6.93/1.47  smt_solver_time:                        0.
% 6.93/1.47  smt_fast_solver_time:                   0.
% 6.93/1.47  prop_fast_solver_time:                  0.
% 6.93/1.47  prop_unsat_core_time:                   0.
% 6.93/1.47  
% 6.93/1.47  ------ QBF
% 6.93/1.47  
% 6.93/1.47  qbf_q_res:                              0
% 6.93/1.47  qbf_num_tautologies:                    0
% 6.93/1.47  qbf_prep_cycles:                        0
% 6.93/1.47  
% 6.93/1.47  ------ BMC1
% 6.93/1.47  
% 6.93/1.47  bmc1_current_bound:                     -1
% 6.93/1.47  bmc1_last_solved_bound:                 -1
% 6.93/1.47  bmc1_unsat_core_size:                   -1
% 6.93/1.47  bmc1_unsat_core_parents_size:           -1
% 6.93/1.47  bmc1_merge_next_fun:                    0
% 6.93/1.47  bmc1_unsat_core_clauses_time:           0.
% 6.93/1.47  
% 6.93/1.47  ------ Instantiation
% 6.93/1.47  
% 6.93/1.47  inst_num_of_clauses:                    1131
% 6.93/1.47  inst_num_in_passive:                    540
% 6.93/1.47  inst_num_in_active:                     401
% 6.93/1.47  inst_num_in_unprocessed:                192
% 6.93/1.47  inst_num_of_loops:                      630
% 6.93/1.47  inst_num_of_learning_restarts:          0
% 6.93/1.47  inst_num_moves_active_passive:          228
% 6.93/1.47  inst_lit_activity:                      0
% 6.93/1.47  inst_lit_activity_moves:                0
% 6.93/1.47  inst_num_tautologies:                   0
% 6.93/1.47  inst_num_prop_implied:                  0
% 6.93/1.47  inst_num_existing_simplified:           0
% 6.93/1.47  inst_num_eq_res_simplified:             0
% 6.93/1.47  inst_num_child_elim:                    0
% 6.93/1.47  inst_num_of_dismatching_blockings:      469
% 6.93/1.47  inst_num_of_non_proper_insts:           1149
% 6.93/1.47  inst_num_of_duplicates:                 0
% 6.93/1.47  inst_inst_num_from_inst_to_res:         0
% 6.93/1.47  inst_dismatching_checking_time:         0.
% 6.93/1.47  
% 6.93/1.47  ------ Resolution
% 6.93/1.47  
% 6.93/1.47  res_num_of_clauses:                     0
% 6.93/1.47  res_num_in_passive:                     0
% 6.93/1.47  res_num_in_active:                      0
% 6.93/1.47  res_num_of_loops:                       157
% 6.93/1.47  res_forward_subset_subsumed:            93
% 6.93/1.47  res_backward_subset_subsumed:           8
% 6.93/1.47  res_forward_subsumed:                   0
% 6.93/1.47  res_backward_subsumed:                  0
% 6.93/1.47  res_forward_subsumption_resolution:     4
% 6.93/1.47  res_backward_subsumption_resolution:    0
% 6.93/1.47  res_clause_to_clause_subsumption:       6113
% 6.93/1.47  res_orphan_elimination:                 0
% 6.93/1.47  res_tautology_del:                      84
% 6.93/1.47  res_num_eq_res_simplified:              0
% 6.93/1.47  res_num_sel_changes:                    0
% 6.93/1.47  res_moves_from_active_to_pass:          0
% 6.93/1.47  
% 6.93/1.47  ------ Superposition
% 6.93/1.47  
% 6.93/1.47  sup_time_total:                         0.
% 6.93/1.47  sup_time_generating:                    0.
% 6.93/1.47  sup_time_sim_full:                      0.
% 6.93/1.47  sup_time_sim_immed:                     0.
% 6.93/1.47  
% 6.93/1.47  sup_num_of_clauses:                     1426
% 6.93/1.47  sup_num_in_active:                      111
% 6.93/1.47  sup_num_in_passive:                     1315
% 6.93/1.47  sup_num_of_loops:                       124
% 6.93/1.47  sup_fw_superposition:                   2121
% 6.93/1.47  sup_bw_superposition:                   2046
% 6.93/1.47  sup_immediate_simplified:               1676
% 6.93/1.47  sup_given_eliminated:                   3
% 6.93/1.47  comparisons_done:                       0
% 6.93/1.47  comparisons_avoided:                    0
% 6.93/1.47  
% 6.93/1.47  ------ Simplifications
% 6.93/1.47  
% 6.93/1.47  
% 6.93/1.47  sim_fw_subset_subsumed:                 6
% 6.93/1.47  sim_bw_subset_subsumed:                 0
% 6.93/1.47  sim_fw_subsumed:                        316
% 6.93/1.47  sim_bw_subsumed:                        30
% 6.93/1.47  sim_fw_subsumption_res:                 0
% 6.93/1.47  sim_bw_subsumption_res:                 0
% 6.93/1.47  sim_tautology_del:                      3
% 6.93/1.47  sim_eq_tautology_del:                   294
% 6.93/1.47  sim_eq_res_simp:                        32
% 6.93/1.47  sim_fw_demodulated:                     1184
% 6.93/1.47  sim_bw_demodulated:                     90
% 6.93/1.47  sim_light_normalised:                   600
% 6.93/1.47  sim_joinable_taut:                      0
% 6.93/1.47  sim_joinable_simp:                      0
% 6.93/1.47  sim_ac_normalised:                      0
% 6.93/1.47  sim_smt_subsumption:                    0
% 6.93/1.47  
%------------------------------------------------------------------------------
