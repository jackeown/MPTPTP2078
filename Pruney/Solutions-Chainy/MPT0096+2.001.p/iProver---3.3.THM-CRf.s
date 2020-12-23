%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:50 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 374 expanded)
%              Number of clauses        :   39 ( 168 expanded)
%              Number of leaves         :   12 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :   79 ( 475 expanded)
%              Number of equality atoms :   60 ( 363 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f29,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_178,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_180,plain,
    ( o_0_0_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_833,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_178,c_180])).

cnf(c_4,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_983,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(o_0_0_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_833,c_4])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_299,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_979,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_833,c_299])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_401,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_407,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_401,c_3])).

cnf(c_1015,plain,
    ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_979,c_407])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_603,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_407])).

cnf(c_1076,plain,
    ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1015,c_603])).

cnf(c_2345,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_983,c_1076])).

cnf(c_482,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_1673,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_833,c_482])).

cnf(c_1727,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1673,c_833,c_1076])).

cnf(c_5,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1887,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1727,c_5])).

cnf(c_1899,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1887,c_979])).

cnf(c_4901,plain,
    ( k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_482,c_1899])).

cnf(c_4919,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1899,c_603])).

cnf(c_4969,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4901,c_4919])).

cnf(c_4971,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4969,c_1,c_482])).

cnf(c_5273,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4971,c_178])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5277,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5273,c_2])).

cnf(c_402,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_299,c_8])).

cnf(c_404,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_402,c_299])).

cnf(c_5278,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5277,c_404])).

cnf(c_5346,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_5278])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_177,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15375,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5346,c_177])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     num_symb
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       true
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 11
% 3.65/0.99  conjectures                             1
% 3.65/0.99  EPR                                     2
% 3.65/0.99  Horn                                    11
% 3.65/0.99  unary                                   10
% 3.65/0.99  binary                                  1
% 3.65/0.99  lits                                    12
% 3.65/0.99  lits eq                                 8
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 1
% 3.65/0.99  fd_pseudo_cond                          0
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Schedule dynamic 5 is on 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     none
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       false
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99   Resolution empty clause
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f10,axiom,(
% 3.65/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f28,plain,(
% 3.65/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f10])).
% 3.65/0.99  
% 3.65/0.99  fof(f8,axiom,(
% 3.65/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f14,plain,(
% 3.65/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f8])).
% 3.65/0.99  
% 3.65/0.99  fof(f26,plain,(
% 3.65/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.65/0.99    inference(cnf_transformation,[],[f14])).
% 3.65/0.99  
% 3.65/0.99  fof(f2,axiom,(
% 3.65/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f19,plain,(
% 3.65/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.65/0.99    inference(cnf_transformation,[],[f2])).
% 3.65/0.99  
% 3.65/0.99  fof(f30,plain,(
% 3.65/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | o_0_0_xboole_0 = X0) )),
% 3.65/0.99    inference(definition_unfolding,[],[f26,f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f6,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f23,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f6])).
% 3.65/0.99  
% 3.65/0.99  fof(f3,axiom,(
% 3.65/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f13,plain,(
% 3.65/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.65/0.99    inference(rectify,[],[f3])).
% 3.65/0.99  
% 3.65/0.99  fof(f20,plain,(
% 3.65/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.65/0.99    inference(cnf_transformation,[],[f13])).
% 3.65/0.99  
% 3.65/0.99  fof(f5,axiom,(
% 3.65/0.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f22,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.65/0.99    inference(cnf_transformation,[],[f5])).
% 3.65/0.99  
% 3.65/0.99  fof(f9,axiom,(
% 3.65/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f27,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f9])).
% 3.65/0.99  
% 3.65/0.99  fof(f1,axiom,(
% 3.65/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f18,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f1])).
% 3.65/0.99  
% 3.65/0.99  fof(f7,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f24,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f7])).
% 3.65/0.99  
% 3.65/0.99  fof(f4,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f21,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f4])).
% 3.65/0.99  
% 3.65/0.99  fof(f11,conjecture,(
% 3.65/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f12,negated_conjecture,(
% 3.65/0.99    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 3.65/0.99    inference(negated_conjecture,[],[f11])).
% 3.65/0.99  
% 3.65/0.99  fof(f15,plain,(
% 3.65/0.99    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 3.65/0.99    inference(ennf_transformation,[],[f12])).
% 3.65/0.99  
% 3.65/0.99  fof(f16,plain,(
% 3.65/0.99    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f17,plain,(
% 3.65/0.99    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f29,plain,(
% 3.65/0.99    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 3.65/0.99    inference(cnf_transformation,[],[f17])).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9,plain,
% 3.65/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_178,plain,
% 3.65/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6,plain,
% 3.65/0.99      ( ~ r1_xboole_0(X0,X0) | o_0_0_xboole_0 = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_180,plain,
% 3.65/0.99      ( o_0_0_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_833,plain,
% 3.65/0.99      ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_178,c_180]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4,plain,
% 3.65/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_983,plain,
% 3.65/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(o_0_0_xboole_0,k3_xboole_0(X0,X1)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_833,c_4]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1,plain,
% 3.65/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3,plain,
% 3.65/0.99      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_299,plain,
% 3.65/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_979,plain,
% 3.65/0.99      ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_833,c_299]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_8,plain,
% 3.65/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_401,plain,
% 3.65/0.99      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_407,plain,
% 3.65/0.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_401,c_3]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1015,plain,
% 3.65/0.99      ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_979,c_407]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_0,plain,
% 3.65/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f18]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_603,plain,
% 3.65/0.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_0,c_407]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1076,plain,
% 3.65/0.99      ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1015,c_603]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2345,plain,
% 3.65/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_983,c_1076]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_482,plain,
% 3.65/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1673,plain,
% 3.65/0.99      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,o_0_0_xboole_0) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_833,c_482]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1727,plain,
% 3.65/0.99      ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_1673,c_833,c_1076]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5,plain,
% 3.65/0.99      ( k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1887,plain,
% 3.65/0.99      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,o_0_0_xboole_0)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1727,c_5]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1899,plain,
% 3.65/0.99      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_1887,c_979]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4901,plain,
% 3.65/0.99      ( k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_482,c_1899]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4919,plain,
% 3.65/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1899,c_603]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4969,plain,
% 3.65/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X0) ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_4901,c_4919]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4971,plain,
% 3.65/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_4969,c_1,c_482]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5273,plain,
% 3.65/0.99      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),X1) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4971,c_178]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2,plain,
% 3.65/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5277,plain,
% 3.65/0.99      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = iProver_top ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_5273,c_2]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_402,plain,
% 3.65/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_299,c_8]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_404,plain,
% 3.65/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_402,c_299]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5278,plain,
% 3.65/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_5277,c_404]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5346,plain,
% 3.65/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_2345,c_5278]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_10,negated_conjecture,
% 3.65/0.99      ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_177,plain,
% 3.65/0.99      ( r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_15375,plain,
% 3.65/0.99      ( $false ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_5346,c_177]) ).
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  ------                               Statistics
% 3.65/0.99  
% 3.65/0.99  ------ General
% 3.65/0.99  
% 3.65/0.99  abstr_ref_over_cycles:                  0
% 3.65/0.99  abstr_ref_under_cycles:                 0
% 3.65/0.99  gc_basic_clause_elim:                   0
% 3.65/0.99  forced_gc_time:                         0
% 3.65/0.99  parsing_time:                           0.008
% 3.65/0.99  unif_index_cands_time:                  0.
% 3.65/0.99  unif_index_add_time:                    0.
% 3.65/0.99  orderings_time:                         0.
% 3.65/0.99  out_proof_time:                         0.006
% 3.65/0.99  total_time:                             0.446
% 3.65/0.99  num_of_symbols:                         38
% 3.65/0.99  num_of_terms:                           20608
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing
% 3.65/0.99  
% 3.65/0.99  num_of_splits:                          0
% 3.65/0.99  num_of_split_atoms:                     0
% 3.65/0.99  num_of_reused_defs:                     0
% 3.65/0.99  num_eq_ax_congr_red:                    0
% 3.65/0.99  num_of_sem_filtered_clauses:            1
% 3.65/0.99  num_of_subtypes:                        0
% 3.65/0.99  monotx_restored_types:                  0
% 3.65/0.99  sat_num_of_epr_types:                   0
% 3.65/0.99  sat_num_of_non_cyclic_types:            0
% 3.65/0.99  sat_guarded_non_collapsed_types:        0
% 3.65/0.99  num_pure_diseq_elim:                    0
% 3.65/0.99  simp_replaced_by:                       0
% 3.65/0.99  res_preprocessed:                       46
% 3.65/0.99  prep_upred:                             0
% 3.65/0.99  prep_unflattend:                        2
% 3.65/0.99  smt_new_axioms:                         0
% 3.65/0.99  pred_elim_cands:                        1
% 3.65/0.99  pred_elim:                              0
% 3.65/0.99  pred_elim_cl:                           0
% 3.65/0.99  pred_elim_cycles:                       1
% 3.65/0.99  merged_defs:                            0
% 3.65/0.99  merged_defs_ncl:                        0
% 3.65/0.99  bin_hyper_res:                          0
% 3.65/0.99  prep_cycles:                            3
% 3.65/0.99  pred_elim_time:                         0.
% 3.65/0.99  splitting_time:                         0.
% 3.65/0.99  sem_filter_time:                        0.
% 3.65/0.99  monotx_time:                            0.
% 3.65/0.99  subtype_inf_time:                       0.
% 3.65/0.99  
% 3.65/0.99  ------ Problem properties
% 3.65/0.99  
% 3.65/0.99  clauses:                                11
% 3.65/0.99  conjectures:                            1
% 3.65/0.99  epr:                                    2
% 3.65/0.99  horn:                                   11
% 3.65/0.99  ground:                                 2
% 3.65/0.99  unary:                                  10
% 3.65/0.99  binary:                                 1
% 3.65/0.99  lits:                                   12
% 3.65/0.99  lits_eq:                                8
% 3.65/0.99  fd_pure:                                0
% 3.65/0.99  fd_pseudo:                              0
% 3.65/0.99  fd_cond:                                1
% 3.65/0.99  fd_pseudo_cond:                         0
% 3.65/0.99  ac_symbols:                             0
% 3.65/0.99  
% 3.65/0.99  ------ Propositional Solver
% 3.65/0.99  
% 3.65/0.99  prop_solver_calls:                      26
% 3.65/0.99  prop_fast_solver_calls:                 272
% 3.65/0.99  smt_solver_calls:                       0
% 3.65/0.99  smt_fast_solver_calls:                  0
% 3.65/0.99  prop_num_of_clauses:                    5179
% 3.65/0.99  prop_preprocess_simplified:             7505
% 3.65/0.99  prop_fo_subsumed:                       0
% 3.65/0.99  prop_solver_time:                       0.
% 3.65/0.99  smt_solver_time:                        0.
% 3.65/0.99  smt_fast_solver_time:                   0.
% 3.65/0.99  prop_fast_solver_time:                  0.
% 3.65/0.99  prop_unsat_core_time:                   0.
% 3.65/0.99  
% 3.65/0.99  ------ QBF
% 3.65/0.99  
% 3.65/0.99  qbf_q_res:                              0
% 3.65/0.99  qbf_num_tautologies:                    0
% 3.65/0.99  qbf_prep_cycles:                        0
% 3.65/0.99  
% 3.65/0.99  ------ BMC1
% 3.65/0.99  
% 3.65/0.99  bmc1_current_bound:                     -1
% 3.65/0.99  bmc1_last_solved_bound:                 -1
% 3.65/0.99  bmc1_unsat_core_size:                   -1
% 3.65/0.99  bmc1_unsat_core_parents_size:           -1
% 3.65/0.99  bmc1_merge_next_fun:                    0
% 3.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation
% 3.65/0.99  
% 3.65/0.99  inst_num_of_clauses:                    1442
% 3.65/0.99  inst_num_in_passive:                    802
% 3.65/0.99  inst_num_in_active:                     492
% 3.65/0.99  inst_num_in_unprocessed:                148
% 3.65/0.99  inst_num_of_loops:                      500
% 3.65/0.99  inst_num_of_learning_restarts:          0
% 3.65/0.99  inst_num_moves_active_passive:          2
% 3.65/0.99  inst_lit_activity:                      0
% 3.65/0.99  inst_lit_activity_moves:                0
% 3.65/0.99  inst_num_tautologies:                   0
% 3.65/0.99  inst_num_prop_implied:                  0
% 3.65/0.99  inst_num_existing_simplified:           0
% 3.65/0.99  inst_num_eq_res_simplified:             0
% 3.65/0.99  inst_num_child_elim:                    0
% 3.65/0.99  inst_num_of_dismatching_blockings:      174
% 3.65/0.99  inst_num_of_non_proper_insts:           1164
% 3.65/0.99  inst_num_of_duplicates:                 0
% 3.65/0.99  inst_inst_num_from_inst_to_res:         0
% 3.65/0.99  inst_dismatching_checking_time:         0.
% 3.65/0.99  
% 3.65/0.99  ------ Resolution
% 3.65/0.99  
% 3.65/0.99  res_num_of_clauses:                     0
% 3.65/0.99  res_num_in_passive:                     0
% 3.65/0.99  res_num_in_active:                      0
% 3.65/0.99  res_num_of_loops:                       49
% 3.65/0.99  res_forward_subset_subsumed:            123
% 3.65/0.99  res_backward_subset_subsumed:           0
% 3.65/0.99  res_forward_subsumed:                   0
% 3.65/0.99  res_backward_subsumed:                  0
% 3.65/0.99  res_forward_subsumption_resolution:     0
% 3.65/0.99  res_backward_subsumption_resolution:    0
% 3.65/0.99  res_clause_to_clause_subsumption:       8847
% 3.65/0.99  res_orphan_elimination:                 0
% 3.65/0.99  res_tautology_del:                      89
% 3.65/0.99  res_num_eq_res_simplified:              0
% 3.65/0.99  res_num_sel_changes:                    0
% 3.65/0.99  res_moves_from_active_to_pass:          0
% 3.65/0.99  
% 3.65/0.99  ------ Superposition
% 3.65/0.99  
% 3.65/0.99  sup_time_total:                         0.
% 3.65/0.99  sup_time_generating:                    0.
% 3.65/0.99  sup_time_sim_full:                      0.
% 3.65/0.99  sup_time_sim_immed:                     0.
% 3.65/0.99  
% 3.65/0.99  sup_num_of_clauses:                     891
% 3.65/0.99  sup_num_in_active:                      91
% 3.65/0.99  sup_num_in_passive:                     800
% 3.65/0.99  sup_num_of_loops:                       99
% 3.65/0.99  sup_fw_superposition:                   2126
% 3.65/0.99  sup_bw_superposition:                   1709
% 3.65/0.99  sup_immediate_simplified:               1745
% 3.65/0.99  sup_given_eliminated:                   4
% 3.65/0.99  comparisons_done:                       0
% 3.65/0.99  comparisons_avoided:                    0
% 3.65/0.99  
% 3.65/0.99  ------ Simplifications
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  sim_fw_subset_subsumed:                 0
% 3.65/0.99  sim_bw_subset_subsumed:                 0
% 3.65/0.99  sim_fw_subsumed:                        491
% 3.65/0.99  sim_bw_subsumed:                        7
% 3.65/0.99  sim_fw_subsumption_res:                 0
% 3.65/0.99  sim_bw_subsumption_res:                 0
% 3.65/0.99  sim_tautology_del:                      0
% 3.65/0.99  sim_eq_tautology_del:                   205
% 3.65/0.99  sim_eq_res_simp:                        0
% 3.65/0.99  sim_fw_demodulated:                     756
% 3.65/0.99  sim_bw_demodulated:                     37
% 3.65/0.99  sim_light_normalised:                   710
% 3.65/0.99  sim_joinable_taut:                      0
% 3.65/0.99  sim_joinable_simp:                      0
% 3.65/0.99  sim_ac_normalised:                      0
% 3.65/0.99  sim_smt_subsumption:                    0
% 3.65/0.99  
%------------------------------------------------------------------------------
