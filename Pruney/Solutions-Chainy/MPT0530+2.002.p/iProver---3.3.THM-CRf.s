%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:36 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of clauses        :   32 (  32 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 170 expanded)
%              Number of equality atoms :   61 (  75 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).

fof(f60,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_489,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_481,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_492,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2180,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_492])).

cnf(c_6169,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_2180])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_490,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6181,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6169,c_490])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_491,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_494,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1895,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_494])).

cnf(c_6445,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6181,c_1895])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_480,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_483,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1543,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) ),
    inference(superposition,[status(thm)],[c_480,c_483])).

cnf(c_92477,plain,
    ( k8_relat_1(k4_xboole_0(sK0,k1_xboole_0),sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_6445,c_1543])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_92483,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_92477,c_5])).

cnf(c_233,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_824,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_234,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_679,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X0
    | k8_relat_1(sK0,sK2) != X0
    | k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_823,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_18,negated_conjecture,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92483,c_824,c_823,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.77/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/2.99  
% 19.77/2.99  ------  iProver source info
% 19.77/2.99  
% 19.77/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.77/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/2.99  git: non_committed_changes: false
% 19.77/2.99  git: last_make_outside_of_git: false
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  ------ Parsing...
% 19.77/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/2.99  ------ Proving...
% 19.77/2.99  ------ Problem Properties 
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  clauses                                 20
% 19.77/2.99  conjectures                             3
% 19.77/2.99  EPR                                     6
% 19.77/2.99  Horn                                    20
% 19.77/2.99  unary                                   11
% 19.77/2.99  binary                                  5
% 19.77/2.99  lits                                    33
% 19.77/2.99  lits eq                                 10
% 19.77/2.99  fd_pure                                 0
% 19.77/2.99  fd_pseudo                               0
% 19.77/2.99  fd_cond                                 0
% 19.77/2.99  fd_pseudo_cond                          1
% 19.77/2.99  AC symbols                              0
% 19.77/2.99  
% 19.77/2.99  ------ Input Options Time Limit: Unbounded
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  Current options:
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ Proving...
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS status Theorem for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  fof(f7,axiom,(
% 19.77/2.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f46,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f7])).
% 19.77/2.99  
% 19.77/2.99  fof(f19,conjecture,(
% 19.77/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f20,negated_conjecture,(
% 19.77/2.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 19.77/2.99    inference(negated_conjecture,[],[f19])).
% 19.77/2.99  
% 19.77/2.99  fof(f32,plain,(
% 19.77/2.99    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 19.77/2.99    inference(ennf_transformation,[],[f20])).
% 19.77/2.99  
% 19.77/2.99  fof(f33,plain,(
% 19.77/2.99    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 19.77/2.99    inference(flattening,[],[f32])).
% 19.77/2.99  
% 19.77/2.99  fof(f36,plain,(
% 19.77/2.99    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f37,plain,(
% 19.77/2.99    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 19.77/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).
% 19.77/2.99  
% 19.77/2.99  fof(f60,plain,(
% 19.77/2.99    r1_tarski(sK0,sK1)),
% 19.77/2.99    inference(cnf_transformation,[],[f37])).
% 19.77/2.99  
% 19.77/2.99  fof(f2,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f21,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.77/2.99    inference(ennf_transformation,[],[f2])).
% 19.77/2.99  
% 19.77/2.99  fof(f22,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.77/2.99    inference(flattening,[],[f21])).
% 19.77/2.99  
% 19.77/2.99  fof(f41,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f22])).
% 19.77/2.99  
% 19.77/2.99  fof(f5,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f23,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 19.77/2.99    inference(ennf_transformation,[],[f5])).
% 19.77/2.99  
% 19.77/2.99  fof(f44,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f23])).
% 19.77/2.99  
% 19.77/2.99  fof(f3,axiom,(
% 19.77/2.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f42,plain,(
% 19.77/2.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f3])).
% 19.77/2.99  
% 19.77/2.99  fof(f1,axiom,(
% 19.77/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f34,plain,(
% 19.77/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.77/2.99    inference(nnf_transformation,[],[f1])).
% 19.77/2.99  
% 19.77/2.99  fof(f35,plain,(
% 19.77/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.77/2.99    inference(flattening,[],[f34])).
% 19.77/2.99  
% 19.77/2.99  fof(f40,plain,(
% 19.77/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f59,plain,(
% 19.77/2.99    v1_relat_1(sK2)),
% 19.77/2.99    inference(cnf_transformation,[],[f37])).
% 19.77/2.99  
% 19.77/2.99  fof(f16,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f29,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.77/2.99    inference(ennf_transformation,[],[f16])).
% 19.77/2.99  
% 19.77/2.99  fof(f55,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f29])).
% 19.77/2.99  
% 19.77/2.99  fof(f6,axiom,(
% 19.77/2.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f45,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f6])).
% 19.77/2.99  
% 19.77/2.99  fof(f64,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 19.77/2.99    inference(definition_unfolding,[],[f55,f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f4,axiom,(
% 19.77/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f43,plain,(
% 19.77/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.77/2.99    inference(cnf_transformation,[],[f4])).
% 19.77/2.99  
% 19.77/2.99  fof(f61,plain,(
% 19.77/2.99    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 19.77/2.99    inference(cnf_transformation,[],[f37])).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7,plain,
% 19.77/2.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_489,plain,
% 19.77/2.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_19,negated_conjecture,
% 19.77/2.99      ( r1_tarski(sK0,sK1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_481,plain,
% 19.77/2.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3,plain,
% 19.77/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.77/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_492,plain,
% 19.77/2.99      ( r1_tarski(X0,X1) != iProver_top
% 19.77/2.99      | r1_tarski(X1,X2) != iProver_top
% 19.77/2.99      | r1_tarski(X0,X2) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2180,plain,
% 19.77/2.99      ( r1_tarski(sK1,X0) != iProver_top
% 19.77/2.99      | r1_tarski(sK0,X0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_481,c_492]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6169,plain,
% 19.77/2.99      ( r1_tarski(sK0,k2_xboole_0(sK1,X0)) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_489,c_2180]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6,plain,
% 19.77/2.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 19.77/2.99      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 19.77/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_490,plain,
% 19.77/2.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 19.77/2.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6181,plain,
% 19.77/2.99      ( r1_tarski(k4_xboole_0(sK0,sK1),X0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6169,c_490]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_4,plain,
% 19.77/2.99      ( r1_tarski(k1_xboole_0,X0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_491,plain,
% 19.77/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_0,plain,
% 19.77/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.77/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_494,plain,
% 19.77/2.99      ( X0 = X1
% 19.77/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.77/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1895,plain,
% 19.77/2.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_491,c_494]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6445,plain,
% 19.77/2.99      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6181,c_1895]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_20,negated_conjecture,
% 19.77/2.99      ( v1_relat_1(sK2) ),
% 19.77/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_480,plain,
% 19.77/2.99      ( v1_relat_1(sK2) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_14,plain,
% 19.77/2.99      ( ~ v1_relat_1(X0)
% 19.77/2.99      | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_483,plain,
% 19.77/2.99      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
% 19.77/2.99      | v1_relat_1(X2) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1543,plain,
% 19.77/2.99      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_480,c_483]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_92477,plain,
% 19.77/2.99      ( k8_relat_1(k4_xboole_0(sK0,k1_xboole_0),sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6445,c_1543]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_92483,plain,
% 19.77/2.99      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k8_relat_1(sK0,sK2) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_92477,c_5]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_233,plain,( X0 = X0 ),theory(equality) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_824,plain,
% 19.77/2.99      ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,sK2) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_233]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_234,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_679,plain,
% 19.77/2.99      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X0
% 19.77/2.99      | k8_relat_1(sK0,sK2) != X0
% 19.77/2.99      | k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_234]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_823,plain,
% 19.77/2.99      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(sK0,sK2)
% 19.77/2.99      | k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
% 19.77/2.99      | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_679]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_18,negated_conjecture,
% 19.77/2.99      ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(contradiction,plain,
% 19.77/2.99      ( $false ),
% 19.77/2.99      inference(minisat,[status(thm)],[c_92483,c_824,c_823,c_18]) ).
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  ------                               Statistics
% 19.77/2.99  
% 19.77/2.99  ------ Selected
% 19.77/2.99  
% 19.77/2.99  total_time:                             2.322
% 19.77/2.99  
%------------------------------------------------------------------------------
