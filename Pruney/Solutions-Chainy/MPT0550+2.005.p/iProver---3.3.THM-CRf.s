%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:29 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   67 (  87 expanded)
%              Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 ( 233 expanded)
%              Number of equality atoms :   75 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK3,sK2)
      & r1_tarski(sK2,k1_relat_1(sK3))
      & k1_xboole_0 != sK2
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2)
    & r1_tarski(sK2,k1_relat_1(sK3))
    & k1_xboole_0 != sK2
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f21])).

fof(f34,plain,(
    k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f33,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_258,plain,
    ( r2_hidden(sK1(X0_42),X0_42)
    | k1_xboole_0 = X0_42 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_363,plain,
    ( k1_xboole_0 = X0_42
    | r2_hidden(sK1(X0_42),X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_257,plain,
    ( k2_tarski(X0_42,X1_42) = k2_tarski(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_256,negated_conjecture,
    ( k1_xboole_0 = k9_relat_1(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_138,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | k9_relat_1(X0,X1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_139,plain,
    ( r1_xboole_0(k1_relat_1(sK3),X0)
    | k9_relat_1(sK3,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | X3 != X2
    | k9_relat_1(sK3,X3) != k1_xboole_0
    | k1_relat_1(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_139])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X1)))
    | k9_relat_1(sK3,X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X0_42)))
    | k9_relat_1(sK3,X0_42) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_366,plain,
    ( k9_relat_1(sK3,X0_42) != k1_xboole_0
    | r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_425,plain,
    ( r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_256,c_366])).

cnf(c_560,plain,
    ( r2_hidden(X0_41,k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_257,c_425])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_102,plain,
    ( k1_relat_1(sK3) != X0
    | k1_setfam_1(k2_tarski(X1,X0)) = X1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_103,plain,
    ( k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3))) = sK2 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_254,plain,
    ( k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3))) = sK2 ),
    inference(subtyping,[status(esa)],[c_103])).

cnf(c_561,plain,
    ( r2_hidden(X0_41,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_560,c_254])).

cnf(c_644,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_363,c_561])).

cnf(c_263,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_406,plain,
    ( sK2 != X0_42
    | k1_xboole_0 != X0_42
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_407,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_255,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_261,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_277,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_644,c_407,c_255,c_277])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.10/1.00  
% 1.10/1.00  ------  iProver source info
% 1.10/1.00  
% 1.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.10/1.00  git: non_committed_changes: false
% 1.10/1.00  git: last_make_outside_of_git: false
% 1.10/1.00  
% 1.10/1.00  ------ 
% 1.10/1.00  
% 1.10/1.00  ------ Input Options
% 1.10/1.00  
% 1.10/1.00  --out_options                           all
% 1.10/1.00  --tptp_safe_out                         true
% 1.10/1.00  --problem_path                          ""
% 1.10/1.00  --include_path                          ""
% 1.10/1.00  --clausifier                            res/vclausify_rel
% 1.10/1.00  --clausifier_options                    --mode clausify
% 1.10/1.00  --stdin                                 false
% 1.10/1.00  --stats_out                             all
% 1.10/1.00  
% 1.10/1.00  ------ General Options
% 1.10/1.00  
% 1.10/1.00  --fof                                   false
% 1.10/1.00  --time_out_real                         305.
% 1.10/1.00  --time_out_virtual                      -1.
% 1.10/1.00  --symbol_type_check                     false
% 1.10/1.00  --clausify_out                          false
% 1.10/1.00  --sig_cnt_out                           false
% 1.10/1.00  --trig_cnt_out                          false
% 1.10/1.00  --trig_cnt_out_tolerance                1.
% 1.10/1.00  --trig_cnt_out_sk_spl                   false
% 1.10/1.00  --abstr_cl_out                          false
% 1.10/1.00  
% 1.10/1.00  ------ Global Options
% 1.10/1.00  
% 1.10/1.00  --schedule                              default
% 1.10/1.00  --add_important_lit                     false
% 1.10/1.00  --prop_solver_per_cl                    1000
% 1.10/1.00  --min_unsat_core                        false
% 1.10/1.00  --soft_assumptions                      false
% 1.10/1.00  --soft_lemma_size                       3
% 1.10/1.00  --prop_impl_unit_size                   0
% 1.10/1.00  --prop_impl_unit                        []
% 1.10/1.00  --share_sel_clauses                     true
% 1.10/1.00  --reset_solvers                         false
% 1.10/1.00  --bc_imp_inh                            [conj_cone]
% 1.10/1.00  --conj_cone_tolerance                   3.
% 1.10/1.00  --extra_neg_conj                        none
% 1.10/1.00  --large_theory_mode                     true
% 1.10/1.00  --prolific_symb_bound                   200
% 1.10/1.00  --lt_threshold                          2000
% 1.10/1.00  --clause_weak_htbl                      true
% 1.10/1.00  --gc_record_bc_elim                     false
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing Options
% 1.10/1.00  
% 1.10/1.00  --preprocessing_flag                    true
% 1.10/1.00  --time_out_prep_mult                    0.1
% 1.10/1.00  --splitting_mode                        input
% 1.10/1.00  --splitting_grd                         true
% 1.10/1.00  --splitting_cvd                         false
% 1.10/1.00  --splitting_cvd_svl                     false
% 1.10/1.00  --splitting_nvd                         32
% 1.10/1.00  --sub_typing                            true
% 1.10/1.00  --prep_gs_sim                           true
% 1.10/1.00  --prep_unflatten                        true
% 1.10/1.00  --prep_res_sim                          true
% 1.10/1.00  --prep_upred                            true
% 1.10/1.00  --prep_sem_filter                       exhaustive
% 1.10/1.00  --prep_sem_filter_out                   false
% 1.10/1.00  --pred_elim                             true
% 1.10/1.00  --res_sim_input                         true
% 1.10/1.00  --eq_ax_congr_red                       true
% 1.10/1.00  --pure_diseq_elim                       true
% 1.10/1.00  --brand_transform                       false
% 1.10/1.00  --non_eq_to_eq                          false
% 1.10/1.00  --prep_def_merge                        true
% 1.10/1.00  --prep_def_merge_prop_impl              false
% 1.10/1.00  --prep_def_merge_mbd                    true
% 1.10/1.00  --prep_def_merge_tr_red                 false
% 1.10/1.00  --prep_def_merge_tr_cl                  false
% 1.10/1.00  --smt_preprocessing                     true
% 1.10/1.00  --smt_ac_axioms                         fast
% 1.10/1.00  --preprocessed_out                      false
% 1.10/1.00  --preprocessed_stats                    false
% 1.10/1.00  
% 1.10/1.00  ------ Abstraction refinement Options
% 1.10/1.00  
% 1.10/1.00  --abstr_ref                             []
% 1.10/1.00  --abstr_ref_prep                        false
% 1.10/1.00  --abstr_ref_until_sat                   false
% 1.10/1.00  --abstr_ref_sig_restrict                funpre
% 1.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.00  --abstr_ref_under                       []
% 1.10/1.00  
% 1.10/1.00  ------ SAT Options
% 1.10/1.00  
% 1.10/1.00  --sat_mode                              false
% 1.10/1.00  --sat_fm_restart_options                ""
% 1.10/1.00  --sat_gr_def                            false
% 1.10/1.00  --sat_epr_types                         true
% 1.10/1.00  --sat_non_cyclic_types                  false
% 1.10/1.00  --sat_finite_models                     false
% 1.10/1.00  --sat_fm_lemmas                         false
% 1.10/1.00  --sat_fm_prep                           false
% 1.10/1.00  --sat_fm_uc_incr                        true
% 1.10/1.00  --sat_out_model                         small
% 1.10/1.00  --sat_out_clauses                       false
% 1.10/1.00  
% 1.10/1.00  ------ QBF Options
% 1.10/1.00  
% 1.10/1.00  --qbf_mode                              false
% 1.10/1.00  --qbf_elim_univ                         false
% 1.10/1.00  --qbf_dom_inst                          none
% 1.10/1.00  --qbf_dom_pre_inst                      false
% 1.10/1.00  --qbf_sk_in                             false
% 1.10/1.00  --qbf_pred_elim                         true
% 1.10/1.00  --qbf_split                             512
% 1.10/1.00  
% 1.10/1.00  ------ BMC1 Options
% 1.10/1.00  
% 1.10/1.00  --bmc1_incremental                      false
% 1.10/1.00  --bmc1_axioms                           reachable_all
% 1.10/1.00  --bmc1_min_bound                        0
% 1.10/1.00  --bmc1_max_bound                        -1
% 1.10/1.00  --bmc1_max_bound_default                -1
% 1.10/1.00  --bmc1_symbol_reachability              true
% 1.10/1.00  --bmc1_property_lemmas                  false
% 1.10/1.00  --bmc1_k_induction                      false
% 1.10/1.00  --bmc1_non_equiv_states                 false
% 1.10/1.00  --bmc1_deadlock                         false
% 1.10/1.00  --bmc1_ucm                              false
% 1.10/1.00  --bmc1_add_unsat_core                   none
% 1.10/1.00  --bmc1_unsat_core_children              false
% 1.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.00  --bmc1_out_stat                         full
% 1.10/1.00  --bmc1_ground_init                      false
% 1.10/1.00  --bmc1_pre_inst_next_state              false
% 1.10/1.00  --bmc1_pre_inst_state                   false
% 1.10/1.00  --bmc1_pre_inst_reach_state             false
% 1.10/1.00  --bmc1_out_unsat_core                   false
% 1.10/1.00  --bmc1_aig_witness_out                  false
% 1.10/1.00  --bmc1_verbose                          false
% 1.10/1.00  --bmc1_dump_clauses_tptp                false
% 1.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.00  --bmc1_dump_file                        -
% 1.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.00  --bmc1_ucm_extend_mode                  1
% 1.10/1.00  --bmc1_ucm_init_mode                    2
% 1.10/1.00  --bmc1_ucm_cone_mode                    none
% 1.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.00  --bmc1_ucm_relax_model                  4
% 1.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.00  --bmc1_ucm_layered_model                none
% 1.10/1.00  --bmc1_ucm_max_lemma_size               10
% 1.10/1.00  
% 1.10/1.00  ------ AIG Options
% 1.10/1.00  
% 1.10/1.00  --aig_mode                              false
% 1.10/1.00  
% 1.10/1.00  ------ Instantiation Options
% 1.10/1.00  
% 1.10/1.00  --instantiation_flag                    true
% 1.10/1.00  --inst_sos_flag                         false
% 1.10/1.00  --inst_sos_phase                        true
% 1.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel_side                     num_symb
% 1.10/1.00  --inst_solver_per_active                1400
% 1.10/1.00  --inst_solver_calls_frac                1.
% 1.10/1.00  --inst_passive_queue_type               priority_queues
% 1.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.00  --inst_passive_queues_freq              [25;2]
% 1.10/1.00  --inst_dismatching                      true
% 1.10/1.00  --inst_eager_unprocessed_to_passive     true
% 1.10/1.00  --inst_prop_sim_given                   true
% 1.10/1.00  --inst_prop_sim_new                     false
% 1.10/1.00  --inst_subs_new                         false
% 1.10/1.00  --inst_eq_res_simp                      false
% 1.10/1.00  --inst_subs_given                       false
% 1.10/1.00  --inst_orphan_elimination               true
% 1.10/1.00  --inst_learning_loop_flag               true
% 1.10/1.00  --inst_learning_start                   3000
% 1.10/1.00  --inst_learning_factor                  2
% 1.10/1.00  --inst_start_prop_sim_after_learn       3
% 1.10/1.00  --inst_sel_renew                        solver
% 1.10/1.00  --inst_lit_activity_flag                true
% 1.10/1.00  --inst_restr_to_given                   false
% 1.10/1.00  --inst_activity_threshold               500
% 1.10/1.00  --inst_out_proof                        true
% 1.10/1.00  
% 1.10/1.00  ------ Resolution Options
% 1.10/1.00  
% 1.10/1.00  --resolution_flag                       true
% 1.10/1.00  --res_lit_sel                           adaptive
% 1.10/1.00  --res_lit_sel_side                      none
% 1.10/1.00  --res_ordering                          kbo
% 1.10/1.00  --res_to_prop_solver                    active
% 1.10/1.00  --res_prop_simpl_new                    false
% 1.10/1.00  --res_prop_simpl_given                  true
% 1.10/1.00  --res_passive_queue_type                priority_queues
% 1.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.00  --res_passive_queues_freq               [15;5]
% 1.10/1.00  --res_forward_subs                      full
% 1.10/1.00  --res_backward_subs                     full
% 1.10/1.00  --res_forward_subs_resolution           true
% 1.10/1.00  --res_backward_subs_resolution          true
% 1.10/1.00  --res_orphan_elimination                true
% 1.10/1.00  --res_time_limit                        2.
% 1.10/1.00  --res_out_proof                         true
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Options
% 1.10/1.00  
% 1.10/1.00  --superposition_flag                    true
% 1.10/1.00  --sup_passive_queue_type                priority_queues
% 1.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.00  --demod_completeness_check              fast
% 1.10/1.00  --demod_use_ground                      true
% 1.10/1.00  --sup_to_prop_solver                    passive
% 1.10/1.00  --sup_prop_simpl_new                    true
% 1.10/1.00  --sup_prop_simpl_given                  true
% 1.10/1.00  --sup_fun_splitting                     false
% 1.10/1.00  --sup_smt_interval                      50000
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Simplification Setup
% 1.10/1.00  
% 1.10/1.00  --sup_indices_passive                   []
% 1.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_full_bw                           [BwDemod]
% 1.10/1.00  --sup_immed_triv                        [TrivRules]
% 1.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_immed_bw_main                     []
% 1.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  
% 1.10/1.00  ------ Combination Options
% 1.10/1.00  
% 1.10/1.00  --comb_res_mult                         3
% 1.10/1.00  --comb_sup_mult                         2
% 1.10/1.00  --comb_inst_mult                        10
% 1.10/1.00  
% 1.10/1.00  ------ Debug Options
% 1.10/1.00  
% 1.10/1.00  --dbg_backtrace                         false
% 1.10/1.00  --dbg_dump_prop_clauses                 false
% 1.10/1.00  --dbg_dump_prop_clauses_file            -
% 1.10/1.00  --dbg_out_stat                          false
% 1.10/1.00  ------ Parsing...
% 1.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.10/1.00  ------ Proving...
% 1.10/1.00  ------ Problem Properties 
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  clauses                                 8
% 1.10/1.00  conjectures                             2
% 1.10/1.00  EPR                                     1
% 1.10/1.00  Horn                                    6
% 1.10/1.00  unary                                   4
% 1.10/1.00  binary                                  4
% 1.10/1.00  lits                                    12
% 1.10/1.00  lits eq                                 7
% 1.10/1.00  fd_pure                                 0
% 1.10/1.00  fd_pseudo                               0
% 1.10/1.00  fd_cond                                 1
% 1.10/1.00  fd_pseudo_cond                          0
% 1.10/1.00  AC symbols                              0
% 1.10/1.00  
% 1.10/1.00  ------ Schedule dynamic 5 is on 
% 1.10/1.00  
% 1.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  ------ 
% 1.10/1.00  Current options:
% 1.10/1.00  ------ 
% 1.10/1.00  
% 1.10/1.00  ------ Input Options
% 1.10/1.00  
% 1.10/1.00  --out_options                           all
% 1.10/1.00  --tptp_safe_out                         true
% 1.10/1.00  --problem_path                          ""
% 1.10/1.00  --include_path                          ""
% 1.10/1.00  --clausifier                            res/vclausify_rel
% 1.10/1.00  --clausifier_options                    --mode clausify
% 1.10/1.00  --stdin                                 false
% 1.10/1.00  --stats_out                             all
% 1.10/1.00  
% 1.10/1.00  ------ General Options
% 1.10/1.00  
% 1.10/1.00  --fof                                   false
% 1.10/1.00  --time_out_real                         305.
% 1.10/1.00  --time_out_virtual                      -1.
% 1.10/1.00  --symbol_type_check                     false
% 1.10/1.00  --clausify_out                          false
% 1.10/1.00  --sig_cnt_out                           false
% 1.10/1.00  --trig_cnt_out                          false
% 1.10/1.00  --trig_cnt_out_tolerance                1.
% 1.10/1.00  --trig_cnt_out_sk_spl                   false
% 1.10/1.00  --abstr_cl_out                          false
% 1.10/1.00  
% 1.10/1.00  ------ Global Options
% 1.10/1.00  
% 1.10/1.00  --schedule                              default
% 1.10/1.00  --add_important_lit                     false
% 1.10/1.00  --prop_solver_per_cl                    1000
% 1.10/1.00  --min_unsat_core                        false
% 1.10/1.00  --soft_assumptions                      false
% 1.10/1.00  --soft_lemma_size                       3
% 1.10/1.00  --prop_impl_unit_size                   0
% 1.10/1.00  --prop_impl_unit                        []
% 1.10/1.00  --share_sel_clauses                     true
% 1.10/1.00  --reset_solvers                         false
% 1.10/1.00  --bc_imp_inh                            [conj_cone]
% 1.10/1.00  --conj_cone_tolerance                   3.
% 1.10/1.00  --extra_neg_conj                        none
% 1.10/1.00  --large_theory_mode                     true
% 1.10/1.00  --prolific_symb_bound                   200
% 1.10/1.00  --lt_threshold                          2000
% 1.10/1.00  --clause_weak_htbl                      true
% 1.10/1.00  --gc_record_bc_elim                     false
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing Options
% 1.10/1.00  
% 1.10/1.00  --preprocessing_flag                    true
% 1.10/1.00  --time_out_prep_mult                    0.1
% 1.10/1.00  --splitting_mode                        input
% 1.10/1.00  --splitting_grd                         true
% 1.10/1.00  --splitting_cvd                         false
% 1.10/1.00  --splitting_cvd_svl                     false
% 1.10/1.00  --splitting_nvd                         32
% 1.10/1.00  --sub_typing                            true
% 1.10/1.00  --prep_gs_sim                           true
% 1.10/1.00  --prep_unflatten                        true
% 1.10/1.00  --prep_res_sim                          true
% 1.10/1.00  --prep_upred                            true
% 1.10/1.00  --prep_sem_filter                       exhaustive
% 1.10/1.00  --prep_sem_filter_out                   false
% 1.10/1.00  --pred_elim                             true
% 1.10/1.00  --res_sim_input                         true
% 1.10/1.00  --eq_ax_congr_red                       true
% 1.10/1.00  --pure_diseq_elim                       true
% 1.10/1.00  --brand_transform                       false
% 1.10/1.00  --non_eq_to_eq                          false
% 1.10/1.00  --prep_def_merge                        true
% 1.10/1.00  --prep_def_merge_prop_impl              false
% 1.10/1.00  --prep_def_merge_mbd                    true
% 1.10/1.00  --prep_def_merge_tr_red                 false
% 1.10/1.00  --prep_def_merge_tr_cl                  false
% 1.10/1.00  --smt_preprocessing                     true
% 1.10/1.00  --smt_ac_axioms                         fast
% 1.10/1.00  --preprocessed_out                      false
% 1.10/1.00  --preprocessed_stats                    false
% 1.10/1.00  
% 1.10/1.00  ------ Abstraction refinement Options
% 1.10/1.00  
% 1.10/1.00  --abstr_ref                             []
% 1.10/1.00  --abstr_ref_prep                        false
% 1.10/1.00  --abstr_ref_until_sat                   false
% 1.10/1.00  --abstr_ref_sig_restrict                funpre
% 1.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.00  --abstr_ref_under                       []
% 1.10/1.00  
% 1.10/1.00  ------ SAT Options
% 1.10/1.00  
% 1.10/1.00  --sat_mode                              false
% 1.10/1.00  --sat_fm_restart_options                ""
% 1.10/1.00  --sat_gr_def                            false
% 1.10/1.00  --sat_epr_types                         true
% 1.10/1.00  --sat_non_cyclic_types                  false
% 1.10/1.00  --sat_finite_models                     false
% 1.10/1.00  --sat_fm_lemmas                         false
% 1.10/1.00  --sat_fm_prep                           false
% 1.10/1.00  --sat_fm_uc_incr                        true
% 1.10/1.00  --sat_out_model                         small
% 1.10/1.00  --sat_out_clauses                       false
% 1.10/1.00  
% 1.10/1.00  ------ QBF Options
% 1.10/1.00  
% 1.10/1.00  --qbf_mode                              false
% 1.10/1.00  --qbf_elim_univ                         false
% 1.10/1.00  --qbf_dom_inst                          none
% 1.10/1.00  --qbf_dom_pre_inst                      false
% 1.10/1.00  --qbf_sk_in                             false
% 1.10/1.00  --qbf_pred_elim                         true
% 1.10/1.00  --qbf_split                             512
% 1.10/1.00  
% 1.10/1.00  ------ BMC1 Options
% 1.10/1.00  
% 1.10/1.00  --bmc1_incremental                      false
% 1.10/1.00  --bmc1_axioms                           reachable_all
% 1.10/1.00  --bmc1_min_bound                        0
% 1.10/1.00  --bmc1_max_bound                        -1
% 1.10/1.00  --bmc1_max_bound_default                -1
% 1.10/1.00  --bmc1_symbol_reachability              true
% 1.10/1.00  --bmc1_property_lemmas                  false
% 1.10/1.00  --bmc1_k_induction                      false
% 1.10/1.00  --bmc1_non_equiv_states                 false
% 1.10/1.00  --bmc1_deadlock                         false
% 1.10/1.00  --bmc1_ucm                              false
% 1.10/1.00  --bmc1_add_unsat_core                   none
% 1.10/1.00  --bmc1_unsat_core_children              false
% 1.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.00  --bmc1_out_stat                         full
% 1.10/1.00  --bmc1_ground_init                      false
% 1.10/1.00  --bmc1_pre_inst_next_state              false
% 1.10/1.00  --bmc1_pre_inst_state                   false
% 1.10/1.00  --bmc1_pre_inst_reach_state             false
% 1.10/1.00  --bmc1_out_unsat_core                   false
% 1.10/1.00  --bmc1_aig_witness_out                  false
% 1.10/1.00  --bmc1_verbose                          false
% 1.10/1.00  --bmc1_dump_clauses_tptp                false
% 1.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.00  --bmc1_dump_file                        -
% 1.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.00  --bmc1_ucm_extend_mode                  1
% 1.10/1.00  --bmc1_ucm_init_mode                    2
% 1.10/1.00  --bmc1_ucm_cone_mode                    none
% 1.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.00  --bmc1_ucm_relax_model                  4
% 1.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.00  --bmc1_ucm_layered_model                none
% 1.10/1.00  --bmc1_ucm_max_lemma_size               10
% 1.10/1.00  
% 1.10/1.00  ------ AIG Options
% 1.10/1.00  
% 1.10/1.00  --aig_mode                              false
% 1.10/1.00  
% 1.10/1.00  ------ Instantiation Options
% 1.10/1.00  
% 1.10/1.00  --instantiation_flag                    true
% 1.10/1.00  --inst_sos_flag                         false
% 1.10/1.00  --inst_sos_phase                        true
% 1.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel_side                     none
% 1.10/1.00  --inst_solver_per_active                1400
% 1.10/1.00  --inst_solver_calls_frac                1.
% 1.10/1.00  --inst_passive_queue_type               priority_queues
% 1.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.00  --inst_passive_queues_freq              [25;2]
% 1.10/1.00  --inst_dismatching                      true
% 1.10/1.00  --inst_eager_unprocessed_to_passive     true
% 1.10/1.00  --inst_prop_sim_given                   true
% 1.10/1.00  --inst_prop_sim_new                     false
% 1.10/1.00  --inst_subs_new                         false
% 1.10/1.00  --inst_eq_res_simp                      false
% 1.10/1.00  --inst_subs_given                       false
% 1.10/1.00  --inst_orphan_elimination               true
% 1.10/1.00  --inst_learning_loop_flag               true
% 1.10/1.00  --inst_learning_start                   3000
% 1.10/1.00  --inst_learning_factor                  2
% 1.10/1.00  --inst_start_prop_sim_after_learn       3
% 1.10/1.00  --inst_sel_renew                        solver
% 1.10/1.00  --inst_lit_activity_flag                true
% 1.10/1.00  --inst_restr_to_given                   false
% 1.10/1.00  --inst_activity_threshold               500
% 1.10/1.00  --inst_out_proof                        true
% 1.10/1.00  
% 1.10/1.00  ------ Resolution Options
% 1.10/1.00  
% 1.10/1.00  --resolution_flag                       false
% 1.10/1.00  --res_lit_sel                           adaptive
% 1.10/1.00  --res_lit_sel_side                      none
% 1.10/1.00  --res_ordering                          kbo
% 1.10/1.00  --res_to_prop_solver                    active
% 1.10/1.00  --res_prop_simpl_new                    false
% 1.10/1.00  --res_prop_simpl_given                  true
% 1.10/1.00  --res_passive_queue_type                priority_queues
% 1.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.00  --res_passive_queues_freq               [15;5]
% 1.10/1.00  --res_forward_subs                      full
% 1.10/1.00  --res_backward_subs                     full
% 1.10/1.00  --res_forward_subs_resolution           true
% 1.10/1.00  --res_backward_subs_resolution          true
% 1.10/1.00  --res_orphan_elimination                true
% 1.10/1.00  --res_time_limit                        2.
% 1.10/1.00  --res_out_proof                         true
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Options
% 1.10/1.00  
% 1.10/1.00  --superposition_flag                    true
% 1.10/1.00  --sup_passive_queue_type                priority_queues
% 1.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.00  --demod_completeness_check              fast
% 1.10/1.00  --demod_use_ground                      true
% 1.10/1.00  --sup_to_prop_solver                    passive
% 1.10/1.00  --sup_prop_simpl_new                    true
% 1.10/1.00  --sup_prop_simpl_given                  true
% 1.10/1.00  --sup_fun_splitting                     false
% 1.10/1.00  --sup_smt_interval                      50000
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Simplification Setup
% 1.10/1.00  
% 1.10/1.00  --sup_indices_passive                   []
% 1.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_full_bw                           [BwDemod]
% 1.10/1.00  --sup_immed_triv                        [TrivRules]
% 1.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_immed_bw_main                     []
% 1.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  
% 1.10/1.00  ------ Combination Options
% 1.10/1.00  
% 1.10/1.00  --comb_res_mult                         3
% 1.10/1.00  --comb_sup_mult                         2
% 1.10/1.00  --comb_inst_mult                        10
% 1.10/1.00  
% 1.10/1.00  ------ Debug Options
% 1.10/1.00  
% 1.10/1.00  --dbg_backtrace                         false
% 1.10/1.00  --dbg_dump_prop_clauses                 false
% 1.10/1.00  --dbg_dump_prop_clauses_file            -
% 1.10/1.00  --dbg_out_stat                          false
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  ------ Proving...
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  % SZS status Theorem for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  fof(f2,axiom,(
% 1.10/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f11,plain,(
% 1.10/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.10/1.00    inference(ennf_transformation,[],[f2])).
% 1.10/1.00  
% 1.10/1.00  fof(f18,plain,(
% 1.10/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f19,plain,(
% 1.10/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).
% 1.10/1.00  
% 1.10/1.00  fof(f25,plain,(
% 1.10/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.10/1.00    inference(cnf_transformation,[],[f19])).
% 1.10/1.00  
% 1.10/1.00  fof(f4,axiom,(
% 1.10/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f27,plain,(
% 1.10/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f4])).
% 1.10/1.00  
% 1.10/1.00  fof(f7,conjecture,(
% 1.10/1.00    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f8,negated_conjecture,(
% 1.10/1.00    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.10/1.00    inference(negated_conjecture,[],[f7])).
% 1.10/1.00  
% 1.10/1.00  fof(f14,plain,(
% 1.10/1.00    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 1.10/1.00    inference(ennf_transformation,[],[f8])).
% 1.10/1.00  
% 1.10/1.00  fof(f15,plain,(
% 1.10/1.00    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 1.10/1.00    inference(flattening,[],[f14])).
% 1.10/1.00  
% 1.10/1.00  fof(f21,plain,(
% 1.10/1.00    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK3,sK2) & r1_tarski(sK2,k1_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3))),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f22,plain,(
% 1.10/1.00    k1_xboole_0 = k9_relat_1(sK3,sK2) & r1_tarski(sK2,k1_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3)),
% 1.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f21])).
% 1.10/1.00  
% 1.10/1.00  fof(f34,plain,(
% 1.10/1.00    k1_xboole_0 = k9_relat_1(sK3,sK2)),
% 1.10/1.00    inference(cnf_transformation,[],[f22])).
% 1.10/1.00  
% 1.10/1.00  fof(f1,axiom,(
% 1.10/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f9,plain,(
% 1.10/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(rectify,[],[f1])).
% 1.10/1.00  
% 1.10/1.00  fof(f10,plain,(
% 1.10/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(ennf_transformation,[],[f9])).
% 1.10/1.00  
% 1.10/1.00  fof(f16,plain,(
% 1.10/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f17,plain,(
% 1.10/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 1.10/1.00  
% 1.10/1.00  fof(f24,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.10/1.00    inference(cnf_transformation,[],[f17])).
% 1.10/1.00  
% 1.10/1.00  fof(f5,axiom,(
% 1.10/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f28,plain,(
% 1.10/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.10/1.00    inference(cnf_transformation,[],[f5])).
% 1.10/1.00  
% 1.10/1.00  fof(f35,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.10/1.00    inference(definition_unfolding,[],[f24,f28])).
% 1.10/1.00  
% 1.10/1.00  fof(f6,axiom,(
% 1.10/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f13,plain,(
% 1.10/1.00    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.10/1.00    inference(ennf_transformation,[],[f6])).
% 1.10/1.00  
% 1.10/1.00  fof(f20,plain,(
% 1.10/1.00    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.10/1.00    inference(nnf_transformation,[],[f13])).
% 1.10/1.00  
% 1.10/1.00  fof(f29,plain,(
% 1.10/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f20])).
% 1.10/1.00  
% 1.10/1.00  fof(f31,plain,(
% 1.10/1.00    v1_relat_1(sK3)),
% 1.10/1.00    inference(cnf_transformation,[],[f22])).
% 1.10/1.00  
% 1.10/1.00  fof(f3,axiom,(
% 1.10/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f12,plain,(
% 1.10/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.10/1.00    inference(ennf_transformation,[],[f3])).
% 1.10/1.00  
% 1.10/1.00  fof(f26,plain,(
% 1.10/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f12])).
% 1.10/1.00  
% 1.10/1.00  fof(f37,plain,(
% 1.10/1.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.10/1.00    inference(definition_unfolding,[],[f26,f28])).
% 1.10/1.00  
% 1.10/1.00  fof(f33,plain,(
% 1.10/1.00    r1_tarski(sK2,k1_relat_1(sK3))),
% 1.10/1.00    inference(cnf_transformation,[],[f22])).
% 1.10/1.00  
% 1.10/1.00  fof(f32,plain,(
% 1.10/1.00    k1_xboole_0 != sK2),
% 1.10/1.00    inference(cnf_transformation,[],[f22])).
% 1.10/1.00  
% 1.10/1.00  cnf(c_2,plain,
% 1.10/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 1.10/1.00      inference(cnf_transformation,[],[f25]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_258,plain,
% 1.10/1.00      ( r2_hidden(sK1(X0_42),X0_42) | k1_xboole_0 = X0_42 ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_363,plain,
% 1.10/1.00      ( k1_xboole_0 = X0_42 | r2_hidden(sK1(X0_42),X0_42) = iProver_top ),
% 1.10/1.00      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_4,plain,
% 1.10/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f27]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_257,plain,
% 1.10/1.00      ( k2_tarski(X0_42,X1_42) = k2_tarski(X1_42,X0_42) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_7,negated_conjecture,
% 1.10/1.00      ( k1_xboole_0 = k9_relat_1(sK3,sK2) ),
% 1.10/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_256,negated_conjecture,
% 1.10/1.00      ( k1_xboole_0 = k9_relat_1(sK3,sK2) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_0,plain,
% 1.10/1.00      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 1.10/1.00      | ~ r1_xboole_0(X1,X2) ),
% 1.10/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_6,plain,
% 1.10/1.00      ( r1_xboole_0(k1_relat_1(X0),X1)
% 1.10/1.00      | ~ v1_relat_1(X0)
% 1.10/1.00      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 1.10/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_10,negated_conjecture,
% 1.10/1.00      ( v1_relat_1(sK3) ),
% 1.10/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_138,plain,
% 1.10/1.00      ( r1_xboole_0(k1_relat_1(X0),X1)
% 1.10/1.00      | k9_relat_1(X0,X1) != k1_xboole_0
% 1.10/1.00      | sK3 != X0 ),
% 1.10/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_139,plain,
% 1.10/1.00      ( r1_xboole_0(k1_relat_1(sK3),X0)
% 1.10/1.00      | k9_relat_1(sK3,X0) != k1_xboole_0 ),
% 1.10/1.00      inference(unflattening,[status(thm)],[c_138]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_193,plain,
% 1.10/1.00      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 1.10/1.00      | X3 != X2
% 1.10/1.00      | k9_relat_1(sK3,X3) != k1_xboole_0
% 1.10/1.00      | k1_relat_1(sK3) != X1 ),
% 1.10/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_139]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_194,plain,
% 1.10/1.00      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X1)))
% 1.10/1.00      | k9_relat_1(sK3,X1) != k1_xboole_0 ),
% 1.10/1.00      inference(unflattening,[status(thm)],[c_193]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_251,plain,
% 1.10/1.00      ( ~ r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X0_42)))
% 1.10/1.00      | k9_relat_1(sK3,X0_42) != k1_xboole_0 ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_194]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_366,plain,
% 1.10/1.00      ( k9_relat_1(sK3,X0_42) != k1_xboole_0
% 1.10/1.00      | r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),X0_42))) != iProver_top ),
% 1.10/1.00      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_425,plain,
% 1.10/1.00      ( r2_hidden(X0_41,k1_setfam_1(k2_tarski(k1_relat_1(sK3),sK2))) != iProver_top ),
% 1.10/1.00      inference(superposition,[status(thm)],[c_256,c_366]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_560,plain,
% 1.10/1.00      ( r2_hidden(X0_41,k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3)))) != iProver_top ),
% 1.10/1.00      inference(demodulation,[status(thm)],[c_257,c_425]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_3,plain,
% 1.10/1.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 1.10/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_8,negated_conjecture,
% 1.10/1.00      ( r1_tarski(sK2,k1_relat_1(sK3)) ),
% 1.10/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_102,plain,
% 1.10/1.00      ( k1_relat_1(sK3) != X0
% 1.10/1.00      | k1_setfam_1(k2_tarski(X1,X0)) = X1
% 1.10/1.00      | sK2 != X1 ),
% 1.10/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_103,plain,
% 1.10/1.00      ( k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3))) = sK2 ),
% 1.10/1.00      inference(unflattening,[status(thm)],[c_102]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_254,plain,
% 1.10/1.00      ( k1_setfam_1(k2_tarski(sK2,k1_relat_1(sK3))) = sK2 ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_103]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_561,plain,
% 1.10/1.00      ( r2_hidden(X0_41,sK2) != iProver_top ),
% 1.10/1.00      inference(light_normalisation,[status(thm)],[c_560,c_254]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_644,plain,
% 1.10/1.00      ( sK2 = k1_xboole_0 ),
% 1.10/1.00      inference(superposition,[status(thm)],[c_363,c_561]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_263,plain,
% 1.10/1.00      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 1.10/1.00      theory(equality) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_406,plain,
% 1.10/1.00      ( sK2 != X0_42 | k1_xboole_0 != X0_42 | k1_xboole_0 = sK2 ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_407,plain,
% 1.10/1.00      ( sK2 != k1_xboole_0
% 1.10/1.00      | k1_xboole_0 = sK2
% 1.10/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_406]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_9,negated_conjecture,
% 1.10/1.00      ( k1_xboole_0 != sK2 ),
% 1.10/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_255,negated_conjecture,
% 1.10/1.00      ( k1_xboole_0 != sK2 ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_261,plain,( X0_42 = X0_42 ),theory(equality) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_277,plain,
% 1.10/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_261]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(contradiction,plain,
% 1.10/1.00      ( $false ),
% 1.10/1.00      inference(minisat,[status(thm)],[c_644,c_407,c_255,c_277]) ).
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  ------                               Statistics
% 1.10/1.00  
% 1.10/1.00  ------ General
% 1.10/1.00  
% 1.10/1.00  abstr_ref_over_cycles:                  0
% 1.10/1.00  abstr_ref_under_cycles:                 0
% 1.10/1.00  gc_basic_clause_elim:                   0
% 1.10/1.00  forced_gc_time:                         0
% 1.10/1.00  parsing_time:                           0.011
% 1.10/1.00  unif_index_cands_time:                  0.
% 1.10/1.00  unif_index_add_time:                    0.
% 1.10/1.00  orderings_time:                         0.
% 1.10/1.00  out_proof_time:                         0.031
% 1.10/1.00  total_time:                             0.098
% 1.10/1.00  num_of_symbols:                         45
% 1.10/1.00  num_of_terms:                           926
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing
% 1.10/1.00  
% 1.10/1.00  num_of_splits:                          0
% 1.10/1.00  num_of_split_atoms:                     0
% 1.10/1.00  num_of_reused_defs:                     0
% 1.10/1.00  num_eq_ax_congr_red:                    12
% 1.10/1.00  num_of_sem_filtered_clauses:            1
% 1.10/1.00  num_of_subtypes:                        4
% 1.10/1.00  monotx_restored_types:                  1
% 1.10/1.00  sat_num_of_epr_types:                   0
% 1.10/1.00  sat_num_of_non_cyclic_types:            0
% 1.10/1.00  sat_guarded_non_collapsed_types:        0
% 1.10/1.00  num_pure_diseq_elim:                    0
% 1.10/1.00  simp_replaced_by:                       0
% 1.10/1.00  res_preprocessed:                       56
% 1.10/1.00  prep_upred:                             0
% 1.10/1.00  prep_unflattend:                        13
% 1.10/1.00  smt_new_axioms:                         0
% 1.10/1.00  pred_elim_cands:                        1
% 1.10/1.00  pred_elim:                              3
% 1.10/1.00  pred_elim_cl:                           3
% 1.10/1.00  pred_elim_cycles:                       6
% 1.10/1.00  merged_defs:                            0
% 1.10/1.00  merged_defs_ncl:                        0
% 1.10/1.00  bin_hyper_res:                          0
% 1.10/1.00  prep_cycles:                            4
% 1.10/1.00  pred_elim_time:                         0.004
% 1.10/1.00  splitting_time:                         0.
% 1.10/1.00  sem_filter_time:                        0.
% 1.10/1.00  monotx_time:                            0.001
% 1.10/1.00  subtype_inf_time:                       0.001
% 1.10/1.00  
% 1.10/1.00  ------ Problem properties
% 1.10/1.00  
% 1.10/1.00  clauses:                                8
% 1.10/1.00  conjectures:                            2
% 1.10/1.00  epr:                                    1
% 1.10/1.00  horn:                                   6
% 1.10/1.00  ground:                                 3
% 1.10/1.00  unary:                                  4
% 1.10/1.00  binary:                                 4
% 1.10/1.00  lits:                                   12
% 1.10/1.00  lits_eq:                                7
% 1.10/1.00  fd_pure:                                0
% 1.10/1.00  fd_pseudo:                              0
% 1.10/1.00  fd_cond:                                1
% 1.10/1.00  fd_pseudo_cond:                         0
% 1.10/1.00  ac_symbols:                             0
% 1.10/1.00  
% 1.10/1.00  ------ Propositional Solver
% 1.10/1.00  
% 1.10/1.00  prop_solver_calls:                      25
% 1.10/1.00  prop_fast_solver_calls:                 231
% 1.10/1.00  smt_solver_calls:                       0
% 1.10/1.00  smt_fast_solver_calls:                  0
% 1.10/1.00  prop_num_of_clauses:                    237
% 1.10/1.00  prop_preprocess_simplified:             1336
% 1.10/1.00  prop_fo_subsumed:                       0
% 1.10/1.00  prop_solver_time:                       0.
% 1.10/1.00  smt_solver_time:                        0.
% 1.10/1.00  smt_fast_solver_time:                   0.
% 1.10/1.00  prop_fast_solver_time:                  0.
% 1.10/1.00  prop_unsat_core_time:                   0.
% 1.10/1.00  
% 1.10/1.00  ------ QBF
% 1.10/1.00  
% 1.10/1.00  qbf_q_res:                              0
% 1.10/1.00  qbf_num_tautologies:                    0
% 1.10/1.00  qbf_prep_cycles:                        0
% 1.10/1.00  
% 1.10/1.00  ------ BMC1
% 1.10/1.00  
% 1.10/1.00  bmc1_current_bound:                     -1
% 1.10/1.00  bmc1_last_solved_bound:                 -1
% 1.10/1.00  bmc1_unsat_core_size:                   -1
% 1.10/1.00  bmc1_unsat_core_parents_size:           -1
% 1.10/1.00  bmc1_merge_next_fun:                    0
% 1.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.10/1.00  
% 1.10/1.00  ------ Instantiation
% 1.10/1.00  
% 1.10/1.00  inst_num_of_clauses:                    75
% 1.10/1.00  inst_num_in_passive:                    20
% 1.10/1.00  inst_num_in_active:                     47
% 1.10/1.00  inst_num_in_unprocessed:                8
% 1.10/1.00  inst_num_of_loops:                      60
% 1.10/1.00  inst_num_of_learning_restarts:          0
% 1.10/1.00  inst_num_moves_active_passive:          10
% 1.10/1.00  inst_lit_activity:                      0
% 1.10/1.00  inst_lit_activity_moves:                0
% 1.10/1.00  inst_num_tautologies:                   0
% 1.10/1.00  inst_num_prop_implied:                  0
% 1.10/1.00  inst_num_existing_simplified:           0
% 1.10/1.00  inst_num_eq_res_simplified:             0
% 1.10/1.00  inst_num_child_elim:                    0
% 1.10/1.00  inst_num_of_dismatching_blockings:      2
% 1.10/1.00  inst_num_of_non_proper_insts:           47
% 1.10/1.00  inst_num_of_duplicates:                 0
% 1.10/1.00  inst_inst_num_from_inst_to_res:         0
% 1.10/1.00  inst_dismatching_checking_time:         0.
% 1.10/1.00  
% 1.10/1.00  ------ Resolution
% 1.10/1.00  
% 1.10/1.00  res_num_of_clauses:                     0
% 1.10/1.00  res_num_in_passive:                     0
% 1.10/1.00  res_num_in_active:                      0
% 1.10/1.00  res_num_of_loops:                       60
% 1.10/1.00  res_forward_subset_subsumed:            7
% 1.10/1.00  res_backward_subset_subsumed:           0
% 1.10/1.00  res_forward_subsumed:                   0
% 1.10/1.00  res_backward_subsumed:                  0
% 1.10/1.00  res_forward_subsumption_resolution:     0
% 1.10/1.00  res_backward_subsumption_resolution:    0
% 1.10/1.00  res_clause_to_clause_subsumption:       12
% 1.10/1.00  res_orphan_elimination:                 0
% 1.10/1.00  res_tautology_del:                      8
% 1.10/1.00  res_num_eq_res_simplified:              0
% 1.10/1.00  res_num_sel_changes:                    0
% 1.10/1.00  res_moves_from_active_to_pass:          0
% 1.10/1.00  
% 1.10/1.00  ------ Superposition
% 1.10/1.00  
% 1.10/1.00  sup_time_total:                         0.
% 1.10/1.00  sup_time_generating:                    0.
% 1.10/1.00  sup_time_sim_full:                      0.
% 1.10/1.00  sup_time_sim_immed:                     0.
% 1.10/1.00  
% 1.10/1.00  sup_num_of_clauses:                     12
% 1.10/1.00  sup_num_in_active:                      10
% 1.10/1.00  sup_num_in_passive:                     2
% 1.10/1.00  sup_num_of_loops:                       10
% 1.10/1.00  sup_fw_superposition:                   5
% 1.10/1.00  sup_bw_superposition:                   4
% 1.10/1.00  sup_immediate_simplified:               2
% 1.10/1.00  sup_given_eliminated:                   0
% 1.10/1.00  comparisons_done:                       0
% 1.10/1.00  comparisons_avoided:                    0
% 1.10/1.00  
% 1.10/1.00  ------ Simplifications
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  sim_fw_subset_subsumed:                 1
% 1.10/1.00  sim_bw_subset_subsumed:                 0
% 1.10/1.00  sim_fw_subsumed:                        0
% 1.10/1.00  sim_bw_subsumed:                        0
% 1.10/1.00  sim_fw_subsumption_res:                 0
% 1.10/1.00  sim_bw_subsumption_res:                 0
% 1.10/1.00  sim_tautology_del:                      0
% 1.10/1.00  sim_eq_tautology_del:                   0
% 1.10/1.00  sim_eq_res_simp:                        0
% 1.10/1.00  sim_fw_demodulated:                     0
% 1.10/1.00  sim_bw_demodulated:                     1
% 1.10/1.00  sim_light_normalised:                   1
% 1.10/1.00  sim_joinable_taut:                      0
% 1.10/1.00  sim_joinable_simp:                      0
% 1.10/1.00  sim_ac_normalised:                      0
% 1.10/1.00  sim_smt_subsumption:                    0
% 1.10/1.00  
%------------------------------------------------------------------------------
