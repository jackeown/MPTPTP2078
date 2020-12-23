%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:17 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 142 expanded)
%              Number of clauses        :   31 (  47 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 267 expanded)
%              Number of equality atoms :   43 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
      & r1_tarski(sK1,sK3)
      & ~ r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
    & r1_tarski(sK1,sK3)
    & ~ r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).

fof(f28,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f27,f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f30,plain,(
    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f30,f27])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_131,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_132,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_261,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_112,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_113,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_602,plain,
    ( k4_xboole_0(sK1,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_113,c_7])).

cnf(c_3,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_698,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_602,c_3])).

cnf(c_971,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_698])).

cnf(c_692,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_602,c_3])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_106,plain,
    ( X0 != X1
    | k2_xboole_0(X2,k4_xboole_0(X0,X2)) = X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_107,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(unflattening,[status(thm)],[c_106])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_267,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_107,c_5])).

cnf(c_741,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_692,c_267])).

cnf(c_1117,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) = k4_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_971,c_741])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_138,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_139,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_260,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_966,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_698,c_260])).

cnf(c_1121,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1117,c_966])).

cnf(c_1156,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_261,c_1121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.82/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/0.96  
% 2.82/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.96  
% 2.82/0.96  ------  iProver source info
% 2.82/0.96  
% 2.82/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.96  git: non_committed_changes: false
% 2.82/0.96  git: last_make_outside_of_git: false
% 2.82/0.96  
% 2.82/0.96  ------ 
% 2.82/0.96  
% 2.82/0.96  ------ Input Options
% 2.82/0.96  
% 2.82/0.96  --out_options                           all
% 2.82/0.96  --tptp_safe_out                         true
% 2.82/0.96  --problem_path                          ""
% 2.82/0.96  --include_path                          ""
% 2.82/0.96  --clausifier                            res/vclausify_rel
% 2.82/0.96  --clausifier_options                    --mode clausify
% 2.82/0.96  --stdin                                 false
% 2.82/0.96  --stats_out                             all
% 2.82/0.96  
% 2.82/0.96  ------ General Options
% 2.82/0.96  
% 2.82/0.96  --fof                                   false
% 2.82/0.96  --time_out_real                         305.
% 2.82/0.96  --time_out_virtual                      -1.
% 2.82/0.96  --symbol_type_check                     false
% 2.82/0.96  --clausify_out                          false
% 2.82/0.96  --sig_cnt_out                           false
% 2.82/0.96  --trig_cnt_out                          false
% 2.82/0.96  --trig_cnt_out_tolerance                1.
% 2.82/0.96  --trig_cnt_out_sk_spl                   false
% 2.82/0.96  --abstr_cl_out                          false
% 2.82/0.96  
% 2.82/0.96  ------ Global Options
% 2.82/0.96  
% 2.82/0.96  --schedule                              default
% 2.82/0.96  --add_important_lit                     false
% 2.82/0.96  --prop_solver_per_cl                    1000
% 2.82/0.96  --min_unsat_core                        false
% 2.82/0.96  --soft_assumptions                      false
% 2.82/0.96  --soft_lemma_size                       3
% 2.82/0.96  --prop_impl_unit_size                   0
% 2.82/0.96  --prop_impl_unit                        []
% 2.82/0.96  --share_sel_clauses                     true
% 2.82/0.96  --reset_solvers                         false
% 2.82/0.96  --bc_imp_inh                            [conj_cone]
% 2.82/0.96  --conj_cone_tolerance                   3.
% 2.82/0.96  --extra_neg_conj                        none
% 2.82/0.96  --large_theory_mode                     true
% 2.82/0.96  --prolific_symb_bound                   200
% 2.82/0.96  --lt_threshold                          2000
% 2.82/0.96  --clause_weak_htbl                      true
% 2.82/0.96  --gc_record_bc_elim                     false
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing Options
% 2.82/0.96  
% 2.82/0.96  --preprocessing_flag                    true
% 2.82/0.96  --time_out_prep_mult                    0.1
% 2.82/0.96  --splitting_mode                        input
% 2.82/0.96  --splitting_grd                         true
% 2.82/0.96  --splitting_cvd                         false
% 2.82/0.96  --splitting_cvd_svl                     false
% 2.82/0.96  --splitting_nvd                         32
% 2.82/0.96  --sub_typing                            true
% 2.82/0.96  --prep_gs_sim                           true
% 2.82/0.96  --prep_unflatten                        true
% 2.82/0.96  --prep_res_sim                          true
% 2.82/0.96  --prep_upred                            true
% 2.82/0.96  --prep_sem_filter                       exhaustive
% 2.82/0.96  --prep_sem_filter_out                   false
% 2.82/0.96  --pred_elim                             true
% 2.82/0.96  --res_sim_input                         true
% 2.82/0.96  --eq_ax_congr_red                       true
% 2.82/0.96  --pure_diseq_elim                       true
% 2.82/0.96  --brand_transform                       false
% 2.82/0.96  --non_eq_to_eq                          false
% 2.82/0.96  --prep_def_merge                        true
% 2.82/0.96  --prep_def_merge_prop_impl              false
% 2.82/0.96  --prep_def_merge_mbd                    true
% 2.82/0.96  --prep_def_merge_tr_red                 false
% 2.82/0.96  --prep_def_merge_tr_cl                  false
% 2.82/0.96  --smt_preprocessing                     true
% 2.82/0.96  --smt_ac_axioms                         fast
% 2.82/0.96  --preprocessed_out                      false
% 2.82/0.96  --preprocessed_stats                    false
% 2.82/0.96  
% 2.82/0.96  ------ Abstraction refinement Options
% 2.82/0.96  
% 2.82/0.96  --abstr_ref                             []
% 2.82/0.96  --abstr_ref_prep                        false
% 2.82/0.96  --abstr_ref_until_sat                   false
% 2.82/0.96  --abstr_ref_sig_restrict                funpre
% 2.82/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.96  --abstr_ref_under                       []
% 2.82/0.96  
% 2.82/0.96  ------ SAT Options
% 2.82/0.96  
% 2.82/0.96  --sat_mode                              false
% 2.82/0.96  --sat_fm_restart_options                ""
% 2.82/0.96  --sat_gr_def                            false
% 2.82/0.96  --sat_epr_types                         true
% 2.82/0.96  --sat_non_cyclic_types                  false
% 2.82/0.96  --sat_finite_models                     false
% 2.82/0.96  --sat_fm_lemmas                         false
% 2.82/0.96  --sat_fm_prep                           false
% 2.82/0.96  --sat_fm_uc_incr                        true
% 2.82/0.96  --sat_out_model                         small
% 2.82/0.96  --sat_out_clauses                       false
% 2.82/0.96  
% 2.82/0.96  ------ QBF Options
% 2.82/0.96  
% 2.82/0.96  --qbf_mode                              false
% 2.82/0.96  --qbf_elim_univ                         false
% 2.82/0.96  --qbf_dom_inst                          none
% 2.82/0.96  --qbf_dom_pre_inst                      false
% 2.82/0.96  --qbf_sk_in                             false
% 2.82/0.96  --qbf_pred_elim                         true
% 2.82/0.96  --qbf_split                             512
% 2.82/0.96  
% 2.82/0.96  ------ BMC1 Options
% 2.82/0.96  
% 2.82/0.96  --bmc1_incremental                      false
% 2.82/0.96  --bmc1_axioms                           reachable_all
% 2.82/0.96  --bmc1_min_bound                        0
% 2.82/0.96  --bmc1_max_bound                        -1
% 2.82/0.96  --bmc1_max_bound_default                -1
% 2.82/0.96  --bmc1_symbol_reachability              true
% 2.82/0.96  --bmc1_property_lemmas                  false
% 2.82/0.96  --bmc1_k_induction                      false
% 2.82/0.96  --bmc1_non_equiv_states                 false
% 2.82/0.96  --bmc1_deadlock                         false
% 2.82/0.96  --bmc1_ucm                              false
% 2.82/0.96  --bmc1_add_unsat_core                   none
% 2.82/0.96  --bmc1_unsat_core_children              false
% 2.82/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.96  --bmc1_out_stat                         full
% 2.82/0.96  --bmc1_ground_init                      false
% 2.82/0.96  --bmc1_pre_inst_next_state              false
% 2.82/0.96  --bmc1_pre_inst_state                   false
% 2.82/0.96  --bmc1_pre_inst_reach_state             false
% 2.82/0.96  --bmc1_out_unsat_core                   false
% 2.82/0.96  --bmc1_aig_witness_out                  false
% 2.82/0.96  --bmc1_verbose                          false
% 2.82/0.96  --bmc1_dump_clauses_tptp                false
% 2.82/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.96  --bmc1_dump_file                        -
% 2.82/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.96  --bmc1_ucm_extend_mode                  1
% 2.82/0.96  --bmc1_ucm_init_mode                    2
% 2.82/0.96  --bmc1_ucm_cone_mode                    none
% 2.82/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.96  --bmc1_ucm_relax_model                  4
% 2.82/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.96  --bmc1_ucm_layered_model                none
% 2.82/0.96  --bmc1_ucm_max_lemma_size               10
% 2.82/0.96  
% 2.82/0.96  ------ AIG Options
% 2.82/0.96  
% 2.82/0.96  --aig_mode                              false
% 2.82/0.96  
% 2.82/0.96  ------ Instantiation Options
% 2.82/0.96  
% 2.82/0.96  --instantiation_flag                    true
% 2.82/0.96  --inst_sos_flag                         false
% 2.82/0.96  --inst_sos_phase                        true
% 2.82/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.96  --inst_lit_sel_side                     num_symb
% 2.82/0.96  --inst_solver_per_active                1400
% 2.82/0.96  --inst_solver_calls_frac                1.
% 2.82/0.96  --inst_passive_queue_type               priority_queues
% 2.82/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.96  --inst_passive_queues_freq              [25;2]
% 2.82/0.96  --inst_dismatching                      true
% 2.82/0.96  --inst_eager_unprocessed_to_passive     true
% 2.82/0.96  --inst_prop_sim_given                   true
% 2.82/0.96  --inst_prop_sim_new                     false
% 2.82/0.96  --inst_subs_new                         false
% 2.82/0.96  --inst_eq_res_simp                      false
% 2.82/0.96  --inst_subs_given                       false
% 2.82/0.96  --inst_orphan_elimination               true
% 2.82/0.96  --inst_learning_loop_flag               true
% 2.82/0.96  --inst_learning_start                   3000
% 2.82/0.96  --inst_learning_factor                  2
% 2.82/0.96  --inst_start_prop_sim_after_learn       3
% 2.82/0.96  --inst_sel_renew                        solver
% 2.82/0.96  --inst_lit_activity_flag                true
% 2.82/0.96  --inst_restr_to_given                   false
% 2.82/0.96  --inst_activity_threshold               500
% 2.82/0.96  --inst_out_proof                        true
% 2.82/0.96  
% 2.82/0.96  ------ Resolution Options
% 2.82/0.96  
% 2.82/0.96  --resolution_flag                       true
% 2.82/0.96  --res_lit_sel                           adaptive
% 2.82/0.96  --res_lit_sel_side                      none
% 2.82/0.96  --res_ordering                          kbo
% 2.82/0.96  --res_to_prop_solver                    active
% 2.82/0.96  --res_prop_simpl_new                    false
% 2.82/0.96  --res_prop_simpl_given                  true
% 2.82/0.96  --res_passive_queue_type                priority_queues
% 2.82/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.96  --res_passive_queues_freq               [15;5]
% 2.82/0.96  --res_forward_subs                      full
% 2.82/0.96  --res_backward_subs                     full
% 2.82/0.96  --res_forward_subs_resolution           true
% 2.82/0.96  --res_backward_subs_resolution          true
% 2.82/0.96  --res_orphan_elimination                true
% 2.82/0.96  --res_time_limit                        2.
% 2.82/0.96  --res_out_proof                         true
% 2.82/0.96  
% 2.82/0.96  ------ Superposition Options
% 2.82/0.96  
% 2.82/0.96  --superposition_flag                    true
% 2.82/0.96  --sup_passive_queue_type                priority_queues
% 2.82/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.96  --demod_completeness_check              fast
% 2.82/0.96  --demod_use_ground                      true
% 2.82/0.96  --sup_to_prop_solver                    passive
% 2.82/0.96  --sup_prop_simpl_new                    true
% 2.82/0.96  --sup_prop_simpl_given                  true
% 2.82/0.96  --sup_fun_splitting                     false
% 2.82/0.96  --sup_smt_interval                      50000
% 2.82/0.96  
% 2.82/0.96  ------ Superposition Simplification Setup
% 2.82/0.96  
% 2.82/0.96  --sup_indices_passive                   []
% 2.82/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_full_bw                           [BwDemod]
% 2.82/0.96  --sup_immed_triv                        [TrivRules]
% 2.82/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_immed_bw_main                     []
% 2.82/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.96  
% 2.82/0.96  ------ Combination Options
% 2.82/0.96  
% 2.82/0.96  --comb_res_mult                         3
% 2.82/0.96  --comb_sup_mult                         2
% 2.82/0.96  --comb_inst_mult                        10
% 2.82/0.96  
% 2.82/0.96  ------ Debug Options
% 2.82/0.96  
% 2.82/0.96  --dbg_backtrace                         false
% 2.82/0.96  --dbg_dump_prop_clauses                 false
% 2.82/0.96  --dbg_dump_prop_clauses_file            -
% 2.82/0.96  --dbg_out_stat                          false
% 2.82/0.96  ------ Parsing...
% 2.82/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.96  ------ Proving...
% 2.82/0.96  ------ Problem Properties 
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  clauses                                 10
% 2.82/0.96  conjectures                             0
% 2.82/0.96  EPR                                     0
% 2.82/0.96  Horn                                    10
% 2.82/0.96  unary                                   9
% 2.82/0.96  binary                                  1
% 2.82/0.96  lits                                    11
% 2.82/0.96  lits eq                                 7
% 2.82/0.96  fd_pure                                 0
% 2.82/0.96  fd_pseudo                               0
% 2.82/0.96  fd_cond                                 0
% 2.82/0.96  fd_pseudo_cond                          0
% 2.82/0.96  AC symbols                              0
% 2.82/0.96  
% 2.82/0.96  ------ Schedule dynamic 5 is on 
% 2.82/0.96  
% 2.82/0.96  ------ no conjectures: strip conj schedule 
% 2.82/0.96  
% 2.82/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  ------ 
% 2.82/0.96  Current options:
% 2.82/0.96  ------ 
% 2.82/0.96  
% 2.82/0.96  ------ Input Options
% 2.82/0.96  
% 2.82/0.96  --out_options                           all
% 2.82/0.96  --tptp_safe_out                         true
% 2.82/0.96  --problem_path                          ""
% 2.82/0.96  --include_path                          ""
% 2.82/0.96  --clausifier                            res/vclausify_rel
% 2.82/0.96  --clausifier_options                    --mode clausify
% 2.82/0.96  --stdin                                 false
% 2.82/0.96  --stats_out                             all
% 2.82/0.96  
% 2.82/0.96  ------ General Options
% 2.82/0.96  
% 2.82/0.96  --fof                                   false
% 2.82/0.96  --time_out_real                         305.
% 2.82/0.96  --time_out_virtual                      -1.
% 2.82/0.96  --symbol_type_check                     false
% 2.82/0.96  --clausify_out                          false
% 2.82/0.96  --sig_cnt_out                           false
% 2.82/0.96  --trig_cnt_out                          false
% 2.82/0.96  --trig_cnt_out_tolerance                1.
% 2.82/0.96  --trig_cnt_out_sk_spl                   false
% 2.82/0.96  --abstr_cl_out                          false
% 2.82/0.96  
% 2.82/0.96  ------ Global Options
% 2.82/0.96  
% 2.82/0.96  --schedule                              default
% 2.82/0.96  --add_important_lit                     false
% 2.82/0.96  --prop_solver_per_cl                    1000
% 2.82/0.96  --min_unsat_core                        false
% 2.82/0.96  --soft_assumptions                      false
% 2.82/0.96  --soft_lemma_size                       3
% 2.82/0.96  --prop_impl_unit_size                   0
% 2.82/0.96  --prop_impl_unit                        []
% 2.82/0.96  --share_sel_clauses                     true
% 2.82/0.96  --reset_solvers                         false
% 2.82/0.96  --bc_imp_inh                            [conj_cone]
% 2.82/0.96  --conj_cone_tolerance                   3.
% 2.82/0.96  --extra_neg_conj                        none
% 2.82/0.96  --large_theory_mode                     true
% 2.82/0.96  --prolific_symb_bound                   200
% 2.82/0.96  --lt_threshold                          2000
% 2.82/0.96  --clause_weak_htbl                      true
% 2.82/0.96  --gc_record_bc_elim                     false
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing Options
% 2.82/0.96  
% 2.82/0.96  --preprocessing_flag                    true
% 2.82/0.96  --time_out_prep_mult                    0.1
% 2.82/0.96  --splitting_mode                        input
% 2.82/0.96  --splitting_grd                         true
% 2.82/0.96  --splitting_cvd                         false
% 2.82/0.96  --splitting_cvd_svl                     false
% 2.82/0.96  --splitting_nvd                         32
% 2.82/0.96  --sub_typing                            true
% 2.82/0.96  --prep_gs_sim                           true
% 2.82/0.96  --prep_unflatten                        true
% 2.82/0.96  --prep_res_sim                          true
% 2.82/0.96  --prep_upred                            true
% 2.82/0.96  --prep_sem_filter                       exhaustive
% 2.82/0.96  --prep_sem_filter_out                   false
% 2.82/0.96  --pred_elim                             true
% 2.82/0.96  --res_sim_input                         true
% 2.82/0.96  --eq_ax_congr_red                       true
% 2.82/0.96  --pure_diseq_elim                       true
% 2.82/0.96  --brand_transform                       false
% 2.82/0.96  --non_eq_to_eq                          false
% 2.82/0.96  --prep_def_merge                        true
% 2.82/0.96  --prep_def_merge_prop_impl              false
% 2.82/0.96  --prep_def_merge_mbd                    true
% 2.82/0.96  --prep_def_merge_tr_red                 false
% 2.82/0.96  --prep_def_merge_tr_cl                  false
% 2.82/0.96  --smt_preprocessing                     true
% 2.82/0.96  --smt_ac_axioms                         fast
% 2.82/0.96  --preprocessed_out                      false
% 2.82/0.96  --preprocessed_stats                    false
% 2.82/0.96  
% 2.82/0.96  ------ Abstraction refinement Options
% 2.82/0.96  
% 2.82/0.96  --abstr_ref                             []
% 2.82/0.96  --abstr_ref_prep                        false
% 2.82/0.96  --abstr_ref_until_sat                   false
% 2.82/0.96  --abstr_ref_sig_restrict                funpre
% 2.82/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.96  --abstr_ref_under                       []
% 2.82/0.96  
% 2.82/0.96  ------ SAT Options
% 2.82/0.96  
% 2.82/0.96  --sat_mode                              false
% 2.82/0.96  --sat_fm_restart_options                ""
% 2.82/0.96  --sat_gr_def                            false
% 2.82/0.96  --sat_epr_types                         true
% 2.82/0.96  --sat_non_cyclic_types                  false
% 2.82/0.96  --sat_finite_models                     false
% 2.82/0.96  --sat_fm_lemmas                         false
% 2.82/0.96  --sat_fm_prep                           false
% 2.82/0.96  --sat_fm_uc_incr                        true
% 2.82/0.96  --sat_out_model                         small
% 2.82/0.96  --sat_out_clauses                       false
% 2.82/0.96  
% 2.82/0.96  ------ QBF Options
% 2.82/0.96  
% 2.82/0.96  --qbf_mode                              false
% 2.82/0.96  --qbf_elim_univ                         false
% 2.82/0.96  --qbf_dom_inst                          none
% 2.82/0.96  --qbf_dom_pre_inst                      false
% 2.82/0.96  --qbf_sk_in                             false
% 2.82/0.96  --qbf_pred_elim                         true
% 2.82/0.96  --qbf_split                             512
% 2.82/0.96  
% 2.82/0.96  ------ BMC1 Options
% 2.82/0.96  
% 2.82/0.96  --bmc1_incremental                      false
% 2.82/0.96  --bmc1_axioms                           reachable_all
% 2.82/0.96  --bmc1_min_bound                        0
% 2.82/0.96  --bmc1_max_bound                        -1
% 2.82/0.96  --bmc1_max_bound_default                -1
% 2.82/0.96  --bmc1_symbol_reachability              true
% 2.82/0.96  --bmc1_property_lemmas                  false
% 2.82/0.96  --bmc1_k_induction                      false
% 2.82/0.96  --bmc1_non_equiv_states                 false
% 2.82/0.96  --bmc1_deadlock                         false
% 2.82/0.96  --bmc1_ucm                              false
% 2.82/0.96  --bmc1_add_unsat_core                   none
% 2.82/0.96  --bmc1_unsat_core_children              false
% 2.82/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.96  --bmc1_out_stat                         full
% 2.82/0.96  --bmc1_ground_init                      false
% 2.82/0.96  --bmc1_pre_inst_next_state              false
% 2.82/0.96  --bmc1_pre_inst_state                   false
% 2.82/0.96  --bmc1_pre_inst_reach_state             false
% 2.82/0.96  --bmc1_out_unsat_core                   false
% 2.82/0.96  --bmc1_aig_witness_out                  false
% 2.82/0.96  --bmc1_verbose                          false
% 2.82/0.96  --bmc1_dump_clauses_tptp                false
% 2.82/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.96  --bmc1_dump_file                        -
% 2.82/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.96  --bmc1_ucm_extend_mode                  1
% 2.82/0.96  --bmc1_ucm_init_mode                    2
% 2.82/0.96  --bmc1_ucm_cone_mode                    none
% 2.82/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.96  --bmc1_ucm_relax_model                  4
% 2.82/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.96  --bmc1_ucm_layered_model                none
% 2.82/0.96  --bmc1_ucm_max_lemma_size               10
% 2.82/0.96  
% 2.82/0.96  ------ AIG Options
% 2.82/0.96  
% 2.82/0.96  --aig_mode                              false
% 2.82/0.96  
% 2.82/0.96  ------ Instantiation Options
% 2.82/0.96  
% 2.82/0.96  --instantiation_flag                    true
% 2.82/0.96  --inst_sos_flag                         false
% 2.82/0.96  --inst_sos_phase                        true
% 2.82/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.96  --inst_lit_sel_side                     none
% 2.82/0.96  --inst_solver_per_active                1400
% 2.82/0.96  --inst_solver_calls_frac                1.
% 2.82/0.96  --inst_passive_queue_type               priority_queues
% 2.82/0.96  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.82/0.96  --inst_passive_queues_freq              [25;2]
% 2.82/0.96  --inst_dismatching                      true
% 2.82/0.96  --inst_eager_unprocessed_to_passive     true
% 2.82/0.96  --inst_prop_sim_given                   true
% 2.82/0.96  --inst_prop_sim_new                     false
% 2.82/0.96  --inst_subs_new                         false
% 2.82/0.96  --inst_eq_res_simp                      false
% 2.82/0.96  --inst_subs_given                       false
% 2.82/0.96  --inst_orphan_elimination               true
% 2.82/0.96  --inst_learning_loop_flag               true
% 2.82/0.96  --inst_learning_start                   3000
% 2.82/0.96  --inst_learning_factor                  2
% 2.82/0.96  --inst_start_prop_sim_after_learn       3
% 2.82/0.96  --inst_sel_renew                        solver
% 2.82/0.96  --inst_lit_activity_flag                true
% 2.82/0.96  --inst_restr_to_given                   false
% 2.82/0.96  --inst_activity_threshold               500
% 2.82/0.96  --inst_out_proof                        true
% 2.82/0.96  
% 2.82/0.96  ------ Resolution Options
% 2.82/0.96  
% 2.82/0.96  --resolution_flag                       false
% 2.82/0.96  --res_lit_sel                           adaptive
% 2.82/0.96  --res_lit_sel_side                      none
% 2.82/0.96  --res_ordering                          kbo
% 2.82/0.96  --res_to_prop_solver                    active
% 2.82/0.96  --res_prop_simpl_new                    false
% 2.82/0.96  --res_prop_simpl_given                  true
% 2.82/0.96  --res_passive_queue_type                priority_queues
% 2.82/0.96  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.82/0.96  --res_passive_queues_freq               [15;5]
% 2.82/0.96  --res_forward_subs                      full
% 2.82/0.96  --res_backward_subs                     full
% 2.82/0.96  --res_forward_subs_resolution           true
% 2.82/0.96  --res_backward_subs_resolution          true
% 2.82/0.96  --res_orphan_elimination                true
% 2.82/0.96  --res_time_limit                        2.
% 2.82/0.96  --res_out_proof                         true
% 2.82/0.96  
% 2.82/0.96  ------ Superposition Options
% 2.82/0.96  
% 2.82/0.96  --superposition_flag                    true
% 2.82/0.96  --sup_passive_queue_type                priority_queues
% 2.82/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.96  --demod_completeness_check              fast
% 2.82/0.96  --demod_use_ground                      true
% 2.82/0.96  --sup_to_prop_solver                    passive
% 2.82/0.96  --sup_prop_simpl_new                    true
% 2.82/0.96  --sup_prop_simpl_given                  true
% 2.82/0.96  --sup_fun_splitting                     false
% 2.82/0.96  --sup_smt_interval                      50000
% 2.82/0.96  
% 2.82/0.96  ------ Superposition Simplification Setup
% 2.82/0.96  
% 2.82/0.96  --sup_indices_passive                   []
% 2.82/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_full_bw                           [BwDemod]
% 2.82/0.96  --sup_immed_triv                        [TrivRules]
% 2.82/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_immed_bw_main                     []
% 2.82/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.96  
% 2.82/0.96  ------ Combination Options
% 2.82/0.96  
% 2.82/0.96  --comb_res_mult                         3
% 2.82/0.96  --comb_sup_mult                         2
% 2.82/0.96  --comb_inst_mult                        10
% 2.82/0.96  
% 2.82/0.96  ------ Debug Options
% 2.82/0.96  
% 2.82/0.96  --dbg_backtrace                         false
% 2.82/0.96  --dbg_dump_prop_clauses                 false
% 2.82/0.96  --dbg_dump_prop_clauses_file            -
% 2.82/0.96  --dbg_out_stat                          false
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  ------ Proving...
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  % SZS status Theorem for theBenchmark.p
% 2.82/0.96  
% 2.82/0.96   Resolution empty clause
% 2.82/0.96  
% 2.82/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/0.96  
% 2.82/0.96  fof(f2,axiom,(
% 2.82/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f11,plain,(
% 2.82/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.82/0.96    inference(rectify,[],[f2])).
% 2.82/0.96  
% 2.82/0.96  fof(f12,plain,(
% 2.82/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.82/0.96    inference(ennf_transformation,[],[f11])).
% 2.82/0.96  
% 2.82/0.96  fof(f15,plain,(
% 2.82/0.96    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.82/0.96    introduced(choice_axiom,[])).
% 2.82/0.96  
% 2.82/0.96  fof(f16,plain,(
% 2.82/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.82/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).
% 2.82/0.96  
% 2.82/0.96  fof(f20,plain,(
% 2.82/0.96    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.82/0.96    inference(cnf_transformation,[],[f16])).
% 2.82/0.96  
% 2.82/0.96  fof(f8,axiom,(
% 2.82/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f27,plain,(
% 2.82/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.82/0.96    inference(cnf_transformation,[],[f8])).
% 2.82/0.96  
% 2.82/0.96  fof(f33,plain,(
% 2.82/0.96    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.82/0.96    inference(definition_unfolding,[],[f20,f27])).
% 2.82/0.96  
% 2.82/0.96  fof(f9,conjecture,(
% 2.82/0.96    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f10,negated_conjecture,(
% 2.82/0.96    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.82/0.96    inference(negated_conjecture,[],[f9])).
% 2.82/0.96  
% 2.82/0.96  fof(f14,plain,(
% 2.82/0.96    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.82/0.96    inference(ennf_transformation,[],[f10])).
% 2.82/0.96  
% 2.82/0.96  fof(f17,plain,(
% 2.82/0.96    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2))),
% 2.82/0.96    introduced(choice_axiom,[])).
% 2.82/0.96  
% 2.82/0.96  fof(f18,plain,(
% 2.82/0.96    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2)),
% 2.82/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).
% 2.82/0.96  
% 2.82/0.96  fof(f28,plain,(
% 2.82/0.96    ~r1_xboole_0(sK1,sK2)),
% 2.82/0.96    inference(cnf_transformation,[],[f18])).
% 2.82/0.96  
% 2.82/0.96  fof(f1,axiom,(
% 2.82/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f19,plain,(
% 2.82/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.82/0.96    inference(cnf_transformation,[],[f1])).
% 2.82/0.96  
% 2.82/0.96  fof(f31,plain,(
% 2.82/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.82/0.96    inference(definition_unfolding,[],[f19,f27,f27])).
% 2.82/0.96  
% 2.82/0.96  fof(f6,axiom,(
% 2.82/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f13,plain,(
% 2.82/0.96    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.82/0.96    inference(ennf_transformation,[],[f6])).
% 2.82/0.96  
% 2.82/0.96  fof(f25,plain,(
% 2.82/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.82/0.96    inference(cnf_transformation,[],[f13])).
% 2.82/0.96  
% 2.82/0.96  fof(f29,plain,(
% 2.82/0.96    r1_tarski(sK1,sK3)),
% 2.82/0.96    inference(cnf_transformation,[],[f18])).
% 2.82/0.96  
% 2.82/0.96  fof(f7,axiom,(
% 2.82/0.96    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f26,plain,(
% 2.82/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.82/0.96    inference(cnf_transformation,[],[f7])).
% 2.82/0.96  
% 2.82/0.96  fof(f3,axiom,(
% 2.82/0.96    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f22,plain,(
% 2.82/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.82/0.96    inference(cnf_transformation,[],[f3])).
% 2.82/0.96  
% 2.82/0.96  fof(f34,plain,(
% 2.82/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.82/0.96    inference(definition_unfolding,[],[f22,f27])).
% 2.82/0.96  
% 2.82/0.96  fof(f4,axiom,(
% 2.82/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f23,plain,(
% 2.82/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.82/0.96    inference(cnf_transformation,[],[f4])).
% 2.82/0.96  
% 2.82/0.96  fof(f5,axiom,(
% 2.82/0.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.82/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.96  
% 2.82/0.96  fof(f24,plain,(
% 2.82/0.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.82/0.96    inference(cnf_transformation,[],[f5])).
% 2.82/0.96  
% 2.82/0.96  fof(f21,plain,(
% 2.82/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.82/0.96    inference(cnf_transformation,[],[f16])).
% 2.82/0.96  
% 2.82/0.96  fof(f32,plain,(
% 2.82/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.82/0.96    inference(definition_unfolding,[],[f21,f27])).
% 2.82/0.96  
% 2.82/0.96  fof(f30,plain,(
% 2.82/0.96    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))),
% 2.82/0.96    inference(cnf_transformation,[],[f18])).
% 2.82/0.96  
% 2.82/0.96  fof(f35,plain,(
% 2.82/0.96    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 2.82/0.96    inference(definition_unfolding,[],[f30,f27])).
% 2.82/0.96  
% 2.82/0.96  cnf(c_2,plain,
% 2.82/0.96      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 2.82/0.96      | r1_xboole_0(X0,X1) ),
% 2.82/0.96      inference(cnf_transformation,[],[f33]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_10,negated_conjecture,
% 2.82/0.96      ( ~ r1_xboole_0(sK1,sK2) ),
% 2.82/0.96      inference(cnf_transformation,[],[f28]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_131,plain,
% 2.82/0.96      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 2.82/0.96      | sK2 != X1
% 2.82/0.96      | sK1 != X0 ),
% 2.82/0.96      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_132,plain,
% 2.82/0.96      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 2.82/0.96      inference(unflattening,[status(thm)],[c_131]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_261,plain,
% 2.82/0.96      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 2.82/0.96      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_0,plain,
% 2.82/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.82/0.96      inference(cnf_transformation,[],[f31]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_6,plain,
% 2.82/0.96      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 2.82/0.96      inference(cnf_transformation,[],[f25]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_9,negated_conjecture,
% 2.82/0.96      ( r1_tarski(sK1,sK3) ),
% 2.82/0.96      inference(cnf_transformation,[],[f29]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_112,plain,
% 2.82/0.96      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | sK3 != X1 | sK1 != X0 ),
% 2.82/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_113,plain,
% 2.82/0.96      ( k2_xboole_0(sK1,k4_xboole_0(sK3,sK1)) = sK3 ),
% 2.82/0.96      inference(unflattening,[status(thm)],[c_112]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_7,plain,
% 2.82/0.96      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.82/0.96      inference(cnf_transformation,[],[f26]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_602,plain,
% 2.82/0.96      ( k4_xboole_0(sK1,sK3) = k1_xboole_0 ),
% 2.82/0.96      inference(superposition,[status(thm)],[c_113,c_7]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_3,plain,
% 2.82/0.96      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 2.82/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_698,plain,
% 2.82/0.96      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
% 2.82/0.96      inference(superposition,[status(thm)],[c_602,c_3]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_971,plain,
% 2.82/0.96      ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
% 2.82/0.96      inference(superposition,[status(thm)],[c_0,c_698]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_692,plain,
% 2.82/0.96      ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X0)) ),
% 2.82/0.96      inference(superposition,[status(thm)],[c_602,c_3]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_4,plain,
% 2.82/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 2.82/0.96      inference(cnf_transformation,[],[f23]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_106,plain,
% 2.82/0.96      ( X0 != X1
% 2.82/0.96      | k2_xboole_0(X2,k4_xboole_0(X0,X2)) = X0
% 2.82/0.96      | k1_xboole_0 != X2 ),
% 2.82/0.96      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_107,plain,
% 2.82/0.96      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.82/0.96      inference(unflattening,[status(thm)],[c_106]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_5,plain,
% 2.82/0.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.82/0.96      inference(cnf_transformation,[],[f24]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_267,plain,
% 2.82/0.96      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.82/0.96      inference(light_normalisation,[status(thm)],[c_107,c_5]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_741,plain,
% 2.82/0.96      ( k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK1,X0) ),
% 2.82/0.96      inference(demodulation,[status(thm)],[c_692,c_267]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_1117,plain,
% 2.82/0.96      ( k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) = k4_xboole_0(sK1,X0) ),
% 2.82/0.96      inference(light_normalisation,[status(thm)],[c_971,c_741]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_1,plain,
% 2.82/0.96      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.82/0.96      | ~ r1_xboole_0(X1,X2) ),
% 2.82/0.96      inference(cnf_transformation,[],[f32]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_8,negated_conjecture,
% 2.82/0.96      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 2.82/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_138,plain,
% 2.82/0.96      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.82/0.96      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2
% 2.82/0.96      | sK1 != X1 ),
% 2.82/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_139,plain,
% 2.82/0.96      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ),
% 2.82/0.96      inference(unflattening,[status(thm)],[c_138]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_260,plain,
% 2.82/0.96      ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) != iProver_top ),
% 2.82/0.96      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_966,plain,
% 2.82/0.96      ( r2_hidden(X0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) != iProver_top ),
% 2.82/0.96      inference(demodulation,[status(thm)],[c_698,c_260]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_1121,plain,
% 2.82/0.96      ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 2.82/0.96      inference(demodulation,[status(thm)],[c_1117,c_966]) ).
% 2.82/0.96  
% 2.82/0.96  cnf(c_1156,plain,
% 2.82/0.96      ( $false ),
% 2.82/0.96      inference(superposition,[status(thm)],[c_261,c_1121]) ).
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/0.96  
% 2.82/0.96  ------                               Statistics
% 2.82/0.96  
% 2.82/0.96  ------ General
% 2.82/0.96  
% 2.82/0.96  abstr_ref_over_cycles:                  0
% 2.82/0.96  abstr_ref_under_cycles:                 0
% 2.82/0.96  gc_basic_clause_elim:                   0
% 2.82/0.96  forced_gc_time:                         0
% 2.82/0.96  parsing_time:                           0.008
% 2.82/0.96  unif_index_cands_time:                  0.
% 2.82/0.96  unif_index_add_time:                    0.
% 2.82/0.96  orderings_time:                         0.
% 2.82/0.96  out_proof_time:                         0.007
% 2.82/0.96  total_time:                             0.074
% 2.82/0.96  num_of_symbols:                         41
% 2.82/0.96  num_of_terms:                           1679
% 2.82/0.96  
% 2.82/0.96  ------ Preprocessing
% 2.82/0.96  
% 2.82/0.96  num_of_splits:                          0
% 2.82/0.96  num_of_split_atoms:                     0
% 2.82/0.96  num_of_reused_defs:                     0
% 2.82/0.96  num_eq_ax_congr_red:                    2
% 2.82/0.96  num_of_sem_filtered_clauses:            1
% 2.82/0.96  num_of_subtypes:                        0
% 2.82/0.96  monotx_restored_types:                  0
% 2.82/0.96  sat_num_of_epr_types:                   0
% 2.82/0.96  sat_num_of_non_cyclic_types:            0
% 2.82/0.96  sat_guarded_non_collapsed_types:        0
% 2.82/0.96  num_pure_diseq_elim:                    0
% 2.82/0.96  simp_replaced_by:                       0
% 2.82/0.96  res_preprocessed:                       54
% 2.82/0.96  prep_upred:                             0
% 2.82/0.96  prep_unflattend:                        11
% 2.82/0.96  smt_new_axioms:                         0
% 2.82/0.96  pred_elim_cands:                        1
% 2.82/0.96  pred_elim:                              2
% 2.82/0.96  pred_elim_cl:                           1
% 2.82/0.96  pred_elim_cycles:                       5
% 2.82/0.96  merged_defs:                            0
% 2.82/0.96  merged_defs_ncl:                        0
% 2.82/0.96  bin_hyper_res:                          0
% 2.82/0.96  prep_cycles:                            4
% 2.82/0.96  pred_elim_time:                         0.001
% 2.82/0.96  splitting_time:                         0.
% 2.82/0.96  sem_filter_time:                        0.
% 2.82/0.96  monotx_time:                            0.
% 2.82/0.96  subtype_inf_time:                       0.
% 2.82/0.96  
% 2.82/0.96  ------ Problem properties
% 2.82/0.96  
% 2.82/0.96  clauses:                                10
% 2.82/0.96  conjectures:                            0
% 2.82/0.96  epr:                                    0
% 2.82/0.96  horn:                                   10
% 2.82/0.96  ground:                                 3
% 2.82/0.96  unary:                                  9
% 2.82/0.96  binary:                                 1
% 2.82/0.96  lits:                                   11
% 2.82/0.96  lits_eq:                                7
% 2.82/0.96  fd_pure:                                0
% 2.82/0.96  fd_pseudo:                              0
% 2.82/0.96  fd_cond:                                0
% 2.82/0.96  fd_pseudo_cond:                         0
% 2.82/0.96  ac_symbols:                             0
% 2.82/0.96  
% 2.82/0.96  ------ Propositional Solver
% 2.82/0.96  
% 2.82/0.96  prop_solver_calls:                      26
% 2.82/0.96  prop_fast_solver_calls:                 195
% 2.82/0.96  smt_solver_calls:                       0
% 2.82/0.96  smt_fast_solver_calls:                  0
% 2.82/0.96  prop_num_of_clauses:                    456
% 2.82/0.96  prop_preprocess_simplified:             1537
% 2.82/0.96  prop_fo_subsumed:                       0
% 2.82/0.96  prop_solver_time:                       0.
% 2.82/0.96  smt_solver_time:                        0.
% 2.82/0.96  smt_fast_solver_time:                   0.
% 2.82/0.96  prop_fast_solver_time:                  0.
% 2.82/0.96  prop_unsat_core_time:                   0.
% 2.82/0.96  
% 2.82/0.96  ------ QBF
% 2.82/0.96  
% 2.82/0.96  qbf_q_res:                              0
% 2.82/0.96  qbf_num_tautologies:                    0
% 2.82/0.96  qbf_prep_cycles:                        0
% 2.82/0.96  
% 2.82/0.96  ------ BMC1
% 2.82/0.96  
% 2.82/0.96  bmc1_current_bound:                     -1
% 2.82/0.96  bmc1_last_solved_bound:                 -1
% 2.82/0.96  bmc1_unsat_core_size:                   -1
% 2.82/0.96  bmc1_unsat_core_parents_size:           -1
% 2.82/0.96  bmc1_merge_next_fun:                    0
% 2.82/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.82/0.96  
% 2.82/0.96  ------ Instantiation
% 2.82/0.96  
% 2.82/0.96  inst_num_of_clauses:                    159
% 2.82/0.96  inst_num_in_passive:                    56
% 2.82/0.96  inst_num_in_active:                     86
% 2.82/0.96  inst_num_in_unprocessed:                17
% 2.82/0.96  inst_num_of_loops:                      90
% 2.82/0.96  inst_num_of_learning_restarts:          0
% 2.82/0.96  inst_num_moves_active_passive:          2
% 2.82/0.96  inst_lit_activity:                      0
% 2.82/0.96  inst_lit_activity_moves:                0
% 2.82/0.96  inst_num_tautologies:                   0
% 2.82/0.96  inst_num_prop_implied:                  0
% 2.82/0.96  inst_num_existing_simplified:           0
% 2.82/0.96  inst_num_eq_res_simplified:             0
% 2.82/0.96  inst_num_child_elim:                    0
% 2.82/0.96  inst_num_of_dismatching_blockings:      21
% 2.82/0.96  inst_num_of_non_proper_insts:           127
% 2.82/0.96  inst_num_of_duplicates:                 0
% 2.82/0.96  inst_inst_num_from_inst_to_res:         0
% 2.82/0.96  inst_dismatching_checking_time:         0.
% 2.82/0.96  
% 2.82/0.96  ------ Resolution
% 2.82/0.96  
% 2.82/0.96  res_num_of_clauses:                     0
% 2.82/0.96  res_num_in_passive:                     0
% 2.82/0.96  res_num_in_active:                      0
% 2.82/0.96  res_num_of_loops:                       58
% 2.82/0.96  res_forward_subset_subsumed:            11
% 2.82/0.96  res_backward_subset_subsumed:           0
% 2.82/0.96  res_forward_subsumed:                   0
% 2.82/0.96  res_backward_subsumed:                  0
% 2.82/0.96  res_forward_subsumption_resolution:     0
% 2.82/0.96  res_backward_subsumption_resolution:    0
% 2.82/0.96  res_clause_to_clause_subsumption:       115
% 2.82/0.96  res_orphan_elimination:                 0
% 2.82/0.96  res_tautology_del:                      18
% 2.82/0.96  res_num_eq_res_simplified:              1
% 2.82/0.96  res_num_sel_changes:                    0
% 2.82/0.96  res_moves_from_active_to_pass:          0
% 2.82/0.96  
% 2.82/0.96  ------ Superposition
% 2.82/0.96  
% 2.82/0.96  sup_time_total:                         0.
% 2.82/0.96  sup_time_generating:                    0.
% 2.82/0.96  sup_time_sim_full:                      0.
% 2.82/0.96  sup_time_sim_immed:                     0.
% 2.82/0.96  
% 2.82/0.96  sup_num_of_clauses:                     41
% 2.82/0.96  sup_num_in_active:                      15
% 2.82/0.96  sup_num_in_passive:                     26
% 2.82/0.96  sup_num_of_loops:                       17
% 2.82/0.96  sup_fw_superposition:                   48
% 2.82/0.96  sup_bw_superposition:                   22
% 2.82/0.96  sup_immediate_simplified:               27
% 2.82/0.96  sup_given_eliminated:                   0
% 2.82/0.96  comparisons_done:                       0
% 2.82/0.96  comparisons_avoided:                    0
% 2.82/0.96  
% 2.82/0.96  ------ Simplifications
% 2.82/0.96  
% 2.82/0.96  
% 2.82/0.96  sim_fw_subset_subsumed:                 0
% 2.82/0.96  sim_bw_subset_subsumed:                 0
% 2.82/0.96  sim_fw_subsumed:                        3
% 2.82/0.96  sim_bw_subsumed:                        0
% 2.82/0.96  sim_fw_subsumption_res:                 0
% 2.82/0.96  sim_bw_subsumption_res:                 0
% 2.82/0.96  sim_tautology_del:                      0
% 2.82/0.96  sim_eq_tautology_del:                   7
% 2.82/0.96  sim_eq_res_simp:                        0
% 2.82/0.96  sim_fw_demodulated:                     19
% 2.82/0.96  sim_bw_demodulated:                     3
% 2.82/0.96  sim_light_normalised:                   13
% 2.82/0.96  sim_joinable_taut:                      0
% 2.82/0.96  sim_joinable_simp:                      0
% 2.82/0.96  sim_ac_normalised:                      0
% 2.82/0.96  sim_smt_subsumption:                    0
% 2.82/0.96  
%------------------------------------------------------------------------------
