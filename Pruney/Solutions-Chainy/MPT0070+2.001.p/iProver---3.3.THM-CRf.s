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
% DateTime   : Thu Dec  3 11:23:14 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 182 expanded)
%              Number of clauses        :   39 (  69 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 278 expanded)
%              Number of equality atoms :   59 ( 152 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f32,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_290,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_294,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_866,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_290,c_294])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_651,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_41006,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_866,c_651])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_653,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_41795,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_41006,c_8,c_653])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_291,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_295,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1114,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_291,c_295])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_293,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_794,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_293])).

cnf(c_1231,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_794])).

cnf(c_41056,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_1231])).

cnf(c_41650,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41056,c_8])).

cnf(c_46928,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_41650])).

cnf(c_47380,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k2_xboole_0(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_46928,c_8,c_653])).

cnf(c_47965,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_47380])).

cnf(c_48685,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41795,c_47965])).

cnf(c_660,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_42963,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_41795,c_660])).

cnf(c_43036,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_42963,c_7])).

cnf(c_48693,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48685,c_43036])).

cnf(c_355,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1205,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_1207,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | r1_tarski(sK0,k4_xboole_0(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_846,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48693,c_1207,c_846,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 11:40:57 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 11.55/1.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/1.95  
% 11.55/1.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.55/1.95  
% 11.55/1.95  ------  iProver source info
% 11.55/1.95  
% 11.55/1.95  git: date: 2020-06-30 10:37:57 +0100
% 11.55/1.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.55/1.95  git: non_committed_changes: false
% 11.55/1.95  git: last_make_outside_of_git: false
% 11.55/1.95  
% 11.55/1.95  ------ 
% 11.55/1.95  
% 11.55/1.95  ------ Input Options
% 11.55/1.95  
% 11.55/1.95  --out_options                           all
% 11.55/1.95  --tptp_safe_out                         true
% 11.55/1.95  --problem_path                          ""
% 11.55/1.95  --include_path                          ""
% 11.55/1.95  --clausifier                            res/vclausify_rel
% 11.55/1.95  --clausifier_options                    --mode clausify
% 11.55/1.95  --stdin                                 false
% 11.55/1.95  --stats_out                             sel
% 11.55/1.95  
% 11.55/1.95  ------ General Options
% 11.55/1.95  
% 11.55/1.95  --fof                                   false
% 11.55/1.95  --time_out_real                         604.99
% 11.55/1.95  --time_out_virtual                      -1.
% 11.55/1.95  --symbol_type_check                     false
% 11.55/1.95  --clausify_out                          false
% 11.55/1.95  --sig_cnt_out                           false
% 11.55/1.95  --trig_cnt_out                          false
% 11.55/1.95  --trig_cnt_out_tolerance                1.
% 11.55/1.95  --trig_cnt_out_sk_spl                   false
% 11.55/1.95  --abstr_cl_out                          false
% 11.55/1.95  
% 11.55/1.95  ------ Global Options
% 11.55/1.95  
% 11.55/1.95  --schedule                              none
% 11.55/1.95  --add_important_lit                     false
% 11.55/1.95  --prop_solver_per_cl                    1000
% 11.55/1.95  --min_unsat_core                        false
% 11.55/1.95  --soft_assumptions                      false
% 11.55/1.95  --soft_lemma_size                       3
% 11.55/1.95  --prop_impl_unit_size                   0
% 11.55/1.95  --prop_impl_unit                        []
% 11.55/1.95  --share_sel_clauses                     true
% 11.55/1.95  --reset_solvers                         false
% 11.55/1.95  --bc_imp_inh                            [conj_cone]
% 11.55/1.95  --conj_cone_tolerance                   3.
% 11.55/1.95  --extra_neg_conj                        none
% 11.55/1.95  --large_theory_mode                     true
% 11.55/1.95  --prolific_symb_bound                   200
% 11.55/1.95  --lt_threshold                          2000
% 11.55/1.95  --clause_weak_htbl                      true
% 11.55/1.95  --gc_record_bc_elim                     false
% 11.55/1.95  
% 11.55/1.95  ------ Preprocessing Options
% 11.55/1.95  
% 11.55/1.95  --preprocessing_flag                    true
% 11.55/1.95  --time_out_prep_mult                    0.1
% 11.55/1.95  --splitting_mode                        input
% 11.55/1.95  --splitting_grd                         true
% 11.55/1.95  --splitting_cvd                         false
% 11.55/1.95  --splitting_cvd_svl                     false
% 11.55/1.95  --splitting_nvd                         32
% 11.55/1.95  --sub_typing                            true
% 11.55/1.95  --prep_gs_sim                           false
% 11.55/1.95  --prep_unflatten                        true
% 11.55/1.95  --prep_res_sim                          true
% 11.55/1.95  --prep_upred                            true
% 11.55/1.95  --prep_sem_filter                       exhaustive
% 11.55/1.95  --prep_sem_filter_out                   false
% 11.55/1.95  --pred_elim                             false
% 11.55/1.95  --res_sim_input                         true
% 11.55/1.95  --eq_ax_congr_red                       true
% 11.55/1.95  --pure_diseq_elim                       true
% 11.55/1.95  --brand_transform                       false
% 11.55/1.95  --non_eq_to_eq                          false
% 11.55/1.95  --prep_def_merge                        true
% 11.55/1.95  --prep_def_merge_prop_impl              false
% 11.55/1.95  --prep_def_merge_mbd                    true
% 11.55/1.95  --prep_def_merge_tr_red                 false
% 11.55/1.95  --prep_def_merge_tr_cl                  false
% 11.55/1.95  --smt_preprocessing                     true
% 11.55/1.95  --smt_ac_axioms                         fast
% 11.55/1.95  --preprocessed_out                      false
% 11.55/1.95  --preprocessed_stats                    false
% 11.55/1.95  
% 11.55/1.95  ------ Abstraction refinement Options
% 11.55/1.95  
% 11.55/1.95  --abstr_ref                             []
% 11.55/1.95  --abstr_ref_prep                        false
% 11.55/1.95  --abstr_ref_until_sat                   false
% 11.55/1.95  --abstr_ref_sig_restrict                funpre
% 11.55/1.95  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/1.95  --abstr_ref_under                       []
% 11.55/1.95  
% 11.55/1.95  ------ SAT Options
% 11.55/1.95  
% 11.55/1.95  --sat_mode                              false
% 11.55/1.95  --sat_fm_restart_options                ""
% 11.55/1.95  --sat_gr_def                            false
% 11.55/1.95  --sat_epr_types                         true
% 11.55/1.95  --sat_non_cyclic_types                  false
% 11.55/1.95  --sat_finite_models                     false
% 11.55/1.95  --sat_fm_lemmas                         false
% 11.55/1.95  --sat_fm_prep                           false
% 11.55/1.95  --sat_fm_uc_incr                        true
% 11.55/1.95  --sat_out_model                         small
% 11.55/1.95  --sat_out_clauses                       false
% 11.55/1.95  
% 11.55/1.95  ------ QBF Options
% 11.55/1.95  
% 11.55/1.95  --qbf_mode                              false
% 11.55/1.95  --qbf_elim_univ                         false
% 11.55/1.95  --qbf_dom_inst                          none
% 11.55/1.95  --qbf_dom_pre_inst                      false
% 11.55/1.95  --qbf_sk_in                             false
% 11.55/1.95  --qbf_pred_elim                         true
% 11.55/1.95  --qbf_split                             512
% 11.55/1.95  
% 11.55/1.95  ------ BMC1 Options
% 11.55/1.95  
% 11.55/1.95  --bmc1_incremental                      false
% 11.55/1.95  --bmc1_axioms                           reachable_all
% 11.55/1.95  --bmc1_min_bound                        0
% 11.55/1.95  --bmc1_max_bound                        -1
% 11.55/1.95  --bmc1_max_bound_default                -1
% 11.55/1.95  --bmc1_symbol_reachability              true
% 11.55/1.95  --bmc1_property_lemmas                  false
% 11.55/1.95  --bmc1_k_induction                      false
% 11.55/1.95  --bmc1_non_equiv_states                 false
% 11.55/1.95  --bmc1_deadlock                         false
% 11.55/1.95  --bmc1_ucm                              false
% 11.55/1.95  --bmc1_add_unsat_core                   none
% 11.55/1.95  --bmc1_unsat_core_children              false
% 11.55/1.95  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/1.95  --bmc1_out_stat                         full
% 11.55/1.95  --bmc1_ground_init                      false
% 11.55/1.95  --bmc1_pre_inst_next_state              false
% 11.55/1.95  --bmc1_pre_inst_state                   false
% 11.55/1.95  --bmc1_pre_inst_reach_state             false
% 11.55/1.95  --bmc1_out_unsat_core                   false
% 11.55/1.95  --bmc1_aig_witness_out                  false
% 11.55/1.95  --bmc1_verbose                          false
% 11.55/1.95  --bmc1_dump_clauses_tptp                false
% 11.55/1.95  --bmc1_dump_unsat_core_tptp             false
% 11.55/1.95  --bmc1_dump_file                        -
% 11.55/1.95  --bmc1_ucm_expand_uc_limit              128
% 11.55/1.95  --bmc1_ucm_n_expand_iterations          6
% 11.55/1.95  --bmc1_ucm_extend_mode                  1
% 11.55/1.95  --bmc1_ucm_init_mode                    2
% 11.55/1.95  --bmc1_ucm_cone_mode                    none
% 11.55/1.95  --bmc1_ucm_reduced_relation_type        0
% 11.55/1.95  --bmc1_ucm_relax_model                  4
% 11.55/1.95  --bmc1_ucm_full_tr_after_sat            true
% 11.55/1.95  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/1.95  --bmc1_ucm_layered_model                none
% 11.55/1.95  --bmc1_ucm_max_lemma_size               10
% 11.55/1.95  
% 11.55/1.95  ------ AIG Options
% 11.55/1.95  
% 11.55/1.95  --aig_mode                              false
% 11.55/1.95  
% 11.55/1.95  ------ Instantiation Options
% 11.55/1.95  
% 11.55/1.95  --instantiation_flag                    true
% 11.55/1.95  --inst_sos_flag                         false
% 11.55/1.95  --inst_sos_phase                        true
% 11.55/1.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/1.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/1.95  --inst_lit_sel_side                     num_symb
% 11.55/1.95  --inst_solver_per_active                1400
% 11.55/1.95  --inst_solver_calls_frac                1.
% 11.55/1.95  --inst_passive_queue_type               priority_queues
% 11.55/1.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/1.95  --inst_passive_queues_freq              [25;2]
% 11.55/1.95  --inst_dismatching                      true
% 11.55/1.95  --inst_eager_unprocessed_to_passive     true
% 11.55/1.95  --inst_prop_sim_given                   true
% 11.55/1.95  --inst_prop_sim_new                     false
% 11.55/1.95  --inst_subs_new                         false
% 11.55/1.95  --inst_eq_res_simp                      false
% 11.55/1.95  --inst_subs_given                       false
% 11.55/1.95  --inst_orphan_elimination               true
% 11.55/1.95  --inst_learning_loop_flag               true
% 11.55/1.95  --inst_learning_start                   3000
% 11.55/1.95  --inst_learning_factor                  2
% 11.55/1.95  --inst_start_prop_sim_after_learn       3
% 11.55/1.95  --inst_sel_renew                        solver
% 11.55/1.95  --inst_lit_activity_flag                true
% 11.55/1.95  --inst_restr_to_given                   false
% 11.55/1.95  --inst_activity_threshold               500
% 11.55/1.95  --inst_out_proof                        true
% 11.55/1.95  
% 11.55/1.95  ------ Resolution Options
% 11.55/1.95  
% 11.55/1.95  --resolution_flag                       true
% 11.55/1.95  --res_lit_sel                           adaptive
% 11.55/1.95  --res_lit_sel_side                      none
% 11.55/1.95  --res_ordering                          kbo
% 11.55/1.95  --res_to_prop_solver                    active
% 11.55/1.95  --res_prop_simpl_new                    false
% 11.55/1.95  --res_prop_simpl_given                  true
% 11.55/1.95  --res_passive_queue_type                priority_queues
% 11.55/1.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/1.95  --res_passive_queues_freq               [15;5]
% 11.55/1.95  --res_forward_subs                      full
% 11.55/1.95  --res_backward_subs                     full
% 11.55/1.95  --res_forward_subs_resolution           true
% 11.55/1.95  --res_backward_subs_resolution          true
% 11.55/1.95  --res_orphan_elimination                true
% 11.55/1.95  --res_time_limit                        2.
% 11.55/1.95  --res_out_proof                         true
% 11.55/1.95  
% 11.55/1.95  ------ Superposition Options
% 11.55/1.95  
% 11.55/1.95  --superposition_flag                    true
% 11.55/1.95  --sup_passive_queue_type                priority_queues
% 11.55/1.95  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/1.95  --sup_passive_queues_freq               [1;4]
% 11.55/1.95  --demod_completeness_check              fast
% 11.55/1.95  --demod_use_ground                      true
% 11.55/1.95  --sup_to_prop_solver                    passive
% 11.55/1.95  --sup_prop_simpl_new                    true
% 11.55/1.95  --sup_prop_simpl_given                  true
% 11.55/1.95  --sup_fun_splitting                     false
% 11.55/1.95  --sup_smt_interval                      50000
% 11.55/1.95  
% 11.55/1.95  ------ Superposition Simplification Setup
% 11.55/1.95  
% 11.55/1.95  --sup_indices_passive                   []
% 11.55/1.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/1.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.95  --sup_full_bw                           [BwDemod]
% 11.55/1.95  --sup_immed_triv                        [TrivRules]
% 11.55/1.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.95  --sup_immed_bw_main                     []
% 11.55/1.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/1.95  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/1.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/1.95  
% 11.55/1.95  ------ Combination Options
% 11.55/1.95  
% 11.55/1.95  --comb_res_mult                         3
% 11.55/1.95  --comb_sup_mult                         2
% 11.55/1.95  --comb_inst_mult                        10
% 11.55/1.95  
% 11.55/1.95  ------ Debug Options
% 11.55/1.95  
% 11.55/1.95  --dbg_backtrace                         false
% 11.55/1.95  --dbg_dump_prop_clauses                 false
% 11.55/1.95  --dbg_dump_prop_clauses_file            -
% 11.55/1.95  --dbg_out_stat                          false
% 11.55/1.95  ------ Parsing...
% 11.55/1.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.55/1.95  
% 11.55/1.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.55/1.95  
% 11.55/1.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.55/1.95  
% 11.55/1.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.55/1.95  ------ Proving...
% 11.55/1.95  ------ Problem Properties 
% 11.55/1.95  
% 11.55/1.95  
% 11.55/1.95  clauses                                 12
% 11.55/1.95  conjectures                             3
% 11.55/1.95  EPR                                     3
% 11.55/1.95  Horn                                    12
% 11.55/1.95  unary                                   9
% 11.55/1.95  binary                                  3
% 11.55/1.95  lits                                    15
% 11.55/1.95  lits eq                                 8
% 11.55/1.95  fd_pure                                 0
% 11.55/1.95  fd_pseudo                               0
% 11.55/1.95  fd_cond                                 0
% 11.55/1.95  fd_pseudo_cond                          0
% 11.55/1.95  AC symbols                              0
% 11.55/1.95  
% 11.55/1.95  ------ Input Options Time Limit: Unbounded
% 11.55/1.95  
% 11.55/1.95  
% 11.55/1.95  ------ 
% 11.55/1.95  Current options:
% 11.55/1.95  ------ 
% 11.55/1.95  
% 11.55/1.95  ------ Input Options
% 11.55/1.95  
% 11.55/1.95  --out_options                           all
% 11.55/1.95  --tptp_safe_out                         true
% 11.55/1.95  --problem_path                          ""
% 11.55/1.95  --include_path                          ""
% 11.55/1.95  --clausifier                            res/vclausify_rel
% 11.55/1.95  --clausifier_options                    --mode clausify
% 11.55/1.95  --stdin                                 false
% 11.55/1.95  --stats_out                             sel
% 11.55/1.95  
% 11.55/1.95  ------ General Options
% 11.55/1.95  
% 11.55/1.95  --fof                                   false
% 11.55/1.95  --time_out_real                         604.99
% 11.55/1.95  --time_out_virtual                      -1.
% 11.55/1.95  --symbol_type_check                     false
% 11.55/1.95  --clausify_out                          false
% 11.55/1.95  --sig_cnt_out                           false
% 11.55/1.95  --trig_cnt_out                          false
% 11.55/1.95  --trig_cnt_out_tolerance                1.
% 11.55/1.95  --trig_cnt_out_sk_spl                   false
% 11.55/1.95  --abstr_cl_out                          false
% 11.55/1.95  
% 11.55/1.95  ------ Global Options
% 11.55/1.95  
% 11.55/1.95  --schedule                              none
% 11.55/1.95  --add_important_lit                     false
% 11.55/1.95  --prop_solver_per_cl                    1000
% 11.55/1.95  --min_unsat_core                        false
% 11.55/1.95  --soft_assumptions                      false
% 11.55/1.95  --soft_lemma_size                       3
% 11.55/1.95  --prop_impl_unit_size                   0
% 11.55/1.95  --prop_impl_unit                        []
% 11.55/1.95  --share_sel_clauses                     true
% 11.55/1.95  --reset_solvers                         false
% 11.55/1.95  --bc_imp_inh                            [conj_cone]
% 11.55/1.95  --conj_cone_tolerance                   3.
% 11.55/1.95  --extra_neg_conj                        none
% 11.55/1.95  --large_theory_mode                     true
% 11.55/1.95  --prolific_symb_bound                   200
% 11.55/1.95  --lt_threshold                          2000
% 11.55/1.95  --clause_weak_htbl                      true
% 11.55/1.95  --gc_record_bc_elim                     false
% 11.55/1.95  
% 11.55/1.95  ------ Preprocessing Options
% 11.55/1.95  
% 11.55/1.95  --preprocessing_flag                    true
% 11.55/1.95  --time_out_prep_mult                    0.1
% 11.55/1.95  --splitting_mode                        input
% 11.55/1.95  --splitting_grd                         true
% 11.55/1.95  --splitting_cvd                         false
% 11.55/1.95  --splitting_cvd_svl                     false
% 11.55/1.95  --splitting_nvd                         32
% 11.55/1.95  --sub_typing                            true
% 11.55/1.95  --prep_gs_sim                           false
% 11.55/1.95  --prep_unflatten                        true
% 11.55/1.95  --prep_res_sim                          true
% 11.55/1.95  --prep_upred                            true
% 11.55/1.95  --prep_sem_filter                       exhaustive
% 11.55/1.95  --prep_sem_filter_out                   false
% 11.55/1.95  --pred_elim                             false
% 11.55/1.95  --res_sim_input                         true
% 11.55/1.95  --eq_ax_congr_red                       true
% 11.55/1.95  --pure_diseq_elim                       true
% 11.55/1.95  --brand_transform                       false
% 11.55/1.95  --non_eq_to_eq                          false
% 11.55/1.95  --prep_def_merge                        true
% 11.55/1.95  --prep_def_merge_prop_impl              false
% 11.55/1.95  --prep_def_merge_mbd                    true
% 11.55/1.95  --prep_def_merge_tr_red                 false
% 11.55/1.95  --prep_def_merge_tr_cl                  false
% 11.55/1.95  --smt_preprocessing                     true
% 11.55/1.95  --smt_ac_axioms                         fast
% 11.55/1.95  --preprocessed_out                      false
% 11.55/1.95  --preprocessed_stats                    false
% 11.55/1.95  
% 11.55/1.95  ------ Abstraction refinement Options
% 11.55/1.95  
% 11.55/1.95  --abstr_ref                             []
% 11.55/1.95  --abstr_ref_prep                        false
% 11.55/1.95  --abstr_ref_until_sat                   false
% 11.55/1.95  --abstr_ref_sig_restrict                funpre
% 11.55/1.95  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/1.95  --abstr_ref_under                       []
% 11.55/1.95  
% 11.55/1.95  ------ SAT Options
% 11.55/1.95  
% 11.55/1.95  --sat_mode                              false
% 11.55/1.95  --sat_fm_restart_options                ""
% 11.55/1.95  --sat_gr_def                            false
% 11.55/1.95  --sat_epr_types                         true
% 11.55/1.95  --sat_non_cyclic_types                  false
% 11.55/1.95  --sat_finite_models                     false
% 11.55/1.95  --sat_fm_lemmas                         false
% 11.55/1.95  --sat_fm_prep                           false
% 11.55/1.95  --sat_fm_uc_incr                        true
% 11.55/1.95  --sat_out_model                         small
% 11.55/1.95  --sat_out_clauses                       false
% 11.55/1.95  
% 11.55/1.95  ------ QBF Options
% 11.55/1.95  
% 11.55/1.95  --qbf_mode                              false
% 11.55/1.95  --qbf_elim_univ                         false
% 11.55/1.95  --qbf_dom_inst                          none
% 11.55/1.95  --qbf_dom_pre_inst                      false
% 11.55/1.95  --qbf_sk_in                             false
% 11.55/1.95  --qbf_pred_elim                         true
% 11.55/1.95  --qbf_split                             512
% 11.55/1.95  
% 11.55/1.95  ------ BMC1 Options
% 11.55/1.95  
% 11.55/1.95  --bmc1_incremental                      false
% 11.55/1.95  --bmc1_axioms                           reachable_all
% 11.55/1.95  --bmc1_min_bound                        0
% 11.55/1.95  --bmc1_max_bound                        -1
% 11.55/1.95  --bmc1_max_bound_default                -1
% 11.55/1.95  --bmc1_symbol_reachability              true
% 11.55/1.95  --bmc1_property_lemmas                  false
% 11.55/1.95  --bmc1_k_induction                      false
% 11.55/1.95  --bmc1_non_equiv_states                 false
% 11.55/1.95  --bmc1_deadlock                         false
% 11.55/1.95  --bmc1_ucm                              false
% 11.55/1.95  --bmc1_add_unsat_core                   none
% 11.55/1.95  --bmc1_unsat_core_children              false
% 11.55/1.95  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/1.95  --bmc1_out_stat                         full
% 11.55/1.95  --bmc1_ground_init                      false
% 11.55/1.95  --bmc1_pre_inst_next_state              false
% 11.55/1.95  --bmc1_pre_inst_state                   false
% 11.55/1.95  --bmc1_pre_inst_reach_state             false
% 11.55/1.95  --bmc1_out_unsat_core                   false
% 11.55/1.95  --bmc1_aig_witness_out                  false
% 11.55/1.95  --bmc1_verbose                          false
% 11.55/1.95  --bmc1_dump_clauses_tptp                false
% 11.55/1.95  --bmc1_dump_unsat_core_tptp             false
% 11.55/1.95  --bmc1_dump_file                        -
% 11.55/1.95  --bmc1_ucm_expand_uc_limit              128
% 11.55/1.95  --bmc1_ucm_n_expand_iterations          6
% 11.55/1.95  --bmc1_ucm_extend_mode                  1
% 11.55/1.95  --bmc1_ucm_init_mode                    2
% 11.55/1.95  --bmc1_ucm_cone_mode                    none
% 11.55/1.95  --bmc1_ucm_reduced_relation_type        0
% 11.55/1.95  --bmc1_ucm_relax_model                  4
% 11.55/1.95  --bmc1_ucm_full_tr_after_sat            true
% 11.55/1.95  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/1.95  --bmc1_ucm_layered_model                none
% 11.55/1.95  --bmc1_ucm_max_lemma_size               10
% 11.55/1.95  
% 11.55/1.95  ------ AIG Options
% 11.55/1.95  
% 11.55/1.95  --aig_mode                              false
% 11.55/1.95  
% 11.55/1.95  ------ Instantiation Options
% 11.55/1.95  
% 11.55/1.95  --instantiation_flag                    true
% 11.55/1.95  --inst_sos_flag                         false
% 11.55/1.95  --inst_sos_phase                        true
% 11.55/1.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/1.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/1.95  --inst_lit_sel_side                     num_symb
% 11.55/1.95  --inst_solver_per_active                1400
% 11.55/1.95  --inst_solver_calls_frac                1.
% 11.55/1.95  --inst_passive_queue_type               priority_queues
% 11.55/1.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/1.95  --inst_passive_queues_freq              [25;2]
% 11.55/1.95  --inst_dismatching                      true
% 11.55/1.95  --inst_eager_unprocessed_to_passive     true
% 11.55/1.95  --inst_prop_sim_given                   true
% 11.55/1.95  --inst_prop_sim_new                     false
% 11.55/1.95  --inst_subs_new                         false
% 11.55/1.95  --inst_eq_res_simp                      false
% 11.55/1.95  --inst_subs_given                       false
% 11.55/1.95  --inst_orphan_elimination               true
% 11.55/1.95  --inst_learning_loop_flag               true
% 11.55/1.95  --inst_learning_start                   3000
% 11.55/1.95  --inst_learning_factor                  2
% 11.55/1.95  --inst_start_prop_sim_after_learn       3
% 11.55/1.95  --inst_sel_renew                        solver
% 11.55/1.95  --inst_lit_activity_flag                true
% 11.55/1.95  --inst_restr_to_given                   false
% 11.55/1.95  --inst_activity_threshold               500
% 11.55/1.95  --inst_out_proof                        true
% 11.55/1.95  
% 11.55/1.95  ------ Resolution Options
% 11.55/1.95  
% 11.55/1.95  --resolution_flag                       true
% 11.55/1.95  --res_lit_sel                           adaptive
% 11.55/1.95  --res_lit_sel_side                      none
% 11.55/1.95  --res_ordering                          kbo
% 11.55/1.95  --res_to_prop_solver                    active
% 11.55/1.95  --res_prop_simpl_new                    false
% 11.55/1.95  --res_prop_simpl_given                  true
% 11.55/1.95  --res_passive_queue_type                priority_queues
% 11.55/1.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/1.95  --res_passive_queues_freq               [15;5]
% 11.55/1.95  --res_forward_subs                      full
% 11.55/1.95  --res_backward_subs                     full
% 11.55/1.95  --res_forward_subs_resolution           true
% 11.55/1.95  --res_backward_subs_resolution          true
% 11.55/1.95  --res_orphan_elimination                true
% 11.55/1.95  --res_time_limit                        2.
% 11.55/1.95  --res_out_proof                         true
% 11.55/1.95  
% 11.55/1.95  ------ Superposition Options
% 11.55/1.95  
% 11.55/1.95  --superposition_flag                    true
% 11.55/1.95  --sup_passive_queue_type                priority_queues
% 11.55/1.95  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/1.95  --sup_passive_queues_freq               [1;4]
% 11.55/1.95  --demod_completeness_check              fast
% 11.55/1.95  --demod_use_ground                      true
% 11.55/1.95  --sup_to_prop_solver                    passive
% 11.55/1.95  --sup_prop_simpl_new                    true
% 11.55/1.95  --sup_prop_simpl_given                  true
% 11.55/1.95  --sup_fun_splitting                     false
% 11.55/1.95  --sup_smt_interval                      50000
% 11.55/1.95  
% 11.55/1.95  ------ Superposition Simplification Setup
% 11.55/1.95  
% 11.55/1.95  --sup_indices_passive                   []
% 11.55/1.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.95  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/1.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.95  --sup_full_bw                           [BwDemod]
% 11.55/1.95  --sup_immed_triv                        [TrivRules]
% 11.55/1.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.95  --sup_immed_bw_main                     []
% 11.55/1.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/1.96  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/1.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/1.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/1.96  
% 11.55/1.96  ------ Combination Options
% 11.55/1.96  
% 11.55/1.96  --comb_res_mult                         3
% 11.55/1.96  --comb_sup_mult                         2
% 11.55/1.96  --comb_inst_mult                        10
% 11.55/1.96  
% 11.55/1.96  ------ Debug Options
% 11.55/1.96  
% 11.55/1.96  --dbg_backtrace                         false
% 11.55/1.96  --dbg_dump_prop_clauses                 false
% 11.55/1.96  --dbg_dump_prop_clauses_file            -
% 11.55/1.96  --dbg_out_stat                          false
% 11.55/1.96  
% 11.55/1.96  
% 11.55/1.96  
% 11.55/1.96  
% 11.55/1.96  ------ Proving...
% 11.55/1.96  
% 11.55/1.96  
% 11.55/1.96  % SZS status Theorem for theBenchmark.p
% 11.55/1.96  
% 11.55/1.96  % SZS output start CNFRefutation for theBenchmark.p
% 11.55/1.96  
% 11.55/1.96  fof(f10,conjecture,(
% 11.55/1.96    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f11,negated_conjecture,(
% 11.55/1.96    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.55/1.96    inference(negated_conjecture,[],[f10])).
% 11.55/1.96  
% 11.55/1.96  fof(f15,plain,(
% 11.55/1.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 11.55/1.96    inference(ennf_transformation,[],[f11])).
% 11.55/1.96  
% 11.55/1.96  fof(f16,plain,(
% 11.55/1.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 11.55/1.96    inference(flattening,[],[f15])).
% 11.55/1.96  
% 11.55/1.96  fof(f18,plain,(
% 11.55/1.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 11.55/1.96    introduced(choice_axiom,[])).
% 11.55/1.96  
% 11.55/1.96  fof(f19,plain,(
% 11.55/1.96    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 11.55/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 11.55/1.96  
% 11.55/1.96  fof(f30,plain,(
% 11.55/1.96    r1_tarski(sK0,sK1)),
% 11.55/1.96    inference(cnf_transformation,[],[f19])).
% 11.55/1.96  
% 11.55/1.96  fof(f5,axiom,(
% 11.55/1.96    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f13,plain,(
% 11.55/1.96    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 11.55/1.96    inference(unused_predicate_definition_removal,[],[f5])).
% 11.55/1.96  
% 11.55/1.96  fof(f14,plain,(
% 11.55/1.96    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 11.55/1.96    inference(ennf_transformation,[],[f13])).
% 11.55/1.96  
% 11.55/1.96  fof(f25,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f14])).
% 11.55/1.96  
% 11.55/1.96  fof(f2,axiom,(
% 11.55/1.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f21,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f2])).
% 11.55/1.96  
% 11.55/1.96  fof(f9,axiom,(
% 11.55/1.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f29,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.55/1.96    inference(cnf_transformation,[],[f9])).
% 11.55/1.96  
% 11.55/1.96  fof(f33,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.55/1.96    inference(definition_unfolding,[],[f21,f29,f29])).
% 11.55/1.96  
% 11.55/1.96  fof(f8,axiom,(
% 11.55/1.96    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f28,plain,(
% 11.55/1.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f8])).
% 11.55/1.96  
% 11.55/1.96  fof(f7,axiom,(
% 11.55/1.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f27,plain,(
% 11.55/1.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.55/1.96    inference(cnf_transformation,[],[f7])).
% 11.55/1.96  
% 11.55/1.96  fof(f1,axiom,(
% 11.55/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f20,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f1])).
% 11.55/1.96  
% 11.55/1.96  fof(f31,plain,(
% 11.55/1.96    r1_xboole_0(sK1,sK2)),
% 11.55/1.96    inference(cnf_transformation,[],[f19])).
% 11.55/1.96  
% 11.55/1.96  fof(f3,axiom,(
% 11.55/1.96    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f17,plain,(
% 11.55/1.96    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.55/1.96    inference(nnf_transformation,[],[f3])).
% 11.55/1.96  
% 11.55/1.96  fof(f22,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f17])).
% 11.55/1.96  
% 11.55/1.96  fof(f35,plain,(
% 11.55/1.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.55/1.96    inference(definition_unfolding,[],[f22,f29])).
% 11.55/1.96  
% 11.55/1.96  fof(f6,axiom,(
% 11.55/1.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.55/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/1.96  
% 11.55/1.96  fof(f26,plain,(
% 11.55/1.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.55/1.96    inference(cnf_transformation,[],[f6])).
% 11.55/1.96  
% 11.55/1.96  fof(f23,plain,(
% 11.55/1.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.55/1.96    inference(cnf_transformation,[],[f17])).
% 11.55/1.96  
% 11.55/1.96  fof(f34,plain,(
% 11.55/1.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.55/1.96    inference(definition_unfolding,[],[f23,f29])).
% 11.55/1.96  
% 11.55/1.96  fof(f32,plain,(
% 11.55/1.96    ~r1_xboole_0(sK0,sK2)),
% 11.55/1.96    inference(cnf_transformation,[],[f19])).
% 11.55/1.96  
% 11.55/1.96  cnf(c_11,negated_conjecture,
% 11.55/1.96      ( r1_tarski(sK0,sK1) ),
% 11.55/1.96      inference(cnf_transformation,[],[f30]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_290,plain,
% 11.55/1.96      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_5,plain,
% 11.55/1.96      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.55/1.96      inference(cnf_transformation,[],[f25]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_294,plain,
% 11.55/1.96      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.55/1.96      | r1_tarski(X0,X1) != iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_866,plain,
% 11.55/1.96      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_290,c_294]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_1,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.55/1.96      inference(cnf_transformation,[],[f33]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_8,plain,
% 11.55/1.96      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.55/1.96      inference(cnf_transformation,[],[f28]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_651,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_41006,plain,
% 11.55/1.96      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_866,c_651]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_7,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.55/1.96      inference(cnf_transformation,[],[f27]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_653,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_41795,plain,
% 11.55/1.96      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK0,X0) ),
% 11.55/1.96      inference(demodulation,[status(thm)],[c_41006,c_8,c_653]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_0,plain,
% 11.55/1.96      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.55/1.96      inference(cnf_transformation,[],[f20]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_10,negated_conjecture,
% 11.55/1.96      ( r1_xboole_0(sK1,sK2) ),
% 11.55/1.96      inference(cnf_transformation,[],[f31]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_291,plain,
% 11.55/1.96      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_3,plain,
% 11.55/1.96      ( ~ r1_xboole_0(X0,X1)
% 11.55/1.96      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.55/1.96      inference(cnf_transformation,[],[f35]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_295,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.55/1.96      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_1114,plain,
% 11.55/1.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_291,c_295]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_6,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.55/1.96      inference(cnf_transformation,[],[f26]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_293,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_794,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_8,c_293]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_1231,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_0,c_794]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_41056,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,X2)) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_651,c_1231]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_41650,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(X1,X2)) = iProver_top ),
% 11.55/1.96      inference(demodulation,[status(thm)],[c_41056,c_8]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_46928,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_1114,c_41650]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_47380,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k2_xboole_0(sK2,X0))) = iProver_top ),
% 11.55/1.96      inference(demodulation,[status(thm)],[c_46928,c_8,c_653]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_47965,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_0,c_47380]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_48685,plain,
% 11.55/1.96      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,sK2)) = iProver_top ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_41795,c_47965]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_660,plain,
% 11.55/1.96      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_42963,plain,
% 11.55/1.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 11.55/1.96      inference(superposition,[status(thm)],[c_41795,c_660]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_43036,plain,
% 11.55/1.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
% 11.55/1.96      inference(demodulation,[status(thm)],[c_42963,c_7]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_48693,plain,
% 11.55/1.96      ( r1_tarski(sK0,k4_xboole_0(sK0,sK2)) = iProver_top ),
% 11.55/1.96      inference(light_normalisation,[status(thm)],[c_48685,c_43036]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_355,plain,
% 11.55/1.96      ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
% 11.55/1.96      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.55/1.96      inference(instantiation,[status(thm)],[c_5]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_1205,plain,
% 11.55/1.96      ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK2))
% 11.55/1.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 11.55/1.96      inference(instantiation,[status(thm)],[c_355]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_1207,plain,
% 11.55/1.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 11.55/1.96      | r1_tarski(sK0,k4_xboole_0(sK0,sK2)) != iProver_top ),
% 11.55/1.96      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_2,plain,
% 11.55/1.96      ( r1_xboole_0(X0,X1)
% 11.55/1.96      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.55/1.96      inference(cnf_transformation,[],[f34]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_846,plain,
% 11.55/1.96      ( r1_xboole_0(sK0,sK2)
% 11.55/1.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 11.55/1.96      inference(instantiation,[status(thm)],[c_2]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(c_9,negated_conjecture,
% 11.55/1.96      ( ~ r1_xboole_0(sK0,sK2) ),
% 11.55/1.96      inference(cnf_transformation,[],[f32]) ).
% 11.55/1.96  
% 11.55/1.96  cnf(contradiction,plain,
% 11.55/1.96      ( $false ),
% 11.55/1.96      inference(minisat,[status(thm)],[c_48693,c_1207,c_846,c_9]) ).
% 11.55/1.96  
% 11.55/1.96  
% 11.55/1.96  % SZS output end CNFRefutation for theBenchmark.p
% 11.55/1.96  
% 11.55/1.96  ------                               Statistics
% 11.55/1.96  
% 11.55/1.96  ------ Selected
% 11.55/1.96  
% 11.55/1.96  total_time:                             1.315
% 11.55/1.96  
%------------------------------------------------------------------------------
