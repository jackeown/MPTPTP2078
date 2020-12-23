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
% DateTime   : Thu Dec  3 11:26:14 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 132 expanded)
%              Number of clauses        :   34 (  43 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 176 expanded)
%              Number of equality atoms :   81 ( 155 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f20,f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f25,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f25,f23,f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f24,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_277,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_195,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_842,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_277,c_195])).

cnf(c_940,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_842,c_4])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_203,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_2220,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_940,c_203])).

cnf(c_2226,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_2220,c_4])).

cnf(c_2227,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_2226,c_0])).

cnf(c_6,negated_conjecture,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_129,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_6,c_4])).

cnf(c_16007,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_2227,c_129])).

cnf(c_45,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_402,plain,
    ( X0 != sK2
    | X1 != sK0
    | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_9052,plain,
    ( X0 != sK0
    | k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_9064,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
    | k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_9052])).

cnf(c_44,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_182,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_1093,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | X0 = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_1688,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_577,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_263,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_511,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_567,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != sK2
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_43,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_177,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_150,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_52,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16007,c_9064,c_1688,c_577,c_567,c_177,c_150,c_52,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:13:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.85/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.50  
% 7.85/1.50  ------  iProver source info
% 7.85/1.50  
% 7.85/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.50  git: non_committed_changes: false
% 7.85/1.50  git: last_make_outside_of_git: false
% 7.85/1.50  
% 7.85/1.50  ------ 
% 7.85/1.50  
% 7.85/1.50  ------ Input Options
% 7.85/1.50  
% 7.85/1.50  --out_options                           all
% 7.85/1.50  --tptp_safe_out                         true
% 7.85/1.50  --problem_path                          ""
% 7.85/1.50  --include_path                          ""
% 7.85/1.50  --clausifier                            res/vclausify_rel
% 7.85/1.50  --clausifier_options                    --mode clausify
% 7.85/1.50  --stdin                                 false
% 7.85/1.50  --stats_out                             sel
% 7.85/1.50  
% 7.85/1.50  ------ General Options
% 7.85/1.50  
% 7.85/1.50  --fof                                   false
% 7.85/1.50  --time_out_real                         604.99
% 7.85/1.50  --time_out_virtual                      -1.
% 7.85/1.50  --symbol_type_check                     false
% 7.85/1.50  --clausify_out                          false
% 7.85/1.50  --sig_cnt_out                           false
% 7.85/1.50  --trig_cnt_out                          false
% 7.85/1.50  --trig_cnt_out_tolerance                1.
% 7.85/1.50  --trig_cnt_out_sk_spl                   false
% 7.85/1.50  --abstr_cl_out                          false
% 7.85/1.50  
% 7.85/1.50  ------ Global Options
% 7.85/1.50  
% 7.85/1.50  --schedule                              none
% 7.85/1.50  --add_important_lit                     false
% 7.85/1.50  --prop_solver_per_cl                    1000
% 7.85/1.50  --min_unsat_core                        false
% 7.85/1.50  --soft_assumptions                      false
% 7.85/1.50  --soft_lemma_size                       3
% 7.85/1.50  --prop_impl_unit_size                   0
% 7.85/1.50  --prop_impl_unit                        []
% 7.85/1.50  --share_sel_clauses                     true
% 7.85/1.50  --reset_solvers                         false
% 7.85/1.50  --bc_imp_inh                            [conj_cone]
% 7.85/1.50  --conj_cone_tolerance                   3.
% 7.85/1.50  --extra_neg_conj                        none
% 7.85/1.50  --large_theory_mode                     true
% 7.85/1.50  --prolific_symb_bound                   200
% 7.85/1.50  --lt_threshold                          2000
% 7.85/1.50  --clause_weak_htbl                      true
% 7.85/1.50  --gc_record_bc_elim                     false
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing Options
% 7.85/1.50  
% 7.85/1.50  --preprocessing_flag                    true
% 7.85/1.50  --time_out_prep_mult                    0.1
% 7.85/1.50  --splitting_mode                        input
% 7.85/1.50  --splitting_grd                         true
% 7.85/1.50  --splitting_cvd                         false
% 7.85/1.50  --splitting_cvd_svl                     false
% 7.85/1.50  --splitting_nvd                         32
% 7.85/1.50  --sub_typing                            true
% 7.85/1.50  --prep_gs_sim                           false
% 7.85/1.50  --prep_unflatten                        true
% 7.85/1.50  --prep_res_sim                          true
% 7.85/1.50  --prep_upred                            true
% 7.85/1.50  --prep_sem_filter                       exhaustive
% 7.85/1.50  --prep_sem_filter_out                   false
% 7.85/1.50  --pred_elim                             false
% 7.85/1.50  --res_sim_input                         true
% 7.85/1.50  --eq_ax_congr_red                       true
% 7.85/1.50  --pure_diseq_elim                       true
% 7.85/1.50  --brand_transform                       false
% 7.85/1.50  --non_eq_to_eq                          false
% 7.85/1.50  --prep_def_merge                        true
% 7.85/1.50  --prep_def_merge_prop_impl              false
% 7.85/1.50  --prep_def_merge_mbd                    true
% 7.85/1.50  --prep_def_merge_tr_red                 false
% 7.85/1.50  --prep_def_merge_tr_cl                  false
% 7.85/1.50  --smt_preprocessing                     true
% 7.85/1.50  --smt_ac_axioms                         fast
% 7.85/1.50  --preprocessed_out                      false
% 7.85/1.50  --preprocessed_stats                    false
% 7.85/1.50  
% 7.85/1.50  ------ Abstraction refinement Options
% 7.85/1.50  
% 7.85/1.50  --abstr_ref                             []
% 7.85/1.50  --abstr_ref_prep                        false
% 7.85/1.50  --abstr_ref_until_sat                   false
% 7.85/1.50  --abstr_ref_sig_restrict                funpre
% 7.85/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.50  --abstr_ref_under                       []
% 7.85/1.50  
% 7.85/1.50  ------ SAT Options
% 7.85/1.50  
% 7.85/1.50  --sat_mode                              false
% 7.85/1.50  --sat_fm_restart_options                ""
% 7.85/1.50  --sat_gr_def                            false
% 7.85/1.50  --sat_epr_types                         true
% 7.85/1.50  --sat_non_cyclic_types                  false
% 7.85/1.50  --sat_finite_models                     false
% 7.85/1.50  --sat_fm_lemmas                         false
% 7.85/1.50  --sat_fm_prep                           false
% 7.85/1.50  --sat_fm_uc_incr                        true
% 7.85/1.50  --sat_out_model                         small
% 7.85/1.50  --sat_out_clauses                       false
% 7.85/1.50  
% 7.85/1.50  ------ QBF Options
% 7.85/1.50  
% 7.85/1.50  --qbf_mode                              false
% 7.85/1.50  --qbf_elim_univ                         false
% 7.85/1.50  --qbf_dom_inst                          none
% 7.85/1.50  --qbf_dom_pre_inst                      false
% 7.85/1.50  --qbf_sk_in                             false
% 7.85/1.50  --qbf_pred_elim                         true
% 7.85/1.50  --qbf_split                             512
% 7.85/1.50  
% 7.85/1.50  ------ BMC1 Options
% 7.85/1.50  
% 7.85/1.50  --bmc1_incremental                      false
% 7.85/1.50  --bmc1_axioms                           reachable_all
% 7.85/1.50  --bmc1_min_bound                        0
% 7.85/1.50  --bmc1_max_bound                        -1
% 7.85/1.50  --bmc1_max_bound_default                -1
% 7.85/1.50  --bmc1_symbol_reachability              true
% 7.85/1.50  --bmc1_property_lemmas                  false
% 7.85/1.50  --bmc1_k_induction                      false
% 7.85/1.50  --bmc1_non_equiv_states                 false
% 7.85/1.50  --bmc1_deadlock                         false
% 7.85/1.50  --bmc1_ucm                              false
% 7.85/1.50  --bmc1_add_unsat_core                   none
% 7.85/1.50  --bmc1_unsat_core_children              false
% 7.85/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.50  --bmc1_out_stat                         full
% 7.85/1.50  --bmc1_ground_init                      false
% 7.85/1.50  --bmc1_pre_inst_next_state              false
% 7.85/1.50  --bmc1_pre_inst_state                   false
% 7.85/1.50  --bmc1_pre_inst_reach_state             false
% 7.85/1.50  --bmc1_out_unsat_core                   false
% 7.85/1.50  --bmc1_aig_witness_out                  false
% 7.85/1.50  --bmc1_verbose                          false
% 7.85/1.50  --bmc1_dump_clauses_tptp                false
% 7.85/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.50  --bmc1_dump_file                        -
% 7.85/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.50  --bmc1_ucm_extend_mode                  1
% 7.85/1.50  --bmc1_ucm_init_mode                    2
% 7.85/1.50  --bmc1_ucm_cone_mode                    none
% 7.85/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.50  --bmc1_ucm_relax_model                  4
% 7.85/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.50  --bmc1_ucm_layered_model                none
% 7.85/1.50  --bmc1_ucm_max_lemma_size               10
% 7.85/1.50  
% 7.85/1.50  ------ AIG Options
% 7.85/1.50  
% 7.85/1.50  --aig_mode                              false
% 7.85/1.50  
% 7.85/1.50  ------ Instantiation Options
% 7.85/1.50  
% 7.85/1.50  --instantiation_flag                    true
% 7.85/1.50  --inst_sos_flag                         false
% 7.85/1.50  --inst_sos_phase                        true
% 7.85/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.50  --inst_lit_sel_side                     num_symb
% 7.85/1.50  --inst_solver_per_active                1400
% 7.85/1.50  --inst_solver_calls_frac                1.
% 7.85/1.50  --inst_passive_queue_type               priority_queues
% 7.85/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.50  --inst_passive_queues_freq              [25;2]
% 7.85/1.50  --inst_dismatching                      true
% 7.85/1.50  --inst_eager_unprocessed_to_passive     true
% 7.85/1.50  --inst_prop_sim_given                   true
% 7.85/1.50  --inst_prop_sim_new                     false
% 7.85/1.50  --inst_subs_new                         false
% 7.85/1.50  --inst_eq_res_simp                      false
% 7.85/1.50  --inst_subs_given                       false
% 7.85/1.50  --inst_orphan_elimination               true
% 7.85/1.50  --inst_learning_loop_flag               true
% 7.85/1.50  --inst_learning_start                   3000
% 7.85/1.50  --inst_learning_factor                  2
% 7.85/1.50  --inst_start_prop_sim_after_learn       3
% 7.85/1.50  --inst_sel_renew                        solver
% 7.85/1.50  --inst_lit_activity_flag                true
% 7.85/1.50  --inst_restr_to_given                   false
% 7.85/1.50  --inst_activity_threshold               500
% 7.85/1.50  --inst_out_proof                        true
% 7.85/1.50  
% 7.85/1.50  ------ Resolution Options
% 7.85/1.50  
% 7.85/1.50  --resolution_flag                       true
% 7.85/1.50  --res_lit_sel                           adaptive
% 7.85/1.50  --res_lit_sel_side                      none
% 7.85/1.50  --res_ordering                          kbo
% 7.85/1.50  --res_to_prop_solver                    active
% 7.85/1.50  --res_prop_simpl_new                    false
% 7.85/1.50  --res_prop_simpl_given                  true
% 7.85/1.50  --res_passive_queue_type                priority_queues
% 7.85/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.50  --res_passive_queues_freq               [15;5]
% 7.85/1.50  --res_forward_subs                      full
% 7.85/1.50  --res_backward_subs                     full
% 7.85/1.50  --res_forward_subs_resolution           true
% 7.85/1.50  --res_backward_subs_resolution          true
% 7.85/1.50  --res_orphan_elimination                true
% 7.85/1.50  --res_time_limit                        2.
% 7.85/1.50  --res_out_proof                         true
% 7.85/1.50  
% 7.85/1.50  ------ Superposition Options
% 7.85/1.50  
% 7.85/1.50  --superposition_flag                    true
% 7.85/1.50  --sup_passive_queue_type                priority_queues
% 7.85/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.50  --sup_passive_queues_freq               [1;4]
% 7.85/1.50  --demod_completeness_check              fast
% 7.85/1.50  --demod_use_ground                      true
% 7.85/1.50  --sup_to_prop_solver                    passive
% 7.85/1.50  --sup_prop_simpl_new                    true
% 7.85/1.50  --sup_prop_simpl_given                  true
% 7.85/1.50  --sup_fun_splitting                     false
% 7.85/1.50  --sup_smt_interval                      50000
% 7.85/1.50  
% 7.85/1.50  ------ Superposition Simplification Setup
% 7.85/1.50  
% 7.85/1.50  --sup_indices_passive                   []
% 7.85/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_full_bw                           [BwDemod]
% 7.85/1.50  --sup_immed_triv                        [TrivRules]
% 7.85/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_immed_bw_main                     []
% 7.85/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.85/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.85/1.50  
% 7.85/1.50  ------ Combination Options
% 7.85/1.50  
% 7.85/1.50  --comb_res_mult                         3
% 7.85/1.50  --comb_sup_mult                         2
% 7.85/1.50  --comb_inst_mult                        10
% 7.85/1.50  
% 7.85/1.50  ------ Debug Options
% 7.85/1.50  
% 7.85/1.50  --dbg_backtrace                         false
% 7.85/1.50  --dbg_dump_prop_clauses                 false
% 7.85/1.50  --dbg_dump_prop_clauses_file            -
% 7.85/1.50  --dbg_out_stat                          false
% 7.85/1.50  ------ Parsing...
% 7.85/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.50  ------ Proving...
% 7.85/1.50  ------ Problem Properties 
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  clauses                                 8
% 7.85/1.50  conjectures                             2
% 7.85/1.50  EPR                                     1
% 7.85/1.50  Horn                                    8
% 7.85/1.50  unary                                   6
% 7.85/1.50  binary                                  2
% 7.85/1.50  lits                                    10
% 7.85/1.50  lits eq                                 7
% 7.85/1.50  fd_pure                                 0
% 7.85/1.50  fd_pseudo                               0
% 7.85/1.50  fd_cond                                 0
% 7.85/1.50  fd_pseudo_cond                          0
% 7.85/1.50  AC symbols                              0
% 7.85/1.50  
% 7.85/1.50  ------ Input Options Time Limit: Unbounded
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  ------ 
% 7.85/1.50  Current options:
% 7.85/1.50  ------ 
% 7.85/1.50  
% 7.85/1.50  ------ Input Options
% 7.85/1.50  
% 7.85/1.50  --out_options                           all
% 7.85/1.50  --tptp_safe_out                         true
% 7.85/1.50  --problem_path                          ""
% 7.85/1.50  --include_path                          ""
% 7.85/1.50  --clausifier                            res/vclausify_rel
% 7.85/1.50  --clausifier_options                    --mode clausify
% 7.85/1.50  --stdin                                 false
% 7.85/1.50  --stats_out                             sel
% 7.85/1.50  
% 7.85/1.50  ------ General Options
% 7.85/1.50  
% 7.85/1.50  --fof                                   false
% 7.85/1.50  --time_out_real                         604.99
% 7.85/1.50  --time_out_virtual                      -1.
% 7.85/1.50  --symbol_type_check                     false
% 7.85/1.50  --clausify_out                          false
% 7.85/1.50  --sig_cnt_out                           false
% 7.85/1.50  --trig_cnt_out                          false
% 7.85/1.50  --trig_cnt_out_tolerance                1.
% 7.85/1.50  --trig_cnt_out_sk_spl                   false
% 7.85/1.50  --abstr_cl_out                          false
% 7.85/1.50  
% 7.85/1.50  ------ Global Options
% 7.85/1.50  
% 7.85/1.50  --schedule                              none
% 7.85/1.50  --add_important_lit                     false
% 7.85/1.50  --prop_solver_per_cl                    1000
% 7.85/1.50  --min_unsat_core                        false
% 7.85/1.50  --soft_assumptions                      false
% 7.85/1.50  --soft_lemma_size                       3
% 7.85/1.50  --prop_impl_unit_size                   0
% 7.85/1.50  --prop_impl_unit                        []
% 7.85/1.50  --share_sel_clauses                     true
% 7.85/1.50  --reset_solvers                         false
% 7.85/1.50  --bc_imp_inh                            [conj_cone]
% 7.85/1.50  --conj_cone_tolerance                   3.
% 7.85/1.50  --extra_neg_conj                        none
% 7.85/1.50  --large_theory_mode                     true
% 7.85/1.50  --prolific_symb_bound                   200
% 7.85/1.50  --lt_threshold                          2000
% 7.85/1.50  --clause_weak_htbl                      true
% 7.85/1.50  --gc_record_bc_elim                     false
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing Options
% 7.85/1.50  
% 7.85/1.50  --preprocessing_flag                    true
% 7.85/1.50  --time_out_prep_mult                    0.1
% 7.85/1.50  --splitting_mode                        input
% 7.85/1.50  --splitting_grd                         true
% 7.85/1.50  --splitting_cvd                         false
% 7.85/1.50  --splitting_cvd_svl                     false
% 7.85/1.50  --splitting_nvd                         32
% 7.85/1.50  --sub_typing                            true
% 7.85/1.50  --prep_gs_sim                           false
% 7.85/1.50  --prep_unflatten                        true
% 7.85/1.50  --prep_res_sim                          true
% 7.85/1.50  --prep_upred                            true
% 7.85/1.50  --prep_sem_filter                       exhaustive
% 7.85/1.50  --prep_sem_filter_out                   false
% 7.85/1.50  --pred_elim                             false
% 7.85/1.50  --res_sim_input                         true
% 7.85/1.50  --eq_ax_congr_red                       true
% 7.85/1.50  --pure_diseq_elim                       true
% 7.85/1.50  --brand_transform                       false
% 7.85/1.50  --non_eq_to_eq                          false
% 7.85/1.50  --prep_def_merge                        true
% 7.85/1.50  --prep_def_merge_prop_impl              false
% 7.85/1.50  --prep_def_merge_mbd                    true
% 7.85/1.50  --prep_def_merge_tr_red                 false
% 7.85/1.50  --prep_def_merge_tr_cl                  false
% 7.85/1.50  --smt_preprocessing                     true
% 7.85/1.50  --smt_ac_axioms                         fast
% 7.85/1.50  --preprocessed_out                      false
% 7.85/1.50  --preprocessed_stats                    false
% 7.85/1.50  
% 7.85/1.50  ------ Abstraction refinement Options
% 7.85/1.50  
% 7.85/1.50  --abstr_ref                             []
% 7.85/1.50  --abstr_ref_prep                        false
% 7.85/1.50  --abstr_ref_until_sat                   false
% 7.85/1.50  --abstr_ref_sig_restrict                funpre
% 7.85/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.50  --abstr_ref_under                       []
% 7.85/1.50  
% 7.85/1.50  ------ SAT Options
% 7.85/1.50  
% 7.85/1.50  --sat_mode                              false
% 7.85/1.50  --sat_fm_restart_options                ""
% 7.85/1.50  --sat_gr_def                            false
% 7.85/1.50  --sat_epr_types                         true
% 7.85/1.50  --sat_non_cyclic_types                  false
% 7.85/1.50  --sat_finite_models                     false
% 7.85/1.50  --sat_fm_lemmas                         false
% 7.85/1.50  --sat_fm_prep                           false
% 7.85/1.50  --sat_fm_uc_incr                        true
% 7.85/1.50  --sat_out_model                         small
% 7.85/1.50  --sat_out_clauses                       false
% 7.85/1.50  
% 7.85/1.50  ------ QBF Options
% 7.85/1.50  
% 7.85/1.50  --qbf_mode                              false
% 7.85/1.50  --qbf_elim_univ                         false
% 7.85/1.50  --qbf_dom_inst                          none
% 7.85/1.50  --qbf_dom_pre_inst                      false
% 7.85/1.50  --qbf_sk_in                             false
% 7.85/1.50  --qbf_pred_elim                         true
% 7.85/1.50  --qbf_split                             512
% 7.85/1.50  
% 7.85/1.50  ------ BMC1 Options
% 7.85/1.50  
% 7.85/1.50  --bmc1_incremental                      false
% 7.85/1.50  --bmc1_axioms                           reachable_all
% 7.85/1.50  --bmc1_min_bound                        0
% 7.85/1.50  --bmc1_max_bound                        -1
% 7.85/1.50  --bmc1_max_bound_default                -1
% 7.85/1.50  --bmc1_symbol_reachability              true
% 7.85/1.50  --bmc1_property_lemmas                  false
% 7.85/1.50  --bmc1_k_induction                      false
% 7.85/1.50  --bmc1_non_equiv_states                 false
% 7.85/1.50  --bmc1_deadlock                         false
% 7.85/1.50  --bmc1_ucm                              false
% 7.85/1.50  --bmc1_add_unsat_core                   none
% 7.85/1.50  --bmc1_unsat_core_children              false
% 7.85/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.50  --bmc1_out_stat                         full
% 7.85/1.50  --bmc1_ground_init                      false
% 7.85/1.50  --bmc1_pre_inst_next_state              false
% 7.85/1.50  --bmc1_pre_inst_state                   false
% 7.85/1.50  --bmc1_pre_inst_reach_state             false
% 7.85/1.50  --bmc1_out_unsat_core                   false
% 7.85/1.50  --bmc1_aig_witness_out                  false
% 7.85/1.50  --bmc1_verbose                          false
% 7.85/1.50  --bmc1_dump_clauses_tptp                false
% 7.85/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.50  --bmc1_dump_file                        -
% 7.85/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.50  --bmc1_ucm_extend_mode                  1
% 7.85/1.50  --bmc1_ucm_init_mode                    2
% 7.85/1.50  --bmc1_ucm_cone_mode                    none
% 7.85/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.50  --bmc1_ucm_relax_model                  4
% 7.85/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.50  --bmc1_ucm_layered_model                none
% 7.85/1.50  --bmc1_ucm_max_lemma_size               10
% 7.85/1.50  
% 7.85/1.50  ------ AIG Options
% 7.85/1.50  
% 7.85/1.50  --aig_mode                              false
% 7.85/1.50  
% 7.85/1.50  ------ Instantiation Options
% 7.85/1.50  
% 7.85/1.50  --instantiation_flag                    true
% 7.85/1.50  --inst_sos_flag                         false
% 7.85/1.50  --inst_sos_phase                        true
% 7.85/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.50  --inst_lit_sel_side                     num_symb
% 7.85/1.50  --inst_solver_per_active                1400
% 7.85/1.50  --inst_solver_calls_frac                1.
% 7.85/1.50  --inst_passive_queue_type               priority_queues
% 7.85/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.50  --inst_passive_queues_freq              [25;2]
% 7.85/1.50  --inst_dismatching                      true
% 7.85/1.50  --inst_eager_unprocessed_to_passive     true
% 7.85/1.50  --inst_prop_sim_given                   true
% 7.85/1.50  --inst_prop_sim_new                     false
% 7.85/1.50  --inst_subs_new                         false
% 7.85/1.50  --inst_eq_res_simp                      false
% 7.85/1.50  --inst_subs_given                       false
% 7.85/1.50  --inst_orphan_elimination               true
% 7.85/1.50  --inst_learning_loop_flag               true
% 7.85/1.50  --inst_learning_start                   3000
% 7.85/1.50  --inst_learning_factor                  2
% 7.85/1.50  --inst_start_prop_sim_after_learn       3
% 7.85/1.50  --inst_sel_renew                        solver
% 7.85/1.50  --inst_lit_activity_flag                true
% 7.85/1.50  --inst_restr_to_given                   false
% 7.85/1.50  --inst_activity_threshold               500
% 7.85/1.50  --inst_out_proof                        true
% 7.85/1.50  
% 7.85/1.50  ------ Resolution Options
% 7.85/1.50  
% 7.85/1.50  --resolution_flag                       true
% 7.85/1.50  --res_lit_sel                           adaptive
% 7.85/1.50  --res_lit_sel_side                      none
% 7.85/1.50  --res_ordering                          kbo
% 7.85/1.50  --res_to_prop_solver                    active
% 7.85/1.50  --res_prop_simpl_new                    false
% 7.85/1.50  --res_prop_simpl_given                  true
% 7.85/1.50  --res_passive_queue_type                priority_queues
% 7.85/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.50  --res_passive_queues_freq               [15;5]
% 7.85/1.50  --res_forward_subs                      full
% 7.85/1.50  --res_backward_subs                     full
% 7.85/1.50  --res_forward_subs_resolution           true
% 7.85/1.50  --res_backward_subs_resolution          true
% 7.85/1.50  --res_orphan_elimination                true
% 7.85/1.50  --res_time_limit                        2.
% 7.85/1.50  --res_out_proof                         true
% 7.85/1.50  
% 7.85/1.50  ------ Superposition Options
% 7.85/1.50  
% 7.85/1.50  --superposition_flag                    true
% 7.85/1.50  --sup_passive_queue_type                priority_queues
% 7.85/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.50  --sup_passive_queues_freq               [1;4]
% 7.85/1.50  --demod_completeness_check              fast
% 7.85/1.50  --demod_use_ground                      true
% 7.85/1.50  --sup_to_prop_solver                    passive
% 7.85/1.50  --sup_prop_simpl_new                    true
% 7.85/1.50  --sup_prop_simpl_given                  true
% 7.85/1.50  --sup_fun_splitting                     false
% 7.85/1.50  --sup_smt_interval                      50000
% 7.85/1.50  
% 7.85/1.50  ------ Superposition Simplification Setup
% 7.85/1.50  
% 7.85/1.50  --sup_indices_passive                   []
% 7.85/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_full_bw                           [BwDemod]
% 7.85/1.50  --sup_immed_triv                        [TrivRules]
% 7.85/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_immed_bw_main                     []
% 7.85/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.85/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.85/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.85/1.50  
% 7.85/1.50  ------ Combination Options
% 7.85/1.50  
% 7.85/1.50  --comb_res_mult                         3
% 7.85/1.50  --comb_sup_mult                         2
% 7.85/1.50  --comb_inst_mult                        10
% 7.85/1.50  
% 7.85/1.50  ------ Debug Options
% 7.85/1.50  
% 7.85/1.50  --dbg_backtrace                         false
% 7.85/1.50  --dbg_dump_prop_clauses                 false
% 7.85/1.50  --dbg_dump_prop_clauses_file            -
% 7.85/1.50  --dbg_out_stat                          false
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  ------ Proving...
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  % SZS status Theorem for theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  fof(f1,axiom,(
% 7.85/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f16,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f1])).
% 7.85/1.50  
% 7.85/1.50  fof(f5,axiom,(
% 7.85/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f20,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.85/1.50    inference(cnf_transformation,[],[f5])).
% 7.85/1.50  
% 7.85/1.50  fof(f27,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.85/1.50    inference(definition_unfolding,[],[f16,f20,f20])).
% 7.85/1.50  
% 7.85/1.50  fof(f6,axiom,(
% 7.85/1.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f21,plain,(
% 7.85/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f6])).
% 7.85/1.50  
% 7.85/1.50  fof(f30,plain,(
% 7.85/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.85/1.50    inference(definition_unfolding,[],[f21,f20,f20])).
% 7.85/1.50  
% 7.85/1.50  fof(f2,axiom,(
% 7.85/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f17,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.85/1.50    inference(cnf_transformation,[],[f2])).
% 7.85/1.50  
% 7.85/1.50  fof(f26,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.85/1.50    inference(definition_unfolding,[],[f17,f20])).
% 7.85/1.50  
% 7.85/1.50  fof(f7,axiom,(
% 7.85/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f22,plain,(
% 7.85/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f7])).
% 7.85/1.50  
% 7.85/1.50  fof(f9,conjecture,(
% 7.85/1.50    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f10,negated_conjecture,(
% 7.85/1.50    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 7.85/1.50    inference(negated_conjecture,[],[f9])).
% 7.85/1.50  
% 7.85/1.50  fof(f13,plain,(
% 7.85/1.50    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 7.85/1.50    inference(ennf_transformation,[],[f10])).
% 7.85/1.50  
% 7.85/1.50  fof(f14,plain,(
% 7.85/1.50    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 7.85/1.50    introduced(choice_axiom,[])).
% 7.85/1.50  
% 7.85/1.50  fof(f15,plain,(
% 7.85/1.50    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 7.85/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 7.85/1.50  
% 7.85/1.50  fof(f25,plain,(
% 7.85/1.50    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.85/1.50    inference(cnf_transformation,[],[f15])).
% 7.85/1.50  
% 7.85/1.50  fof(f8,axiom,(
% 7.85/1.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f23,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f8])).
% 7.85/1.50  
% 7.85/1.50  fof(f31,plain,(
% 7.85/1.50    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 7.85/1.50    inference(definition_unfolding,[],[f25,f23,f20])).
% 7.85/1.50  
% 7.85/1.50  fof(f4,axiom,(
% 7.85/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.85/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.50  
% 7.85/1.50  fof(f12,plain,(
% 7.85/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.85/1.50    inference(ennf_transformation,[],[f4])).
% 7.85/1.50  
% 7.85/1.50  fof(f19,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.85/1.50    inference(cnf_transformation,[],[f12])).
% 7.85/1.50  
% 7.85/1.50  fof(f29,plain,(
% 7.85/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.85/1.50    inference(definition_unfolding,[],[f19,f20])).
% 7.85/1.50  
% 7.85/1.50  fof(f24,plain,(
% 7.85/1.50    r1_tarski(sK2,sK1)),
% 7.85/1.50    inference(cnf_transformation,[],[f15])).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1,plain,
% 7.85/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4,plain,
% 7.85/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.85/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_277,plain,
% 7.85/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_0,plain,
% 7.85/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.85/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_195,plain,
% 7.85/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_842,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_277,c_195]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_940,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_842,c_4]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5,plain,
% 7.85/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.85/1.50      inference(cnf_transformation,[],[f22]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_203,plain,
% 7.85/1.50      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2220,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_940,c_203]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2226,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 7.85/1.50      inference(light_normalisation,[status(thm)],[c_2220,c_4]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2227,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_2226,c_0]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6,negated_conjecture,
% 7.85/1.50      ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
% 7.85/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_129,plain,
% 7.85/1.50      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) != k4_xboole_0(sK0,sK2) ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_6,c_4]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_16007,plain,
% 7.85/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
% 7.85/1.50      inference(demodulation,[status(thm)],[c_2227,c_129]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_45,plain,
% 7.85/1.50      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_402,plain,
% 7.85/1.50      ( X0 != sK2
% 7.85/1.50      | X1 != sK0
% 7.85/1.50      | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_45]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9052,plain,
% 7.85/1.50      ( X0 != sK0
% 7.85/1.50      | k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2)
% 7.85/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_402]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9064,plain,
% 7.85/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
% 7.85/1.50      | k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2)
% 7.85/1.50      | sK0 != sK0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_9052]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_44,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_182,plain,
% 7.85/1.50      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_44]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1093,plain,
% 7.85/1.50      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 7.85/1.50      | X0 = sK2
% 7.85/1.50      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_182]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1688,plain,
% 7.85/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 7.85/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2
% 7.85/1.50      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1093]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_577,plain,
% 7.85/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_263,plain,
% 7.85/1.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_44]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_511,plain,
% 7.85/1.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_263]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_567,plain,
% 7.85/1.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != sK2
% 7.85/1.50      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 7.85/1.50      | sK2 != sK2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_511]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_43,plain,( X0 = X0 ),theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_177,plain,
% 7.85/1.50      ( sK2 = sK2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_43]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3,plain,
% 7.85/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.85/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_150,plain,
% 7.85/1.50      ( ~ r1_tarski(sK2,sK1)
% 7.85/1.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_52,plain,
% 7.85/1.50      ( sK0 = sK0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_43]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7,negated_conjecture,
% 7.85/1.50      ( r1_tarski(sK2,sK1) ),
% 7.85/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(contradiction,plain,
% 7.85/1.50      ( $false ),
% 7.85/1.50      inference(minisat,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_16007,c_9064,c_1688,c_577,c_567,c_177,c_150,c_52,c_7]) ).
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  ------                               Statistics
% 7.85/1.50  
% 7.85/1.50  ------ Selected
% 7.85/1.50  
% 7.85/1.50  total_time:                             0.943
% 7.85/1.50  
%------------------------------------------------------------------------------
