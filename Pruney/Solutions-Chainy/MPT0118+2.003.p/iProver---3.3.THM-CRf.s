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
% DateTime   : Thu Dec  3 11:26:08 EST 2020

% Result     : Theorem 14.85s
% Output     : CNFRefutation 14.85s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 399 expanded)
%              Number of clauses        :   40 ( 174 expanded)
%              Number of leaves         :    9 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :   70 ( 442 expanded)
%              Number of equality atoms :   62 ( 392 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f20,f15,f15])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f21,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f21,f15,f15])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_38,plain,
    ( X0 != X1
    | k3_xboole_0(X1,X2) != X3
    | k3_xboole_0(X3,X0) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_39,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_38])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_49,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_39,c_1,c_0])).

cnf(c_65,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_49])).

cnf(c_66,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_65,c_3])).

cnf(c_61,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_255,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_66,c_61])).

cnf(c_345,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_255])).

cnf(c_391,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_345,c_66])).

cnf(c_409,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_391,c_61])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_51,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0])).

cnf(c_1520,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3))) = k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3))) ),
    inference(superposition,[status(thm)],[c_409,c_51])).

cnf(c_143,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(superposition,[status(thm)],[c_1,c_51])).

cnf(c_144,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_1,c_51])).

cnf(c_153,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_144,c_1])).

cnf(c_154,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_143,c_153])).

cnf(c_274,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_61,c_51])).

cnf(c_350,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_61,c_255])).

cnf(c_60,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_207,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_66,c_60])).

cnf(c_314,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_207,c_60])).

cnf(c_387,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_350,c_314])).

cnf(c_134,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_62,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_673,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_134,c_62])).

cnf(c_693,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X0,X2),X3))) = k3_xboole_0(X3,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_673,c_387])).

cnf(c_1567,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_1520,c_3,c_154,c_274,c_387,c_693])).

cnf(c_104,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_51])).

cnf(c_6,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_50,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,k3_xboole_0(sK1,sK1)))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_1,c_0])).

cnf(c_67,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_66,c_50])).

cnf(c_14262,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_104,c_67])).

cnf(c_50420,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_1567,c_14262])).

cnf(c_50421,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_50420])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 14.85/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.85/2.49  
% 14.85/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.85/2.49  
% 14.85/2.49  ------  iProver source info
% 14.85/2.49  
% 14.85/2.49  git: date: 2020-06-30 10:37:57 +0100
% 14.85/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.85/2.49  git: non_committed_changes: false
% 14.85/2.49  git: last_make_outside_of_git: false
% 14.85/2.49  
% 14.85/2.49  ------ 
% 14.85/2.49  
% 14.85/2.49  ------ Input Options
% 14.85/2.49  
% 14.85/2.49  --out_options                           all
% 14.85/2.49  --tptp_safe_out                         true
% 14.85/2.49  --problem_path                          ""
% 14.85/2.49  --include_path                          ""
% 14.85/2.49  --clausifier                            res/vclausify_rel
% 14.85/2.49  --clausifier_options                    --mode clausify
% 14.85/2.49  --stdin                                 false
% 14.85/2.49  --stats_out                             all
% 14.85/2.49  
% 14.85/2.49  ------ General Options
% 14.85/2.49  
% 14.85/2.49  --fof                                   false
% 14.85/2.49  --time_out_real                         305.
% 14.85/2.49  --time_out_virtual                      -1.
% 14.85/2.49  --symbol_type_check                     false
% 14.85/2.49  --clausify_out                          false
% 14.85/2.49  --sig_cnt_out                           false
% 14.85/2.49  --trig_cnt_out                          false
% 14.85/2.49  --trig_cnt_out_tolerance                1.
% 14.85/2.49  --trig_cnt_out_sk_spl                   false
% 14.85/2.49  --abstr_cl_out                          false
% 14.85/2.49  
% 14.85/2.49  ------ Global Options
% 14.85/2.49  
% 14.85/2.49  --schedule                              default
% 14.85/2.49  --add_important_lit                     false
% 14.85/2.49  --prop_solver_per_cl                    1000
% 14.85/2.49  --min_unsat_core                        false
% 14.85/2.49  --soft_assumptions                      false
% 14.85/2.49  --soft_lemma_size                       3
% 14.85/2.49  --prop_impl_unit_size                   0
% 14.85/2.49  --prop_impl_unit                        []
% 14.85/2.49  --share_sel_clauses                     true
% 14.85/2.49  --reset_solvers                         false
% 14.85/2.49  --bc_imp_inh                            [conj_cone]
% 14.85/2.49  --conj_cone_tolerance                   3.
% 14.85/2.49  --extra_neg_conj                        none
% 14.85/2.49  --large_theory_mode                     true
% 14.85/2.49  --prolific_symb_bound                   200
% 14.85/2.49  --lt_threshold                          2000
% 14.85/2.49  --clause_weak_htbl                      true
% 14.85/2.49  --gc_record_bc_elim                     false
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing Options
% 14.85/2.49  
% 14.85/2.49  --preprocessing_flag                    true
% 14.85/2.49  --time_out_prep_mult                    0.1
% 14.85/2.49  --splitting_mode                        input
% 14.85/2.49  --splitting_grd                         true
% 14.85/2.49  --splitting_cvd                         false
% 14.85/2.49  --splitting_cvd_svl                     false
% 14.85/2.49  --splitting_nvd                         32
% 14.85/2.49  --sub_typing                            true
% 14.85/2.49  --prep_gs_sim                           true
% 14.85/2.49  --prep_unflatten                        true
% 14.85/2.49  --prep_res_sim                          true
% 14.85/2.49  --prep_upred                            true
% 14.85/2.49  --prep_sem_filter                       exhaustive
% 14.85/2.49  --prep_sem_filter_out                   false
% 14.85/2.49  --pred_elim                             true
% 14.85/2.49  --res_sim_input                         true
% 14.85/2.49  --eq_ax_congr_red                       true
% 14.85/2.49  --pure_diseq_elim                       true
% 14.85/2.49  --brand_transform                       false
% 14.85/2.49  --non_eq_to_eq                          false
% 14.85/2.49  --prep_def_merge                        true
% 14.85/2.49  --prep_def_merge_prop_impl              false
% 14.85/2.49  --prep_def_merge_mbd                    true
% 14.85/2.49  --prep_def_merge_tr_red                 false
% 14.85/2.49  --prep_def_merge_tr_cl                  false
% 14.85/2.49  --smt_preprocessing                     true
% 14.85/2.49  --smt_ac_axioms                         fast
% 14.85/2.49  --preprocessed_out                      false
% 14.85/2.49  --preprocessed_stats                    false
% 14.85/2.49  
% 14.85/2.49  ------ Abstraction refinement Options
% 14.85/2.49  
% 14.85/2.49  --abstr_ref                             []
% 14.85/2.49  --abstr_ref_prep                        false
% 14.85/2.49  --abstr_ref_until_sat                   false
% 14.85/2.49  --abstr_ref_sig_restrict                funpre
% 14.85/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.85/2.49  --abstr_ref_under                       []
% 14.85/2.49  
% 14.85/2.49  ------ SAT Options
% 14.85/2.49  
% 14.85/2.49  --sat_mode                              false
% 14.85/2.49  --sat_fm_restart_options                ""
% 14.85/2.49  --sat_gr_def                            false
% 14.85/2.49  --sat_epr_types                         true
% 14.85/2.49  --sat_non_cyclic_types                  false
% 14.85/2.49  --sat_finite_models                     false
% 14.85/2.49  --sat_fm_lemmas                         false
% 14.85/2.49  --sat_fm_prep                           false
% 14.85/2.49  --sat_fm_uc_incr                        true
% 14.85/2.49  --sat_out_model                         small
% 14.85/2.49  --sat_out_clauses                       false
% 14.85/2.49  
% 14.85/2.49  ------ QBF Options
% 14.85/2.49  
% 14.85/2.49  --qbf_mode                              false
% 14.85/2.49  --qbf_elim_univ                         false
% 14.85/2.49  --qbf_dom_inst                          none
% 14.85/2.49  --qbf_dom_pre_inst                      false
% 14.85/2.49  --qbf_sk_in                             false
% 14.85/2.49  --qbf_pred_elim                         true
% 14.85/2.49  --qbf_split                             512
% 14.85/2.49  
% 14.85/2.49  ------ BMC1 Options
% 14.85/2.49  
% 14.85/2.49  --bmc1_incremental                      false
% 14.85/2.49  --bmc1_axioms                           reachable_all
% 14.85/2.49  --bmc1_min_bound                        0
% 14.85/2.49  --bmc1_max_bound                        -1
% 14.85/2.49  --bmc1_max_bound_default                -1
% 14.85/2.49  --bmc1_symbol_reachability              true
% 14.85/2.49  --bmc1_property_lemmas                  false
% 14.85/2.49  --bmc1_k_induction                      false
% 14.85/2.49  --bmc1_non_equiv_states                 false
% 14.85/2.49  --bmc1_deadlock                         false
% 14.85/2.49  --bmc1_ucm                              false
% 14.85/2.49  --bmc1_add_unsat_core                   none
% 14.85/2.49  --bmc1_unsat_core_children              false
% 14.85/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.85/2.49  --bmc1_out_stat                         full
% 14.85/2.49  --bmc1_ground_init                      false
% 14.85/2.49  --bmc1_pre_inst_next_state              false
% 14.85/2.49  --bmc1_pre_inst_state                   false
% 14.85/2.49  --bmc1_pre_inst_reach_state             false
% 14.85/2.49  --bmc1_out_unsat_core                   false
% 14.85/2.49  --bmc1_aig_witness_out                  false
% 14.85/2.49  --bmc1_verbose                          false
% 14.85/2.49  --bmc1_dump_clauses_tptp                false
% 14.85/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.85/2.49  --bmc1_dump_file                        -
% 14.85/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.85/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.85/2.49  --bmc1_ucm_extend_mode                  1
% 14.85/2.49  --bmc1_ucm_init_mode                    2
% 14.85/2.49  --bmc1_ucm_cone_mode                    none
% 14.85/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.85/2.49  --bmc1_ucm_relax_model                  4
% 14.85/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.85/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.85/2.49  --bmc1_ucm_layered_model                none
% 14.85/2.49  --bmc1_ucm_max_lemma_size               10
% 14.85/2.49  
% 14.85/2.49  ------ AIG Options
% 14.85/2.49  
% 14.85/2.49  --aig_mode                              false
% 14.85/2.49  
% 14.85/2.49  ------ Instantiation Options
% 14.85/2.49  
% 14.85/2.49  --instantiation_flag                    true
% 14.85/2.49  --inst_sos_flag                         false
% 14.85/2.49  --inst_sos_phase                        true
% 14.85/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.85/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.85/2.49  --inst_lit_sel_side                     num_symb
% 14.85/2.49  --inst_solver_per_active                1400
% 14.85/2.49  --inst_solver_calls_frac                1.
% 14.85/2.49  --inst_passive_queue_type               priority_queues
% 14.85/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.85/2.49  --inst_passive_queues_freq              [25;2]
% 14.85/2.49  --inst_dismatching                      true
% 14.85/2.49  --inst_eager_unprocessed_to_passive     true
% 14.85/2.49  --inst_prop_sim_given                   true
% 14.85/2.49  --inst_prop_sim_new                     false
% 14.85/2.49  --inst_subs_new                         false
% 14.85/2.49  --inst_eq_res_simp                      false
% 14.85/2.49  --inst_subs_given                       false
% 14.85/2.49  --inst_orphan_elimination               true
% 14.85/2.49  --inst_learning_loop_flag               true
% 14.85/2.49  --inst_learning_start                   3000
% 14.85/2.49  --inst_learning_factor                  2
% 14.85/2.49  --inst_start_prop_sim_after_learn       3
% 14.85/2.49  --inst_sel_renew                        solver
% 14.85/2.49  --inst_lit_activity_flag                true
% 14.85/2.49  --inst_restr_to_given                   false
% 14.85/2.49  --inst_activity_threshold               500
% 14.85/2.49  --inst_out_proof                        true
% 14.85/2.49  
% 14.85/2.49  ------ Resolution Options
% 14.85/2.49  
% 14.85/2.49  --resolution_flag                       true
% 14.85/2.49  --res_lit_sel                           adaptive
% 14.85/2.49  --res_lit_sel_side                      none
% 14.85/2.49  --res_ordering                          kbo
% 14.85/2.49  --res_to_prop_solver                    active
% 14.85/2.49  --res_prop_simpl_new                    false
% 14.85/2.49  --res_prop_simpl_given                  true
% 14.85/2.49  --res_passive_queue_type                priority_queues
% 14.85/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.85/2.49  --res_passive_queues_freq               [15;5]
% 14.85/2.49  --res_forward_subs                      full
% 14.85/2.49  --res_backward_subs                     full
% 14.85/2.49  --res_forward_subs_resolution           true
% 14.85/2.49  --res_backward_subs_resolution          true
% 14.85/2.49  --res_orphan_elimination                true
% 14.85/2.49  --res_time_limit                        2.
% 14.85/2.49  --res_out_proof                         true
% 14.85/2.49  
% 14.85/2.49  ------ Superposition Options
% 14.85/2.49  
% 14.85/2.49  --superposition_flag                    true
% 14.85/2.49  --sup_passive_queue_type                priority_queues
% 14.85/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.85/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.85/2.49  --demod_completeness_check              fast
% 14.85/2.49  --demod_use_ground                      true
% 14.85/2.49  --sup_to_prop_solver                    passive
% 14.85/2.49  --sup_prop_simpl_new                    true
% 14.85/2.49  --sup_prop_simpl_given                  true
% 14.85/2.49  --sup_fun_splitting                     false
% 14.85/2.49  --sup_smt_interval                      50000
% 14.85/2.49  
% 14.85/2.49  ------ Superposition Simplification Setup
% 14.85/2.49  
% 14.85/2.49  --sup_indices_passive                   []
% 14.85/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.85/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.85/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.85/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 14.85/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.85/2.49  --sup_full_bw                           [BwDemod]
% 14.85/2.49  --sup_immed_triv                        [TrivRules]
% 14.85/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.85/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.85/2.49  --sup_immed_bw_main                     []
% 14.85/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.85/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.85/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.85/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.85/2.49  
% 14.85/2.49  ------ Combination Options
% 14.85/2.49  
% 14.85/2.49  --comb_res_mult                         3
% 14.85/2.49  --comb_sup_mult                         2
% 14.85/2.49  --comb_inst_mult                        10
% 14.85/2.49  
% 14.85/2.49  ------ Debug Options
% 14.85/2.49  
% 14.85/2.49  --dbg_backtrace                         false
% 14.85/2.49  --dbg_dump_prop_clauses                 false
% 14.85/2.49  --dbg_dump_prop_clauses_file            -
% 14.85/2.49  --dbg_out_stat                          false
% 14.85/2.49  ------ Parsing...
% 14.85/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.85/2.49  ------ Proving...
% 14.85/2.49  ------ Problem Properties 
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  clauses                                 6
% 14.85/2.49  conjectures                             1
% 14.85/2.49  EPR                                     0
% 14.85/2.49  Horn                                    6
% 14.85/2.49  unary                                   6
% 14.85/2.49  binary                                  0
% 14.85/2.49  lits                                    6
% 14.85/2.49  lits eq                                 6
% 14.85/2.49  fd_pure                                 0
% 14.85/2.49  fd_pseudo                               0
% 14.85/2.49  fd_cond                                 0
% 14.85/2.49  fd_pseudo_cond                          0
% 14.85/2.49  AC symbols                              1
% 14.85/2.49  
% 14.85/2.49  ------ Schedule UEQ
% 14.85/2.49  
% 14.85/2.49  ------ pure equality problem: resolution off 
% 14.85/2.49  
% 14.85/2.49  ------ Option_UEQ Time Limit: Unbounded
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  ------ 
% 14.85/2.49  Current options:
% 14.85/2.49  ------ 
% 14.85/2.49  
% 14.85/2.49  ------ Input Options
% 14.85/2.49  
% 14.85/2.49  --out_options                           all
% 14.85/2.49  --tptp_safe_out                         true
% 14.85/2.49  --problem_path                          ""
% 14.85/2.49  --include_path                          ""
% 14.85/2.49  --clausifier                            res/vclausify_rel
% 14.85/2.49  --clausifier_options                    --mode clausify
% 14.85/2.49  --stdin                                 false
% 14.85/2.49  --stats_out                             all
% 14.85/2.49  
% 14.85/2.49  ------ General Options
% 14.85/2.49  
% 14.85/2.49  --fof                                   false
% 14.85/2.49  --time_out_real                         305.
% 14.85/2.49  --time_out_virtual                      -1.
% 14.85/2.49  --symbol_type_check                     false
% 14.85/2.49  --clausify_out                          false
% 14.85/2.49  --sig_cnt_out                           false
% 14.85/2.49  --trig_cnt_out                          false
% 14.85/2.49  --trig_cnt_out_tolerance                1.
% 14.85/2.49  --trig_cnt_out_sk_spl                   false
% 14.85/2.49  --abstr_cl_out                          false
% 14.85/2.49  
% 14.85/2.49  ------ Global Options
% 14.85/2.49  
% 14.85/2.49  --schedule                              default
% 14.85/2.49  --add_important_lit                     false
% 14.85/2.49  --prop_solver_per_cl                    1000
% 14.85/2.49  --min_unsat_core                        false
% 14.85/2.49  --soft_assumptions                      false
% 14.85/2.49  --soft_lemma_size                       3
% 14.85/2.49  --prop_impl_unit_size                   0
% 14.85/2.49  --prop_impl_unit                        []
% 14.85/2.49  --share_sel_clauses                     true
% 14.85/2.49  --reset_solvers                         false
% 14.85/2.49  --bc_imp_inh                            [conj_cone]
% 14.85/2.49  --conj_cone_tolerance                   3.
% 14.85/2.49  --extra_neg_conj                        none
% 14.85/2.49  --large_theory_mode                     true
% 14.85/2.49  --prolific_symb_bound                   200
% 14.85/2.49  --lt_threshold                          2000
% 14.85/2.49  --clause_weak_htbl                      true
% 14.85/2.49  --gc_record_bc_elim                     false
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing Options
% 14.85/2.49  
% 14.85/2.49  --preprocessing_flag                    true
% 14.85/2.49  --time_out_prep_mult                    0.1
% 14.85/2.49  --splitting_mode                        input
% 14.85/2.49  --splitting_grd                         true
% 14.85/2.49  --splitting_cvd                         false
% 14.85/2.49  --splitting_cvd_svl                     false
% 14.85/2.49  --splitting_nvd                         32
% 14.85/2.49  --sub_typing                            true
% 14.85/2.49  --prep_gs_sim                           true
% 14.85/2.49  --prep_unflatten                        true
% 14.85/2.49  --prep_res_sim                          true
% 14.85/2.49  --prep_upred                            true
% 14.85/2.49  --prep_sem_filter                       exhaustive
% 14.85/2.49  --prep_sem_filter_out                   false
% 14.85/2.49  --pred_elim                             true
% 14.85/2.49  --res_sim_input                         true
% 14.85/2.49  --eq_ax_congr_red                       true
% 14.85/2.49  --pure_diseq_elim                       true
% 14.85/2.49  --brand_transform                       false
% 14.85/2.49  --non_eq_to_eq                          false
% 14.85/2.49  --prep_def_merge                        true
% 14.85/2.49  --prep_def_merge_prop_impl              false
% 14.85/2.49  --prep_def_merge_mbd                    true
% 14.85/2.49  --prep_def_merge_tr_red                 false
% 14.85/2.49  --prep_def_merge_tr_cl                  false
% 14.85/2.49  --smt_preprocessing                     true
% 14.85/2.49  --smt_ac_axioms                         fast
% 14.85/2.49  --preprocessed_out                      false
% 14.85/2.49  --preprocessed_stats                    false
% 14.85/2.49  
% 14.85/2.49  ------ Abstraction refinement Options
% 14.85/2.49  
% 14.85/2.49  --abstr_ref                             []
% 14.85/2.49  --abstr_ref_prep                        false
% 14.85/2.49  --abstr_ref_until_sat                   false
% 14.85/2.49  --abstr_ref_sig_restrict                funpre
% 14.85/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.85/2.49  --abstr_ref_under                       []
% 14.85/2.49  
% 14.85/2.49  ------ SAT Options
% 14.85/2.49  
% 14.85/2.49  --sat_mode                              false
% 14.85/2.49  --sat_fm_restart_options                ""
% 14.85/2.49  --sat_gr_def                            false
% 14.85/2.49  --sat_epr_types                         true
% 14.85/2.49  --sat_non_cyclic_types                  false
% 14.85/2.49  --sat_finite_models                     false
% 14.85/2.49  --sat_fm_lemmas                         false
% 14.85/2.49  --sat_fm_prep                           false
% 14.85/2.49  --sat_fm_uc_incr                        true
% 14.85/2.49  --sat_out_model                         small
% 14.85/2.49  --sat_out_clauses                       false
% 14.85/2.49  
% 14.85/2.49  ------ QBF Options
% 14.85/2.49  
% 14.85/2.49  --qbf_mode                              false
% 14.85/2.49  --qbf_elim_univ                         false
% 14.85/2.49  --qbf_dom_inst                          none
% 14.85/2.49  --qbf_dom_pre_inst                      false
% 14.85/2.49  --qbf_sk_in                             false
% 14.85/2.49  --qbf_pred_elim                         true
% 14.85/2.49  --qbf_split                             512
% 14.85/2.49  
% 14.85/2.49  ------ BMC1 Options
% 14.85/2.49  
% 14.85/2.49  --bmc1_incremental                      false
% 14.85/2.49  --bmc1_axioms                           reachable_all
% 14.85/2.49  --bmc1_min_bound                        0
% 14.85/2.49  --bmc1_max_bound                        -1
% 14.85/2.49  --bmc1_max_bound_default                -1
% 14.85/2.49  --bmc1_symbol_reachability              true
% 14.85/2.49  --bmc1_property_lemmas                  false
% 14.85/2.49  --bmc1_k_induction                      false
% 14.85/2.49  --bmc1_non_equiv_states                 false
% 14.85/2.49  --bmc1_deadlock                         false
% 14.85/2.49  --bmc1_ucm                              false
% 14.85/2.49  --bmc1_add_unsat_core                   none
% 14.85/2.49  --bmc1_unsat_core_children              false
% 14.85/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.85/2.49  --bmc1_out_stat                         full
% 14.85/2.49  --bmc1_ground_init                      false
% 14.85/2.49  --bmc1_pre_inst_next_state              false
% 14.85/2.49  --bmc1_pre_inst_state                   false
% 14.85/2.49  --bmc1_pre_inst_reach_state             false
% 14.85/2.49  --bmc1_out_unsat_core                   false
% 14.85/2.49  --bmc1_aig_witness_out                  false
% 14.85/2.49  --bmc1_verbose                          false
% 14.85/2.49  --bmc1_dump_clauses_tptp                false
% 14.85/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.85/2.49  --bmc1_dump_file                        -
% 14.85/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.85/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.85/2.49  --bmc1_ucm_extend_mode                  1
% 14.85/2.49  --bmc1_ucm_init_mode                    2
% 14.85/2.49  --bmc1_ucm_cone_mode                    none
% 14.85/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.85/2.49  --bmc1_ucm_relax_model                  4
% 14.85/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.85/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.85/2.49  --bmc1_ucm_layered_model                none
% 14.85/2.49  --bmc1_ucm_max_lemma_size               10
% 14.85/2.49  
% 14.85/2.49  ------ AIG Options
% 14.85/2.49  
% 14.85/2.49  --aig_mode                              false
% 14.85/2.49  
% 14.85/2.49  ------ Instantiation Options
% 14.85/2.49  
% 14.85/2.49  --instantiation_flag                    false
% 14.85/2.49  --inst_sos_flag                         false
% 14.85/2.49  --inst_sos_phase                        true
% 14.85/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.85/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.85/2.49  --inst_lit_sel_side                     num_symb
% 14.85/2.49  --inst_solver_per_active                1400
% 14.85/2.49  --inst_solver_calls_frac                1.
% 14.85/2.49  --inst_passive_queue_type               priority_queues
% 14.85/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.85/2.49  --inst_passive_queues_freq              [25;2]
% 14.85/2.49  --inst_dismatching                      true
% 14.85/2.49  --inst_eager_unprocessed_to_passive     true
% 14.85/2.49  --inst_prop_sim_given                   true
% 14.85/2.49  --inst_prop_sim_new                     false
% 14.85/2.49  --inst_subs_new                         false
% 14.85/2.49  --inst_eq_res_simp                      false
% 14.85/2.49  --inst_subs_given                       false
% 14.85/2.49  --inst_orphan_elimination               true
% 14.85/2.49  --inst_learning_loop_flag               true
% 14.85/2.49  --inst_learning_start                   3000
% 14.85/2.49  --inst_learning_factor                  2
% 14.85/2.49  --inst_start_prop_sim_after_learn       3
% 14.85/2.49  --inst_sel_renew                        solver
% 14.85/2.49  --inst_lit_activity_flag                true
% 14.85/2.49  --inst_restr_to_given                   false
% 14.85/2.49  --inst_activity_threshold               500
% 14.85/2.49  --inst_out_proof                        true
% 14.85/2.49  
% 14.85/2.49  ------ Resolution Options
% 14.85/2.49  
% 14.85/2.49  --resolution_flag                       false
% 14.85/2.49  --res_lit_sel                           adaptive
% 14.85/2.49  --res_lit_sel_side                      none
% 14.85/2.49  --res_ordering                          kbo
% 14.85/2.49  --res_to_prop_solver                    active
% 14.85/2.49  --res_prop_simpl_new                    false
% 14.85/2.49  --res_prop_simpl_given                  true
% 14.85/2.49  --res_passive_queue_type                priority_queues
% 14.85/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.85/2.49  --res_passive_queues_freq               [15;5]
% 14.85/2.49  --res_forward_subs                      full
% 14.85/2.49  --res_backward_subs                     full
% 14.85/2.49  --res_forward_subs_resolution           true
% 14.85/2.49  --res_backward_subs_resolution          true
% 14.85/2.49  --res_orphan_elimination                true
% 14.85/2.49  --res_time_limit                        2.
% 14.85/2.49  --res_out_proof                         true
% 14.85/2.49  
% 14.85/2.49  ------ Superposition Options
% 14.85/2.49  
% 14.85/2.49  --superposition_flag                    true
% 14.85/2.49  --sup_passive_queue_type                priority_queues
% 14.85/2.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.85/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.85/2.49  --demod_completeness_check              fast
% 14.85/2.49  --demod_use_ground                      true
% 14.85/2.49  --sup_to_prop_solver                    active
% 14.85/2.49  --sup_prop_simpl_new                    false
% 14.85/2.49  --sup_prop_simpl_given                  false
% 14.85/2.49  --sup_fun_splitting                     true
% 14.85/2.49  --sup_smt_interval                      10000
% 14.85/2.49  
% 14.85/2.49  ------ Superposition Simplification Setup
% 14.85/2.49  
% 14.85/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.85/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.85/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.85/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.85/2.49  --sup_full_triv                         [TrivRules]
% 14.85/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.85/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.85/2.49  --sup_immed_triv                        [TrivRules]
% 14.85/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.85/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.85/2.49  --sup_immed_bw_main                     []
% 14.85/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.85/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.85/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.85/2.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 14.85/2.49  
% 14.85/2.49  ------ Combination Options
% 14.85/2.49  
% 14.85/2.49  --comb_res_mult                         1
% 14.85/2.49  --comb_sup_mult                         1
% 14.85/2.49  --comb_inst_mult                        1000000
% 14.85/2.49  
% 14.85/2.49  ------ Debug Options
% 14.85/2.49  
% 14.85/2.49  --dbg_backtrace                         false
% 14.85/2.49  --dbg_dump_prop_clauses                 false
% 14.85/2.49  --dbg_dump_prop_clauses_file            -
% 14.85/2.49  --dbg_out_stat                          false
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  ------ Proving...
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  % SZS status Theorem for theBenchmark.p
% 14.85/2.49  
% 14.85/2.49   Resolution empty clause
% 14.85/2.49  
% 14.85/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 14.85/2.49  
% 14.85/2.49  fof(f5,axiom,(
% 14.85/2.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f18,plain,(
% 14.85/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 14.85/2.49    inference(cnf_transformation,[],[f5])).
% 14.85/2.49  
% 14.85/2.49  fof(f4,axiom,(
% 14.85/2.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f17,plain,(
% 14.85/2.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 14.85/2.49    inference(cnf_transformation,[],[f4])).
% 14.85/2.49  
% 14.85/2.49  fof(f6,axiom,(
% 14.85/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f10,plain,(
% 14.85/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 14.85/2.49    inference(ennf_transformation,[],[f6])).
% 14.85/2.49  
% 14.85/2.49  fof(f19,plain,(
% 14.85/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 14.85/2.49    inference(cnf_transformation,[],[f10])).
% 14.85/2.49  
% 14.85/2.49  fof(f3,axiom,(
% 14.85/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f16,plain,(
% 14.85/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 14.85/2.49    inference(cnf_transformation,[],[f3])).
% 14.85/2.49  
% 14.85/2.49  fof(f1,axiom,(
% 14.85/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f14,plain,(
% 14.85/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.85/2.49    inference(cnf_transformation,[],[f1])).
% 14.85/2.49  
% 14.85/2.49  fof(f7,axiom,(
% 14.85/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f20,plain,(
% 14.85/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 14.85/2.49    inference(cnf_transformation,[],[f7])).
% 14.85/2.49  
% 14.85/2.49  fof(f2,axiom,(
% 14.85/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f15,plain,(
% 14.85/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.85/2.49    inference(cnf_transformation,[],[f2])).
% 14.85/2.49  
% 14.85/2.49  fof(f22,plain,(
% 14.85/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 14.85/2.49    inference(definition_unfolding,[],[f20,f15,f15])).
% 14.85/2.49  
% 14.85/2.49  fof(f8,conjecture,(
% 14.85/2.49    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 14.85/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.85/2.49  
% 14.85/2.49  fof(f9,negated_conjecture,(
% 14.85/2.49    ~! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 14.85/2.49    inference(negated_conjecture,[],[f8])).
% 14.85/2.49  
% 14.85/2.49  fof(f11,plain,(
% 14.85/2.49    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 14.85/2.49    inference(ennf_transformation,[],[f9])).
% 14.85/2.49  
% 14.85/2.49  fof(f12,plain,(
% 14.85/2.49    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) => k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 14.85/2.49    introduced(choice_axiom,[])).
% 14.85/2.49  
% 14.85/2.49  fof(f13,plain,(
% 14.85/2.49    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 14.85/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 14.85/2.49  
% 14.85/2.49  fof(f21,plain,(
% 14.85/2.49    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 14.85/2.49    inference(cnf_transformation,[],[f13])).
% 14.85/2.49  
% 14.85/2.49  fof(f23,plain,(
% 14.85/2.49    k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)))),
% 14.85/2.49    inference(definition_unfolding,[],[f21,f15,f15])).
% 14.85/2.49  
% 14.85/2.49  cnf(c_3,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 14.85/2.49      inference(cnf_transformation,[],[f18]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_2,plain,
% 14.85/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 14.85/2.49      inference(cnf_transformation,[],[f17]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_4,plain,
% 14.85/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 14.85/2.49      inference(cnf_transformation,[],[f19]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_38,plain,
% 14.85/2.49      ( X0 != X1 | k3_xboole_0(X1,X2) != X3 | k3_xboole_0(X3,X0) = X3 ),
% 14.85/2.49      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_39,plain,
% 14.85/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 14.85/2.49      inference(unflattening,[status(thm)],[c_38]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_1,plain,
% 14.85/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 14.85/2.49      inference(cnf_transformation,[],[f16]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_0,plain,
% 14.85/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 14.85/2.49      inference(cnf_transformation,[],[f14]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_49,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 14.85/2.49      inference(theory_normalisation,[status(thm)],[c_39,c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_65,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_3,c_49]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_66,plain,
% 14.85/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 14.85/2.49      inference(light_normalisation,[status(thm)],[c_65,c_3]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_61,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_255,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_66,c_61]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_345,plain,
% 14.85/2.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_3,c_255]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_391,plain,
% 14.85/2.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 14.85/2.49      inference(light_normalisation,[status(thm)],[c_345,c_66]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_409,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X2,X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_391,c_61]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_5,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 14.85/2.49      inference(cnf_transformation,[],[f22]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_51,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 14.85/2.49      inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_1520,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3))) = k5_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3))) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_409,c_51]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_143,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_1,c_51]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_144,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_1,c_51]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_153,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 14.85/2.49      inference(light_normalisation,[status(thm)],[c_144,c_1]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_154,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 14.85/2.49      inference(demodulation,[status(thm)],[c_143,c_153]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_274,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_61,c_51]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_350,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_61,c_255]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_60,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_207,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_66,c_60]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_314,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X0))) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_207,c_60]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_387,plain,
% 14.85/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 14.85/2.49      inference(light_normalisation,[status(thm)],[c_350,c_314]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_134,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_62,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_673,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X0,X2)) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_134,c_62]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_693,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k2_xboole_0(X0,X2),X3))) = k3_xboole_0(X3,k3_xboole_0(X0,X1)) ),
% 14.85/2.49      inference(demodulation,[status(thm)],[c_673,c_387]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_1567,plain,
% 14.85/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 14.85/2.49      inference(demodulation,
% 14.85/2.49                [status(thm)],
% 14.85/2.49                [c_1520,c_3,c_154,c_274,c_387,c_693]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_104,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 14.85/2.49      inference(superposition,[status(thm)],[c_0,c_51]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_6,negated_conjecture,
% 14.85/2.49      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
% 14.85/2.49      inference(cnf_transformation,[],[f23]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_50,negated_conjecture,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,k3_xboole_0(sK1,sK1)))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 14.85/2.49      inference(theory_normalisation,[status(thm)],[c_6,c_1,c_0]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_67,plain,
% 14.85/2.49      ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 14.85/2.49      inference(demodulation,[status(thm)],[c_66,c_50]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_14262,plain,
% 14.85/2.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 14.85/2.49      inference(demodulation,[status(thm)],[c_104,c_67]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_50420,plain,
% 14.85/2.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 14.85/2.49      inference(demodulation,[status(thm)],[c_1567,c_14262]) ).
% 14.85/2.49  
% 14.85/2.49  cnf(c_50421,plain,
% 14.85/2.49      ( $false ),
% 14.85/2.49      inference(theory_normalisation,[status(thm)],[c_50420]) ).
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 14.85/2.49  
% 14.85/2.49  ------                               Statistics
% 14.85/2.49  
% 14.85/2.49  ------ General
% 14.85/2.49  
% 14.85/2.49  abstr_ref_over_cycles:                  0
% 14.85/2.49  abstr_ref_under_cycles:                 0
% 14.85/2.49  gc_basic_clause_elim:                   0
% 14.85/2.49  forced_gc_time:                         0
% 14.85/2.49  parsing_time:                           0.009
% 14.85/2.49  unif_index_cands_time:                  0.
% 14.85/2.49  unif_index_add_time:                    0.
% 14.85/2.49  orderings_time:                         0.
% 14.85/2.49  out_proof_time:                         0.008
% 14.85/2.49  total_time:                             1.528
% 14.85/2.49  num_of_symbols:                         38
% 14.85/2.49  num_of_terms:                           74879
% 14.85/2.49  
% 14.85/2.49  ------ Preprocessing
% 14.85/2.49  
% 14.85/2.49  num_of_splits:                          0
% 14.85/2.49  num_of_split_atoms:                     0
% 14.85/2.49  num_of_reused_defs:                     0
% 14.85/2.49  num_eq_ax_congr_red:                    7
% 14.85/2.49  num_of_sem_filtered_clauses:            0
% 14.85/2.49  num_of_subtypes:                        0
% 14.85/2.49  monotx_restored_types:                  0
% 14.85/2.49  sat_num_of_epr_types:                   0
% 14.85/2.49  sat_num_of_non_cyclic_types:            0
% 14.85/2.49  sat_guarded_non_collapsed_types:        0
% 14.85/2.49  num_pure_diseq_elim:                    0
% 14.85/2.49  simp_replaced_by:                       0
% 14.85/2.49  res_preprocessed:                       23
% 14.85/2.49  prep_upred:                             0
% 14.85/2.49  prep_unflattend:                        2
% 14.85/2.49  smt_new_axioms:                         0
% 14.85/2.49  pred_elim_cands:                        0
% 14.85/2.49  pred_elim:                              1
% 14.85/2.49  pred_elim_cl:                           1
% 14.85/2.49  pred_elim_cycles:                       2
% 14.85/2.49  merged_defs:                            0
% 14.85/2.49  merged_defs_ncl:                        0
% 14.85/2.49  bin_hyper_res:                          0
% 14.85/2.49  prep_cycles:                            3
% 14.85/2.49  pred_elim_time:                         0.
% 14.85/2.49  splitting_time:                         0.
% 14.85/2.49  sem_filter_time:                        0.
% 14.85/2.49  monotx_time:                            0.001
% 14.85/2.49  subtype_inf_time:                       0.
% 14.85/2.49  
% 14.85/2.49  ------ Problem properties
% 14.85/2.49  
% 14.85/2.49  clauses:                                6
% 14.85/2.49  conjectures:                            1
% 14.85/2.49  epr:                                    0
% 14.85/2.49  horn:                                   6
% 14.85/2.49  ground:                                 1
% 14.85/2.49  unary:                                  6
% 14.85/2.49  binary:                                 0
% 14.85/2.49  lits:                                   6
% 14.85/2.49  lits_eq:                                6
% 14.85/2.49  fd_pure:                                0
% 14.85/2.49  fd_pseudo:                              0
% 14.85/2.49  fd_cond:                                0
% 14.85/2.49  fd_pseudo_cond:                         0
% 14.85/2.49  ac_symbols:                             1
% 14.85/2.49  
% 14.85/2.49  ------ Propositional Solver
% 14.85/2.49  
% 14.85/2.49  prop_solver_calls:                      17
% 14.85/2.49  prop_fast_solver_calls:                 61
% 14.85/2.49  smt_solver_calls:                       0
% 14.85/2.49  smt_fast_solver_calls:                  0
% 14.85/2.49  prop_num_of_clauses:                    227
% 14.85/2.49  prop_preprocess_simplified:             409
% 14.85/2.49  prop_fo_subsumed:                       0
% 14.85/2.49  prop_solver_time:                       0.
% 14.85/2.49  smt_solver_time:                        0.
% 14.85/2.49  smt_fast_solver_time:                   0.
% 14.85/2.49  prop_fast_solver_time:                  0.
% 14.85/2.49  prop_unsat_core_time:                   0.
% 14.85/2.49  
% 14.85/2.49  ------ QBF
% 14.85/2.49  
% 14.85/2.49  qbf_q_res:                              0
% 14.85/2.49  qbf_num_tautologies:                    0
% 14.85/2.49  qbf_prep_cycles:                        0
% 14.85/2.49  
% 14.85/2.49  ------ BMC1
% 14.85/2.49  
% 14.85/2.49  bmc1_current_bound:                     -1
% 14.85/2.49  bmc1_last_solved_bound:                 -1
% 14.85/2.49  bmc1_unsat_core_size:                   -1
% 14.85/2.49  bmc1_unsat_core_parents_size:           -1
% 14.85/2.49  bmc1_merge_next_fun:                    0
% 14.85/2.49  bmc1_unsat_core_clauses_time:           0.
% 14.85/2.49  
% 14.85/2.49  ------ Instantiation
% 14.85/2.49  
% 14.85/2.49  inst_num_of_clauses:                    0
% 14.85/2.49  inst_num_in_passive:                    0
% 14.85/2.49  inst_num_in_active:                     0
% 14.85/2.49  inst_num_in_unprocessed:                0
% 14.85/2.49  inst_num_of_loops:                      0
% 14.85/2.49  inst_num_of_learning_restarts:          0
% 14.85/2.49  inst_num_moves_active_passive:          0
% 14.85/2.49  inst_lit_activity:                      0
% 14.85/2.49  inst_lit_activity_moves:                0
% 14.85/2.49  inst_num_tautologies:                   0
% 14.85/2.49  inst_num_prop_implied:                  0
% 14.85/2.49  inst_num_existing_simplified:           0
% 14.85/2.49  inst_num_eq_res_simplified:             0
% 14.85/2.49  inst_num_child_elim:                    0
% 14.85/2.49  inst_num_of_dismatching_blockings:      0
% 14.85/2.49  inst_num_of_non_proper_insts:           0
% 14.85/2.49  inst_num_of_duplicates:                 0
% 14.85/2.49  inst_inst_num_from_inst_to_res:         0
% 14.85/2.49  inst_dismatching_checking_time:         0.
% 14.85/2.49  
% 14.85/2.49  ------ Resolution
% 14.85/2.49  
% 14.85/2.49  res_num_of_clauses:                     0
% 14.85/2.49  res_num_in_passive:                     0
% 14.85/2.49  res_num_in_active:                      0
% 14.85/2.49  res_num_of_loops:                       26
% 14.85/2.49  res_forward_subset_subsumed:            0
% 14.85/2.49  res_backward_subset_subsumed:           0
% 14.85/2.49  res_forward_subsumed:                   0
% 14.85/2.49  res_backward_subsumed:                  0
% 14.85/2.49  res_forward_subsumption_resolution:     0
% 14.85/2.49  res_backward_subsumption_resolution:    0
% 14.85/2.49  res_clause_to_clause_subsumption:       254091
% 14.85/2.49  res_orphan_elimination:                 0
% 14.85/2.49  res_tautology_del:                      0
% 14.85/2.49  res_num_eq_res_simplified:              0
% 14.85/2.49  res_num_sel_changes:                    0
% 14.85/2.49  res_moves_from_active_to_pass:          0
% 14.85/2.49  
% 14.85/2.49  ------ Superposition
% 14.85/2.49  
% 14.85/2.49  sup_time_total:                         0.
% 14.85/2.49  sup_time_generating:                    0.
% 14.85/2.49  sup_time_sim_full:                      0.
% 14.85/2.49  sup_time_sim_immed:                     0.
% 14.85/2.49  
% 14.85/2.49  sup_num_of_clauses:                     4600
% 14.85/2.49  sup_num_in_active:                      144
% 14.85/2.49  sup_num_in_passive:                     4456
% 14.85/2.49  sup_num_of_loops:                       147
% 14.85/2.49  sup_fw_superposition:                   17670
% 14.85/2.49  sup_bw_superposition:                   12454
% 14.85/2.49  sup_immediate_simplified:               18550
% 14.85/2.49  sup_given_eliminated:                   0
% 14.85/2.49  comparisons_done:                       0
% 14.85/2.49  comparisons_avoided:                    0
% 14.85/2.49  
% 14.85/2.49  ------ Simplifications
% 14.85/2.49  
% 14.85/2.49  
% 14.85/2.49  sim_fw_subset_subsumed:                 0
% 14.85/2.49  sim_bw_subset_subsumed:                 0
% 14.85/2.49  sim_fw_subsumed:                        868
% 14.85/2.49  sim_bw_subsumed:                        0
% 14.85/2.49  sim_fw_subsumption_res:                 0
% 14.85/2.49  sim_bw_subsumption_res:                 0
% 14.85/2.49  sim_tautology_del:                      0
% 14.85/2.49  sim_eq_tautology_del:                   2020
% 14.85/2.49  sim_eq_res_simp:                        0
% 14.85/2.49  sim_fw_demodulated:                     12914
% 14.85/2.49  sim_bw_demodulated:                     64
% 14.85/2.49  sim_light_normalised:                   7031
% 14.85/2.49  sim_joinable_taut:                      1057
% 14.85/2.49  sim_joinable_simp:                      1
% 14.85/2.49  sim_ac_normalised:                      0
% 14.85/2.49  sim_smt_subsumption:                    0
% 14.85/2.49  
%------------------------------------------------------------------------------
