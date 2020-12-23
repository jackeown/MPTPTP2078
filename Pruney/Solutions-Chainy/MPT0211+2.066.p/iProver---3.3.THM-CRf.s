%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:33 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 281 expanded)
%              Number of clauses        :   20 (  36 expanded)
%              Number of leaves         :   12 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :   56 ( 282 expanded)
%              Number of equality atoms :   55 ( 281 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f31,f26,f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f20,f19,f26,f33])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))),k4_xboole_0(k2_enumset1(X5,X5,X5,X5),k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f23,f19,f34,f35])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f28,f34,f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f21,f26,f26])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f32,f19,f33,f33,f26])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( k2_enumset1(X0_37,X0_37,X1_37,X2_37) = k2_enumset1(X0_37,X0_37,X2_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))),k4_xboole_0(k2_enumset1(X4_37,X4_37,X4_37,X4_37),k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X4_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_37,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X4_37,X4_37,X4_37,X4_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X4_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) ),
    inference(light_normalisation,[status(thm)],[c_19,c_22])).

cnf(c_655,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
    inference(superposition,[status(thm)],[c_37,c_22])).

cnf(c_759,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) = k2_enumset1(X0_37,X2_37,X1_37,X3_37) ),
    inference(superposition,[status(thm)],[c_17,c_655])).

cnf(c_656,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
    inference(superposition,[status(thm)],[c_37,c_37])).

cnf(c_666,plain,
    ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
    inference(light_normalisation,[status(thm)],[c_656,c_22])).

cnf(c_903,plain,
    ( k2_enumset1(X0_37,X1_37,X2_37,X1_37) = k2_enumset1(X0_37,X0_37,X2_37,X1_37) ),
    inference(superposition,[status(thm)],[c_759,c_666])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,plain,
    ( k2_enumset1(X0_37,X0_37,X1_37,X2_37) = k2_enumset1(X2_37,X2_37,X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_36,plain,
    ( k2_enumset1(sK1,sK0,sK2,sK0) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_16,c_22])).

cnf(c_46,plain,
    ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK0,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_21,c_36])).

cnf(c_3357,plain,
    ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_903,c_46])).

cnf(c_3523,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3357])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.26/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.97  
% 3.26/0.97  ------  iProver source info
% 3.26/0.97  
% 3.26/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.97  git: non_committed_changes: false
% 3.26/0.97  git: last_make_outside_of_git: false
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    true
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     num_symb
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       true
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.97  --res_to_prop_solver                    active
% 3.26/0.97  --res_prop_simpl_new                    false
% 3.26/0.97  --res_prop_simpl_given                  true
% 3.26/0.97  --res_passive_queue_type                priority_queues
% 3.26/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.97  --res_passive_queues_freq               [15;5]
% 3.26/0.97  --res_forward_subs                      full
% 3.26/0.97  --res_backward_subs                     full
% 3.26/0.97  --res_forward_subs_resolution           true
% 3.26/0.97  --res_backward_subs_resolution          true
% 3.26/0.97  --res_orphan_elimination                true
% 3.26/0.97  --res_time_limit                        2.
% 3.26/0.97  --res_out_proof                         true
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Options
% 3.26/0.97  
% 3.26/0.97  --superposition_flag                    true
% 3.26/0.97  --sup_passive_queue_type                priority_queues
% 3.26/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.97  --demod_completeness_check              fast
% 3.26/0.97  --demod_use_ground                      true
% 3.26/0.97  --sup_to_prop_solver                    passive
% 3.26/0.97  --sup_prop_simpl_new                    true
% 3.26/0.97  --sup_prop_simpl_given                  true
% 3.26/0.97  --sup_fun_splitting                     false
% 3.26/0.97  --sup_smt_interval                      50000
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Simplification Setup
% 3.26/0.97  
% 3.26/0.97  --sup_indices_passive                   []
% 3.26/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_full_bw                           [BwDemod]
% 3.26/0.97  --sup_immed_triv                        [TrivRules]
% 3.26/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_immed_bw_main                     []
% 3.26/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  
% 3.26/0.97  ------ Combination Options
% 3.26/0.97  
% 3.26/0.97  --comb_res_mult                         3
% 3.26/0.97  --comb_sup_mult                         2
% 3.26/0.97  --comb_inst_mult                        10
% 3.26/0.97  
% 3.26/0.97  ------ Debug Options
% 3.26/0.97  
% 3.26/0.97  --dbg_backtrace                         false
% 3.26/0.97  --dbg_dump_prop_clauses                 false
% 3.26/0.97  --dbg_dump_prop_clauses_file            -
% 3.26/0.97  --dbg_out_stat                          false
% 3.26/0.97  ------ Parsing...
% 3.26/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.26/0.97  ------ Proving...
% 3.26/0.97  ------ Problem Properties 
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  clauses                                 7
% 3.26/0.97  conjectures                             1
% 3.26/0.97  EPR                                     0
% 3.26/0.97  Horn                                    7
% 3.26/0.97  unary                                   7
% 3.26/0.97  binary                                  0
% 3.26/0.97  lits                                    7
% 3.26/0.97  lits eq                                 7
% 3.26/0.97  fd_pure                                 0
% 3.26/0.97  fd_pseudo                               0
% 3.26/0.97  fd_cond                                 0
% 3.26/0.97  fd_pseudo_cond                          0
% 3.26/0.97  AC symbols                              0
% 3.26/0.97  
% 3.26/0.97  ------ Schedule UEQ
% 3.26/0.97  
% 3.26/0.97  ------ pure equality problem: resolution off 
% 3.26/0.97  
% 3.26/0.97  ------ Option_UEQ Time Limit: Unbounded
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  Current options:
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    false
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     num_symb
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       false
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.97  --res_to_prop_solver                    active
% 3.26/0.97  --res_prop_simpl_new                    false
% 3.26/0.97  --res_prop_simpl_given                  true
% 3.26/0.97  --res_passive_queue_type                priority_queues
% 3.26/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.97  --res_passive_queues_freq               [15;5]
% 3.26/0.97  --res_forward_subs                      full
% 3.26/0.97  --res_backward_subs                     full
% 3.26/0.97  --res_forward_subs_resolution           true
% 3.26/0.97  --res_backward_subs_resolution          true
% 3.26/0.97  --res_orphan_elimination                true
% 3.26/0.97  --res_time_limit                        2.
% 3.26/0.97  --res_out_proof                         true
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Options
% 3.26/0.97  
% 3.26/0.97  --superposition_flag                    true
% 3.26/0.97  --sup_passive_queue_type                priority_queues
% 3.26/0.97  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.97  --demod_completeness_check              fast
% 3.26/0.97  --demod_use_ground                      true
% 3.26/0.97  --sup_to_prop_solver                    active
% 3.26/0.97  --sup_prop_simpl_new                    false
% 3.26/0.97  --sup_prop_simpl_given                  false
% 3.26/0.97  --sup_fun_splitting                     true
% 3.26/0.97  --sup_smt_interval                      10000
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Simplification Setup
% 3.26/0.97  
% 3.26/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.26/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_full_triv                         [TrivRules]
% 3.26/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.26/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.26/0.97  --sup_immed_triv                        [TrivRules]
% 3.26/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_bw_main                     []
% 3.26/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.26/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.26/0.97  
% 3.26/0.97  ------ Combination Options
% 3.26/0.97  
% 3.26/0.97  --comb_res_mult                         1
% 3.26/0.97  --comb_sup_mult                         1
% 3.26/0.97  --comb_inst_mult                        1000000
% 3.26/0.97  
% 3.26/0.97  ------ Debug Options
% 3.26/0.97  
% 3.26/0.97  --dbg_backtrace                         false
% 3.26/0.97  --dbg_dump_prop_clauses                 false
% 3.26/0.97  --dbg_dump_prop_clauses_file            -
% 3.26/0.97  --dbg_out_stat                          false
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  ------ Proving...
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  % SZS status Theorem for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97   Resolution empty clause
% 3.26/0.97  
% 3.26/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  fof(f13,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f31,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f13])).
% 3.26/0.97  
% 3.26/0.97  fof(f8,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f26,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f8])).
% 3.26/0.97  
% 3.26/0.97  fof(f42,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f31,f26,f26])).
% 3.26/0.97  
% 3.26/0.97  fof(f10,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f28,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f10])).
% 3.26/0.97  
% 3.26/0.97  fof(f5,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f23,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f5])).
% 3.26/0.97  
% 3.26/0.97  fof(f2,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f20,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f2])).
% 3.26/0.97  
% 3.26/0.97  fof(f1,axiom,(
% 3.26/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f19,plain,(
% 3.26/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.26/0.97    inference(cnf_transformation,[],[f1])).
% 3.26/0.97  
% 3.26/0.97  fof(f34,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f20,f19,f26,f33])).
% 3.26/0.97  
% 3.26/0.97  fof(f6,axiom,(
% 3.26/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f24,plain,(
% 3.26/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f6])).
% 3.26/0.97  
% 3.26/0.97  fof(f7,axiom,(
% 3.26/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f25,plain,(
% 3.26/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f7])).
% 3.26/0.97  
% 3.26/0.97  fof(f33,plain,(
% 3.26/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f25,f26])).
% 3.26/0.97  
% 3.26/0.97  fof(f35,plain,(
% 3.26/0.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f24,f33])).
% 3.26/0.97  
% 3.26/0.97  fof(f36,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))),k4_xboole_0(k2_enumset1(X5,X5,X5,X5),k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f23,f19,f34,f35])).
% 3.26/0.97  
% 3.26/0.97  fof(f40,plain,(
% 3.26/0.97    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1)))))) )),
% 3.26/0.97    inference(definition_unfolding,[],[f28,f34,f36])).
% 3.26/0.97  
% 3.26/0.97  fof(f9,axiom,(
% 3.26/0.97    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f27,plain,(
% 3.26/0.97    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f9])).
% 3.26/0.97  
% 3.26/0.97  fof(f37,plain,(
% 3.26/0.97    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f27,f34])).
% 3.26/0.97  
% 3.26/0.97  fof(f3,axiom,(
% 3.26/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f21,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.26/0.97    inference(cnf_transformation,[],[f3])).
% 3.26/0.97  
% 3.26/0.97  fof(f38,plain,(
% 3.26/0.97    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0)) )),
% 3.26/0.97    inference(definition_unfolding,[],[f21,f26,f26])).
% 3.26/0.97  
% 3.26/0.97  fof(f14,conjecture,(
% 3.26/0.97    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.26/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.97  
% 3.26/0.97  fof(f15,negated_conjecture,(
% 3.26/0.97    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.26/0.97    inference(negated_conjecture,[],[f14])).
% 3.26/0.97  
% 3.26/0.97  fof(f16,plain,(
% 3.26/0.97    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 3.26/0.97    inference(ennf_transformation,[],[f15])).
% 3.26/0.97  
% 3.26/0.97  fof(f17,plain,(
% 3.26/0.97    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.26/0.97    introduced(choice_axiom,[])).
% 3.26/0.97  
% 3.26/0.97  fof(f18,plain,(
% 3.26/0.97    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.26/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 3.26/0.97  
% 3.26/0.97  fof(f32,plain,(
% 3.26/0.97    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 3.26/0.97    inference(cnf_transformation,[],[f18])).
% 3.26/0.97  
% 3.26/0.97  fof(f43,plain,(
% 3.26/0.97    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 3.26/0.97    inference(definition_unfolding,[],[f32,f19,f33,f33,f26])).
% 3.26/0.97  
% 3.26/0.97  cnf(c_5,plain,
% 3.26/0.97      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_17,plain,
% 3.26/0.97      ( k2_enumset1(X0_37,X0_37,X1_37,X2_37) = k2_enumset1(X0_37,X0_37,X2_37,X1_37) ),
% 3.26/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3,plain,
% 3.26/0.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X4,X4,X4,X4),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))) ),
% 3.26/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_19,plain,
% 3.26/0.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))),k4_xboole_0(k2_enumset1(X4_37,X4_37,X4_37,X4_37),k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X4_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) ),
% 3.26/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_0,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.26/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_22,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
% 3.26/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_37,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X4_37,X4_37,X4_37,X4_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X4_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) ),
% 3.26/0.97      inference(light_normalisation,[status(thm)],[c_19,c_22]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_655,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_37,c_22]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_759,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X0_37,X1_37,X2_37))) = k2_enumset1(X0_37,X2_37,X1_37,X3_37) ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_17,c_655]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_656,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k5_xboole_0(k2_enumset1(X0_37,X0_37,X0_37,X1_37),k4_xboole_0(k2_enumset1(X2_37,X2_37,X2_37,X3_37),k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_37,c_37]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_666,plain,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k2_enumset1(X3_37,X3_37,X3_37,X3_37),k2_enumset1(X0_37,X1_37,X2_37,X3_37))) = k2_enumset1(X0_37,X1_37,X2_37,X3_37) ),
% 3.26/0.97      inference(light_normalisation,[status(thm)],[c_656,c_22]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_903,plain,
% 3.26/0.97      ( k2_enumset1(X0_37,X1_37,X2_37,X1_37) = k2_enumset1(X0_37,X0_37,X2_37,X1_37) ),
% 3.26/0.97      inference(superposition,[status(thm)],[c_759,c_666]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_1,plain,
% 3.26/0.97      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X0,X1) ),
% 3.26/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_21,plain,
% 3.26/0.97      ( k2_enumset1(X0_37,X0_37,X1_37,X2_37) = k2_enumset1(X2_37,X2_37,X0_37,X1_37) ),
% 3.26/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_6,negated_conjecture,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.26/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_16,negated_conjecture,
% 3.26/0.97      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK0),k2_enumset1(sK1,sK1,sK1,sK0))) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.26/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_36,plain,
% 3.26/0.97      ( k2_enumset1(sK1,sK0,sK2,sK0) != k2_enumset1(sK0,sK0,sK1,sK2) ),
% 3.26/0.97      inference(demodulation,[status(thm)],[c_16,c_22]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_46,plain,
% 3.26/0.97      ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK0,sK2,sK0) ),
% 3.26/0.97      inference(demodulation,[status(thm)],[c_21,c_36]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3357,plain,
% 3.26/0.97      ( k2_enumset1(sK1,sK1,sK2,sK0) != k2_enumset1(sK1,sK1,sK2,sK0) ),
% 3.26/0.97      inference(demodulation,[status(thm)],[c_903,c_46]) ).
% 3.26/0.97  
% 3.26/0.97  cnf(c_3523,plain,
% 3.26/0.97      ( $false ),
% 3.26/0.97      inference(equality_resolution_simp,[status(thm)],[c_3357]) ).
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  ------                               Statistics
% 3.26/0.97  
% 3.26/0.97  ------ General
% 3.26/0.97  
% 3.26/0.97  abstr_ref_over_cycles:                  0
% 3.26/0.97  abstr_ref_under_cycles:                 0
% 3.26/0.97  gc_basic_clause_elim:                   0
% 3.26/0.97  forced_gc_time:                         0
% 3.26/0.97  parsing_time:                           0.008
% 3.26/0.97  unif_index_cands_time:                  0.
% 3.26/0.97  unif_index_add_time:                    0.
% 3.26/0.97  orderings_time:                         0.
% 3.26/0.97  out_proof_time:                         0.007
% 3.26/0.97  total_time:                             0.152
% 3.26/0.97  num_of_symbols:                         38
% 3.26/0.97  num_of_terms:                           2042
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing
% 3.26/0.97  
% 3.26/0.97  num_of_splits:                          0
% 3.26/0.97  num_of_split_atoms:                     0
% 3.26/0.97  num_of_reused_defs:                     0
% 3.26/0.97  num_eq_ax_congr_red:                    20
% 3.26/0.97  num_of_sem_filtered_clauses:            0
% 3.26/0.97  num_of_subtypes:                        3
% 3.26/0.97  monotx_restored_types:                  0
% 3.26/0.97  sat_num_of_epr_types:                   0
% 3.26/0.97  sat_num_of_non_cyclic_types:            0
% 3.26/0.97  sat_guarded_non_collapsed_types:        0
% 3.26/0.97  num_pure_diseq_elim:                    0
% 3.26/0.97  simp_replaced_by:                       0
% 3.26/0.97  res_preprocessed:                       19
% 3.26/0.97  prep_upred:                             0
% 3.26/0.97  prep_unflattend:                        0
% 3.26/0.97  smt_new_axioms:                         0
% 3.26/0.97  pred_elim_cands:                        0
% 3.26/0.97  pred_elim:                              0
% 3.26/0.97  pred_elim_cl:                           0
% 3.26/0.97  pred_elim_cycles:                       0
% 3.26/0.97  merged_defs:                            0
% 3.26/0.97  merged_defs_ncl:                        0
% 3.26/0.97  bin_hyper_res:                          0
% 3.26/0.97  prep_cycles:                            2
% 3.26/0.97  pred_elim_time:                         0.
% 3.26/0.97  splitting_time:                         0.
% 3.26/0.97  sem_filter_time:                        0.
% 3.26/0.97  monotx_time:                            0.
% 3.26/0.97  subtype_inf_time:                       0.
% 3.26/0.97  
% 3.26/0.97  ------ Problem properties
% 3.26/0.97  
% 3.26/0.97  clauses:                                7
% 3.26/0.97  conjectures:                            1
% 3.26/0.97  epr:                                    0
% 3.26/0.97  horn:                                   7
% 3.26/0.97  ground:                                 1
% 3.26/0.97  unary:                                  7
% 3.26/0.97  binary:                                 0
% 3.26/0.97  lits:                                   7
% 3.26/0.97  lits_eq:                                7
% 3.26/0.97  fd_pure:                                0
% 3.26/0.97  fd_pseudo:                              0
% 3.26/0.97  fd_cond:                                0
% 3.26/0.97  fd_pseudo_cond:                         0
% 3.26/0.97  ac_symbols:                             0
% 3.26/0.97  
% 3.26/0.97  ------ Propositional Solver
% 3.26/0.97  
% 3.26/0.97  prop_solver_calls:                      13
% 3.26/0.97  prop_fast_solver_calls:                 50
% 3.26/0.97  smt_solver_calls:                       0
% 3.26/0.97  smt_fast_solver_calls:                  0
% 3.26/0.97  prop_num_of_clauses:                    72
% 3.26/0.97  prop_preprocess_simplified:             277
% 3.26/0.97  prop_fo_subsumed:                       0
% 3.26/0.97  prop_solver_time:                       0.
% 3.26/0.97  smt_solver_time:                        0.
% 3.26/0.97  smt_fast_solver_time:                   0.
% 3.26/0.97  prop_fast_solver_time:                  0.
% 3.26/0.97  prop_unsat_core_time:                   0.
% 3.26/0.97  
% 3.26/0.97  ------ QBF
% 3.26/0.97  
% 3.26/0.97  qbf_q_res:                              0
% 3.26/0.97  qbf_num_tautologies:                    0
% 3.26/0.97  qbf_prep_cycles:                        0
% 3.26/0.97  
% 3.26/0.97  ------ BMC1
% 3.26/0.97  
% 3.26/0.97  bmc1_current_bound:                     -1
% 3.26/0.97  bmc1_last_solved_bound:                 -1
% 3.26/0.97  bmc1_unsat_core_size:                   -1
% 3.26/0.97  bmc1_unsat_core_parents_size:           -1
% 3.26/0.97  bmc1_merge_next_fun:                    0
% 3.26/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation
% 3.26/0.97  
% 3.26/0.97  inst_num_of_clauses:                    0
% 3.26/0.97  inst_num_in_passive:                    0
% 3.26/0.97  inst_num_in_active:                     0
% 3.26/0.97  inst_num_in_unprocessed:                0
% 3.26/0.97  inst_num_of_loops:                      0
% 3.26/0.97  inst_num_of_learning_restarts:          0
% 3.26/0.97  inst_num_moves_active_passive:          0
% 3.26/0.97  inst_lit_activity:                      0
% 3.26/0.97  inst_lit_activity_moves:                0
% 3.26/0.97  inst_num_tautologies:                   0
% 3.26/0.97  inst_num_prop_implied:                  0
% 3.26/0.97  inst_num_existing_simplified:           0
% 3.26/0.97  inst_num_eq_res_simplified:             0
% 3.26/0.97  inst_num_child_elim:                    0
% 3.26/0.97  inst_num_of_dismatching_blockings:      0
% 3.26/0.97  inst_num_of_non_proper_insts:           0
% 3.26/0.97  inst_num_of_duplicates:                 0
% 3.26/0.97  inst_inst_num_from_inst_to_res:         0
% 3.26/0.97  inst_dismatching_checking_time:         0.
% 3.26/0.97  
% 3.26/0.97  ------ Resolution
% 3.26/0.97  
% 3.26/0.97  res_num_of_clauses:                     0
% 3.26/0.97  res_num_in_passive:                     0
% 3.26/0.97  res_num_in_active:                      0
% 3.26/0.97  res_num_of_loops:                       21
% 3.26/0.97  res_forward_subset_subsumed:            0
% 3.26/0.97  res_backward_subset_subsumed:           0
% 3.26/0.97  res_forward_subsumed:                   0
% 3.26/0.97  res_backward_subsumed:                  0
% 3.26/0.97  res_forward_subsumption_resolution:     0
% 3.26/0.97  res_backward_subsumption_resolution:    0
% 3.26/0.97  res_clause_to_clause_subsumption:       7677
% 3.26/0.97  res_orphan_elimination:                 0
% 3.26/0.97  res_tautology_del:                      0
% 3.26/0.97  res_num_eq_res_simplified:              0
% 3.26/0.97  res_num_sel_changes:                    0
% 3.26/0.97  res_moves_from_active_to_pass:          0
% 3.26/0.97  
% 3.26/0.97  ------ Superposition
% 3.26/0.97  
% 3.26/0.97  sup_time_total:                         0.
% 3.26/0.97  sup_time_generating:                    0.
% 3.26/0.97  sup_time_sim_full:                      0.
% 3.26/0.97  sup_time_sim_immed:                     0.
% 3.26/0.97  
% 3.26/0.97  sup_num_of_clauses:                     420
% 3.26/0.97  sup_num_in_active:                      41
% 3.26/0.97  sup_num_in_passive:                     379
% 3.26/0.97  sup_num_of_loops:                       43
% 3.26/0.97  sup_fw_superposition:                   1457
% 3.26/0.97  sup_bw_superposition:                   1917
% 3.26/0.97  sup_immediate_simplified:               156
% 3.26/0.97  sup_given_eliminated:                   0
% 3.26/0.97  comparisons_done:                       0
% 3.26/0.97  comparisons_avoided:                    0
% 3.26/0.97  
% 3.26/0.97  ------ Simplifications
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  sim_fw_subset_subsumed:                 0
% 3.26/0.97  sim_bw_subset_subsumed:                 0
% 3.26/0.97  sim_fw_subsumed:                        40
% 3.26/0.97  sim_bw_subsumed:                        13
% 3.26/0.98  sim_fw_subsumption_res:                 0
% 3.26/0.98  sim_bw_subsumption_res:                 0
% 3.26/0.98  sim_tautology_del:                      0
% 3.26/0.98  sim_eq_tautology_del:                   5
% 3.26/0.98  sim_eq_res_simp:                        0
% 3.26/0.98  sim_fw_demodulated:                     41
% 3.26/0.98  sim_bw_demodulated:                     3
% 3.26/0.98  sim_light_normalised:                   66
% 3.26/0.98  sim_joinable_taut:                      0
% 3.26/0.98  sim_joinable_simp:                      0
% 3.26/0.98  sim_ac_normalised:                      0
% 3.26/0.98  sim_smt_subsumption:                    0
% 3.26/0.98  
%------------------------------------------------------------------------------
