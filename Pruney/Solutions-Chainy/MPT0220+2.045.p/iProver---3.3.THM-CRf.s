%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:34 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 197 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :   77 ( 203 expanded)
%              Number of equality atoms :   68 ( 194 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f37,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f46,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f37,f38,f44,f43,f43])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f44,f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_301,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_528,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_3,c_301])).

cnf(c_529,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_301])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_553,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_529,c_2])).

cnf(c_830,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_528,c_553])).

cnf(c_847,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_4,c_830])).

cnf(c_876,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_847,c_2])).

cnf(c_303,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_848,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_303,c_830])).

cnf(c_873,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_848,c_2])).

cnf(c_877,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_876,c_873])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_401,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_5,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_87,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_88,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_318,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_87,c_88])).

cnf(c_1361,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_401,c_318])).

cnf(c_10277,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_877,c_1361])).

cnf(c_10281,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10277])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.75/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.04  
% 3.75/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/1.04  
% 3.75/1.04  ------  iProver source info
% 3.75/1.04  
% 3.75/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.75/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/1.04  git: non_committed_changes: false
% 3.75/1.04  git: last_make_outside_of_git: false
% 3.75/1.04  
% 3.75/1.04  ------ 
% 3.75/1.04  
% 3.75/1.04  ------ Input Options
% 3.75/1.04  
% 3.75/1.04  --out_options                           all
% 3.75/1.04  --tptp_safe_out                         true
% 3.75/1.04  --problem_path                          ""
% 3.75/1.04  --include_path                          ""
% 3.75/1.04  --clausifier                            res/vclausify_rel
% 3.75/1.04  --clausifier_options                    --mode clausify
% 3.75/1.04  --stdin                                 false
% 3.75/1.04  --stats_out                             sel
% 3.75/1.04  
% 3.75/1.04  ------ General Options
% 3.75/1.04  
% 3.75/1.04  --fof                                   false
% 3.75/1.04  --time_out_real                         604.96
% 3.75/1.04  --time_out_virtual                      -1.
% 3.75/1.04  --symbol_type_check                     false
% 3.75/1.04  --clausify_out                          false
% 3.75/1.04  --sig_cnt_out                           false
% 3.75/1.04  --trig_cnt_out                          false
% 3.75/1.04  --trig_cnt_out_tolerance                1.
% 3.75/1.04  --trig_cnt_out_sk_spl                   false
% 3.75/1.04  --abstr_cl_out                          false
% 3.75/1.04  
% 3.75/1.04  ------ Global Options
% 3.75/1.04  
% 3.75/1.04  --schedule                              none
% 3.75/1.04  --add_important_lit                     false
% 3.75/1.04  --prop_solver_per_cl                    1000
% 3.75/1.04  --min_unsat_core                        false
% 3.75/1.04  --soft_assumptions                      false
% 3.75/1.04  --soft_lemma_size                       3
% 3.75/1.04  --prop_impl_unit_size                   0
% 3.75/1.04  --prop_impl_unit                        []
% 3.75/1.04  --share_sel_clauses                     true
% 3.75/1.04  --reset_solvers                         false
% 3.75/1.04  --bc_imp_inh                            [conj_cone]
% 3.75/1.04  --conj_cone_tolerance                   3.
% 3.75/1.04  --extra_neg_conj                        none
% 3.75/1.04  --large_theory_mode                     true
% 3.75/1.04  --prolific_symb_bound                   200
% 3.75/1.04  --lt_threshold                          2000
% 3.75/1.04  --clause_weak_htbl                      true
% 3.75/1.04  --gc_record_bc_elim                     false
% 3.75/1.04  
% 3.75/1.04  ------ Preprocessing Options
% 3.75/1.04  
% 3.75/1.04  --preprocessing_flag                    true
% 3.75/1.04  --time_out_prep_mult                    0.1
% 3.75/1.04  --splitting_mode                        input
% 3.75/1.04  --splitting_grd                         true
% 3.75/1.04  --splitting_cvd                         false
% 3.75/1.04  --splitting_cvd_svl                     false
% 3.75/1.04  --splitting_nvd                         32
% 3.75/1.04  --sub_typing                            true
% 3.75/1.04  --prep_gs_sim                           false
% 3.75/1.04  --prep_unflatten                        true
% 3.75/1.04  --prep_res_sim                          true
% 3.75/1.04  --prep_upred                            true
% 3.75/1.04  --prep_sem_filter                       exhaustive
% 3.75/1.04  --prep_sem_filter_out                   false
% 3.75/1.04  --pred_elim                             false
% 3.75/1.04  --res_sim_input                         true
% 3.75/1.04  --eq_ax_congr_red                       true
% 3.75/1.04  --pure_diseq_elim                       true
% 3.75/1.04  --brand_transform                       false
% 3.75/1.04  --non_eq_to_eq                          false
% 3.75/1.04  --prep_def_merge                        true
% 3.75/1.04  --prep_def_merge_prop_impl              false
% 3.75/1.04  --prep_def_merge_mbd                    true
% 3.75/1.04  --prep_def_merge_tr_red                 false
% 3.75/1.04  --prep_def_merge_tr_cl                  false
% 3.75/1.04  --smt_preprocessing                     true
% 3.75/1.04  --smt_ac_axioms                         fast
% 3.75/1.04  --preprocessed_out                      false
% 3.75/1.04  --preprocessed_stats                    false
% 3.75/1.04  
% 3.75/1.04  ------ Abstraction refinement Options
% 3.75/1.04  
% 3.75/1.04  --abstr_ref                             []
% 3.75/1.04  --abstr_ref_prep                        false
% 3.75/1.04  --abstr_ref_until_sat                   false
% 3.75/1.04  --abstr_ref_sig_restrict                funpre
% 3.75/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.04  --abstr_ref_under                       []
% 3.75/1.04  
% 3.75/1.04  ------ SAT Options
% 3.75/1.04  
% 3.75/1.04  --sat_mode                              false
% 3.75/1.04  --sat_fm_restart_options                ""
% 3.75/1.04  --sat_gr_def                            false
% 3.75/1.04  --sat_epr_types                         true
% 3.75/1.04  --sat_non_cyclic_types                  false
% 3.75/1.04  --sat_finite_models                     false
% 3.75/1.04  --sat_fm_lemmas                         false
% 3.75/1.04  --sat_fm_prep                           false
% 3.75/1.04  --sat_fm_uc_incr                        true
% 3.75/1.04  --sat_out_model                         small
% 3.75/1.04  --sat_out_clauses                       false
% 3.75/1.04  
% 3.75/1.04  ------ QBF Options
% 3.75/1.04  
% 3.75/1.04  --qbf_mode                              false
% 3.75/1.04  --qbf_elim_univ                         false
% 3.75/1.04  --qbf_dom_inst                          none
% 3.75/1.04  --qbf_dom_pre_inst                      false
% 3.75/1.04  --qbf_sk_in                             false
% 3.75/1.04  --qbf_pred_elim                         true
% 3.75/1.04  --qbf_split                             512
% 3.75/1.04  
% 3.75/1.04  ------ BMC1 Options
% 3.75/1.04  
% 3.75/1.04  --bmc1_incremental                      false
% 3.75/1.04  --bmc1_axioms                           reachable_all
% 3.75/1.04  --bmc1_min_bound                        0
% 3.75/1.04  --bmc1_max_bound                        -1
% 3.75/1.04  --bmc1_max_bound_default                -1
% 3.75/1.04  --bmc1_symbol_reachability              true
% 3.75/1.04  --bmc1_property_lemmas                  false
% 3.75/1.04  --bmc1_k_induction                      false
% 3.75/1.04  --bmc1_non_equiv_states                 false
% 3.75/1.04  --bmc1_deadlock                         false
% 3.75/1.04  --bmc1_ucm                              false
% 3.75/1.04  --bmc1_add_unsat_core                   none
% 3.75/1.04  --bmc1_unsat_core_children              false
% 3.75/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.04  --bmc1_out_stat                         full
% 3.75/1.04  --bmc1_ground_init                      false
% 3.75/1.04  --bmc1_pre_inst_next_state              false
% 3.75/1.04  --bmc1_pre_inst_state                   false
% 3.75/1.04  --bmc1_pre_inst_reach_state             false
% 3.75/1.04  --bmc1_out_unsat_core                   false
% 3.75/1.04  --bmc1_aig_witness_out                  false
% 3.75/1.04  --bmc1_verbose                          false
% 3.75/1.04  --bmc1_dump_clauses_tptp                false
% 3.75/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.04  --bmc1_dump_file                        -
% 3.75/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.04  --bmc1_ucm_extend_mode                  1
% 3.75/1.04  --bmc1_ucm_init_mode                    2
% 3.75/1.04  --bmc1_ucm_cone_mode                    none
% 3.75/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.04  --bmc1_ucm_relax_model                  4
% 3.75/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.04  --bmc1_ucm_layered_model                none
% 3.75/1.04  --bmc1_ucm_max_lemma_size               10
% 3.75/1.04  
% 3.75/1.04  ------ AIG Options
% 3.75/1.04  
% 3.75/1.04  --aig_mode                              false
% 3.75/1.04  
% 3.75/1.04  ------ Instantiation Options
% 3.75/1.04  
% 3.75/1.04  --instantiation_flag                    true
% 3.75/1.04  --inst_sos_flag                         false
% 3.75/1.04  --inst_sos_phase                        true
% 3.75/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.04  --inst_lit_sel_side                     num_symb
% 3.75/1.04  --inst_solver_per_active                1400
% 3.75/1.04  --inst_solver_calls_frac                1.
% 3.75/1.04  --inst_passive_queue_type               priority_queues
% 3.75/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.04  --inst_passive_queues_freq              [25;2]
% 3.75/1.04  --inst_dismatching                      true
% 3.75/1.04  --inst_eager_unprocessed_to_passive     true
% 3.75/1.04  --inst_prop_sim_given                   true
% 3.75/1.04  --inst_prop_sim_new                     false
% 3.75/1.04  --inst_subs_new                         false
% 3.75/1.04  --inst_eq_res_simp                      false
% 3.75/1.04  --inst_subs_given                       false
% 3.75/1.04  --inst_orphan_elimination               true
% 3.75/1.04  --inst_learning_loop_flag               true
% 3.75/1.04  --inst_learning_start                   3000
% 3.75/1.04  --inst_learning_factor                  2
% 3.75/1.04  --inst_start_prop_sim_after_learn       3
% 3.75/1.04  --inst_sel_renew                        solver
% 3.75/1.04  --inst_lit_activity_flag                true
% 3.75/1.04  --inst_restr_to_given                   false
% 3.75/1.04  --inst_activity_threshold               500
% 3.75/1.04  --inst_out_proof                        true
% 3.75/1.04  
% 3.75/1.04  ------ Resolution Options
% 3.75/1.04  
% 3.75/1.04  --resolution_flag                       true
% 3.75/1.04  --res_lit_sel                           adaptive
% 3.75/1.04  --res_lit_sel_side                      none
% 3.75/1.04  --res_ordering                          kbo
% 3.75/1.04  --res_to_prop_solver                    active
% 3.75/1.04  --res_prop_simpl_new                    false
% 3.75/1.04  --res_prop_simpl_given                  true
% 3.75/1.04  --res_passive_queue_type                priority_queues
% 3.75/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.04  --res_passive_queues_freq               [15;5]
% 3.75/1.04  --res_forward_subs                      full
% 3.75/1.04  --res_backward_subs                     full
% 3.75/1.04  --res_forward_subs_resolution           true
% 3.75/1.04  --res_backward_subs_resolution          true
% 3.75/1.04  --res_orphan_elimination                true
% 3.75/1.04  --res_time_limit                        2.
% 3.75/1.04  --res_out_proof                         true
% 3.75/1.04  
% 3.75/1.04  ------ Superposition Options
% 3.75/1.04  
% 3.75/1.04  --superposition_flag                    true
% 3.75/1.04  --sup_passive_queue_type                priority_queues
% 3.75/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.04  --sup_passive_queues_freq               [1;4]
% 3.75/1.04  --demod_completeness_check              fast
% 3.75/1.04  --demod_use_ground                      true
% 3.75/1.04  --sup_to_prop_solver                    passive
% 3.75/1.04  --sup_prop_simpl_new                    true
% 3.75/1.04  --sup_prop_simpl_given                  true
% 3.75/1.04  --sup_fun_splitting                     false
% 3.75/1.04  --sup_smt_interval                      50000
% 3.75/1.04  
% 3.75/1.04  ------ Superposition Simplification Setup
% 3.75/1.04  
% 3.75/1.04  --sup_indices_passive                   []
% 3.75/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_full_bw                           [BwDemod]
% 3.75/1.04  --sup_immed_triv                        [TrivRules]
% 3.75/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_immed_bw_main                     []
% 3.75/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.04  
% 3.75/1.04  ------ Combination Options
% 3.75/1.04  
% 3.75/1.04  --comb_res_mult                         3
% 3.75/1.04  --comb_sup_mult                         2
% 3.75/1.04  --comb_inst_mult                        10
% 3.75/1.04  
% 3.75/1.04  ------ Debug Options
% 3.75/1.04  
% 3.75/1.04  --dbg_backtrace                         false
% 3.75/1.04  --dbg_dump_prop_clauses                 false
% 3.75/1.04  --dbg_dump_prop_clauses_file            -
% 3.75/1.04  --dbg_out_stat                          false
% 3.75/1.04  ------ Parsing...
% 3.75/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/1.04  
% 3.75/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.75/1.04  
% 3.75/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/1.04  
% 3.75/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/1.04  ------ Proving...
% 3.75/1.04  ------ Problem Properties 
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  clauses                                 7
% 3.75/1.04  conjectures                             1
% 3.75/1.04  EPR                                     0
% 3.75/1.04  Horn                                    7
% 3.75/1.04  unary                                   6
% 3.75/1.04  binary                                  1
% 3.75/1.04  lits                                    8
% 3.75/1.04  lits eq                                 6
% 3.75/1.04  fd_pure                                 0
% 3.75/1.04  fd_pseudo                               0
% 3.75/1.04  fd_cond                                 0
% 3.75/1.04  fd_pseudo_cond                          0
% 3.75/1.04  AC symbols                              0
% 3.75/1.04  
% 3.75/1.04  ------ Input Options Time Limit: Unbounded
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  ------ 
% 3.75/1.04  Current options:
% 3.75/1.04  ------ 
% 3.75/1.04  
% 3.75/1.04  ------ Input Options
% 3.75/1.04  
% 3.75/1.04  --out_options                           all
% 3.75/1.04  --tptp_safe_out                         true
% 3.75/1.04  --problem_path                          ""
% 3.75/1.04  --include_path                          ""
% 3.75/1.04  --clausifier                            res/vclausify_rel
% 3.75/1.04  --clausifier_options                    --mode clausify
% 3.75/1.04  --stdin                                 false
% 3.75/1.04  --stats_out                             sel
% 3.75/1.04  
% 3.75/1.04  ------ General Options
% 3.75/1.04  
% 3.75/1.04  --fof                                   false
% 3.75/1.04  --time_out_real                         604.96
% 3.75/1.04  --time_out_virtual                      -1.
% 3.75/1.04  --symbol_type_check                     false
% 3.75/1.04  --clausify_out                          false
% 3.75/1.04  --sig_cnt_out                           false
% 3.75/1.04  --trig_cnt_out                          false
% 3.75/1.04  --trig_cnt_out_tolerance                1.
% 3.75/1.04  --trig_cnt_out_sk_spl                   false
% 3.75/1.04  --abstr_cl_out                          false
% 3.75/1.04  
% 3.75/1.04  ------ Global Options
% 3.75/1.04  
% 3.75/1.04  --schedule                              none
% 3.75/1.04  --add_important_lit                     false
% 3.75/1.04  --prop_solver_per_cl                    1000
% 3.75/1.04  --min_unsat_core                        false
% 3.75/1.04  --soft_assumptions                      false
% 3.75/1.04  --soft_lemma_size                       3
% 3.75/1.04  --prop_impl_unit_size                   0
% 3.75/1.04  --prop_impl_unit                        []
% 3.75/1.04  --share_sel_clauses                     true
% 3.75/1.04  --reset_solvers                         false
% 3.75/1.04  --bc_imp_inh                            [conj_cone]
% 3.75/1.04  --conj_cone_tolerance                   3.
% 3.75/1.04  --extra_neg_conj                        none
% 3.75/1.04  --large_theory_mode                     true
% 3.75/1.04  --prolific_symb_bound                   200
% 3.75/1.04  --lt_threshold                          2000
% 3.75/1.04  --clause_weak_htbl                      true
% 3.75/1.04  --gc_record_bc_elim                     false
% 3.75/1.04  
% 3.75/1.04  ------ Preprocessing Options
% 3.75/1.04  
% 3.75/1.04  --preprocessing_flag                    true
% 3.75/1.04  --time_out_prep_mult                    0.1
% 3.75/1.04  --splitting_mode                        input
% 3.75/1.04  --splitting_grd                         true
% 3.75/1.04  --splitting_cvd                         false
% 3.75/1.04  --splitting_cvd_svl                     false
% 3.75/1.04  --splitting_nvd                         32
% 3.75/1.04  --sub_typing                            true
% 3.75/1.04  --prep_gs_sim                           false
% 3.75/1.04  --prep_unflatten                        true
% 3.75/1.04  --prep_res_sim                          true
% 3.75/1.04  --prep_upred                            true
% 3.75/1.04  --prep_sem_filter                       exhaustive
% 3.75/1.04  --prep_sem_filter_out                   false
% 3.75/1.04  --pred_elim                             false
% 3.75/1.04  --res_sim_input                         true
% 3.75/1.04  --eq_ax_congr_red                       true
% 3.75/1.04  --pure_diseq_elim                       true
% 3.75/1.04  --brand_transform                       false
% 3.75/1.04  --non_eq_to_eq                          false
% 3.75/1.04  --prep_def_merge                        true
% 3.75/1.04  --prep_def_merge_prop_impl              false
% 3.75/1.04  --prep_def_merge_mbd                    true
% 3.75/1.04  --prep_def_merge_tr_red                 false
% 3.75/1.04  --prep_def_merge_tr_cl                  false
% 3.75/1.04  --smt_preprocessing                     true
% 3.75/1.04  --smt_ac_axioms                         fast
% 3.75/1.04  --preprocessed_out                      false
% 3.75/1.04  --preprocessed_stats                    false
% 3.75/1.04  
% 3.75/1.04  ------ Abstraction refinement Options
% 3.75/1.04  
% 3.75/1.04  --abstr_ref                             []
% 3.75/1.04  --abstr_ref_prep                        false
% 3.75/1.04  --abstr_ref_until_sat                   false
% 3.75/1.04  --abstr_ref_sig_restrict                funpre
% 3.75/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.04  --abstr_ref_under                       []
% 3.75/1.04  
% 3.75/1.04  ------ SAT Options
% 3.75/1.04  
% 3.75/1.04  --sat_mode                              false
% 3.75/1.04  --sat_fm_restart_options                ""
% 3.75/1.04  --sat_gr_def                            false
% 3.75/1.04  --sat_epr_types                         true
% 3.75/1.04  --sat_non_cyclic_types                  false
% 3.75/1.04  --sat_finite_models                     false
% 3.75/1.04  --sat_fm_lemmas                         false
% 3.75/1.04  --sat_fm_prep                           false
% 3.75/1.04  --sat_fm_uc_incr                        true
% 3.75/1.04  --sat_out_model                         small
% 3.75/1.04  --sat_out_clauses                       false
% 3.75/1.04  
% 3.75/1.04  ------ QBF Options
% 3.75/1.04  
% 3.75/1.04  --qbf_mode                              false
% 3.75/1.04  --qbf_elim_univ                         false
% 3.75/1.04  --qbf_dom_inst                          none
% 3.75/1.04  --qbf_dom_pre_inst                      false
% 3.75/1.04  --qbf_sk_in                             false
% 3.75/1.04  --qbf_pred_elim                         true
% 3.75/1.04  --qbf_split                             512
% 3.75/1.04  
% 3.75/1.04  ------ BMC1 Options
% 3.75/1.04  
% 3.75/1.04  --bmc1_incremental                      false
% 3.75/1.04  --bmc1_axioms                           reachable_all
% 3.75/1.04  --bmc1_min_bound                        0
% 3.75/1.04  --bmc1_max_bound                        -1
% 3.75/1.04  --bmc1_max_bound_default                -1
% 3.75/1.04  --bmc1_symbol_reachability              true
% 3.75/1.04  --bmc1_property_lemmas                  false
% 3.75/1.04  --bmc1_k_induction                      false
% 3.75/1.04  --bmc1_non_equiv_states                 false
% 3.75/1.04  --bmc1_deadlock                         false
% 3.75/1.04  --bmc1_ucm                              false
% 3.75/1.04  --bmc1_add_unsat_core                   none
% 3.75/1.04  --bmc1_unsat_core_children              false
% 3.75/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.04  --bmc1_out_stat                         full
% 3.75/1.04  --bmc1_ground_init                      false
% 3.75/1.04  --bmc1_pre_inst_next_state              false
% 3.75/1.04  --bmc1_pre_inst_state                   false
% 3.75/1.04  --bmc1_pre_inst_reach_state             false
% 3.75/1.04  --bmc1_out_unsat_core                   false
% 3.75/1.04  --bmc1_aig_witness_out                  false
% 3.75/1.04  --bmc1_verbose                          false
% 3.75/1.04  --bmc1_dump_clauses_tptp                false
% 3.75/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.04  --bmc1_dump_file                        -
% 3.75/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.04  --bmc1_ucm_extend_mode                  1
% 3.75/1.04  --bmc1_ucm_init_mode                    2
% 3.75/1.04  --bmc1_ucm_cone_mode                    none
% 3.75/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.04  --bmc1_ucm_relax_model                  4
% 3.75/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.04  --bmc1_ucm_layered_model                none
% 3.75/1.04  --bmc1_ucm_max_lemma_size               10
% 3.75/1.04  
% 3.75/1.04  ------ AIG Options
% 3.75/1.04  
% 3.75/1.04  --aig_mode                              false
% 3.75/1.04  
% 3.75/1.04  ------ Instantiation Options
% 3.75/1.04  
% 3.75/1.04  --instantiation_flag                    true
% 3.75/1.04  --inst_sos_flag                         false
% 3.75/1.04  --inst_sos_phase                        true
% 3.75/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.04  --inst_lit_sel_side                     num_symb
% 3.75/1.04  --inst_solver_per_active                1400
% 3.75/1.04  --inst_solver_calls_frac                1.
% 3.75/1.04  --inst_passive_queue_type               priority_queues
% 3.75/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.04  --inst_passive_queues_freq              [25;2]
% 3.75/1.04  --inst_dismatching                      true
% 3.75/1.04  --inst_eager_unprocessed_to_passive     true
% 3.75/1.04  --inst_prop_sim_given                   true
% 3.75/1.04  --inst_prop_sim_new                     false
% 3.75/1.04  --inst_subs_new                         false
% 3.75/1.04  --inst_eq_res_simp                      false
% 3.75/1.04  --inst_subs_given                       false
% 3.75/1.04  --inst_orphan_elimination               true
% 3.75/1.04  --inst_learning_loop_flag               true
% 3.75/1.04  --inst_learning_start                   3000
% 3.75/1.04  --inst_learning_factor                  2
% 3.75/1.04  --inst_start_prop_sim_after_learn       3
% 3.75/1.04  --inst_sel_renew                        solver
% 3.75/1.04  --inst_lit_activity_flag                true
% 3.75/1.04  --inst_restr_to_given                   false
% 3.75/1.04  --inst_activity_threshold               500
% 3.75/1.04  --inst_out_proof                        true
% 3.75/1.04  
% 3.75/1.04  ------ Resolution Options
% 3.75/1.04  
% 3.75/1.04  --resolution_flag                       true
% 3.75/1.04  --res_lit_sel                           adaptive
% 3.75/1.04  --res_lit_sel_side                      none
% 3.75/1.04  --res_ordering                          kbo
% 3.75/1.04  --res_to_prop_solver                    active
% 3.75/1.04  --res_prop_simpl_new                    false
% 3.75/1.04  --res_prop_simpl_given                  true
% 3.75/1.04  --res_passive_queue_type                priority_queues
% 3.75/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.04  --res_passive_queues_freq               [15;5]
% 3.75/1.04  --res_forward_subs                      full
% 3.75/1.04  --res_backward_subs                     full
% 3.75/1.04  --res_forward_subs_resolution           true
% 3.75/1.04  --res_backward_subs_resolution          true
% 3.75/1.04  --res_orphan_elimination                true
% 3.75/1.04  --res_time_limit                        2.
% 3.75/1.04  --res_out_proof                         true
% 3.75/1.04  
% 3.75/1.04  ------ Superposition Options
% 3.75/1.04  
% 3.75/1.04  --superposition_flag                    true
% 3.75/1.04  --sup_passive_queue_type                priority_queues
% 3.75/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.04  --sup_passive_queues_freq               [1;4]
% 3.75/1.04  --demod_completeness_check              fast
% 3.75/1.04  --demod_use_ground                      true
% 3.75/1.04  --sup_to_prop_solver                    passive
% 3.75/1.04  --sup_prop_simpl_new                    true
% 3.75/1.04  --sup_prop_simpl_given                  true
% 3.75/1.04  --sup_fun_splitting                     false
% 3.75/1.04  --sup_smt_interval                      50000
% 3.75/1.04  
% 3.75/1.04  ------ Superposition Simplification Setup
% 3.75/1.04  
% 3.75/1.04  --sup_indices_passive                   []
% 3.75/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_full_bw                           [BwDemod]
% 3.75/1.04  --sup_immed_triv                        [TrivRules]
% 3.75/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_immed_bw_main                     []
% 3.75/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.04  
% 3.75/1.04  ------ Combination Options
% 3.75/1.04  
% 3.75/1.04  --comb_res_mult                         3
% 3.75/1.04  --comb_sup_mult                         2
% 3.75/1.04  --comb_inst_mult                        10
% 3.75/1.04  
% 3.75/1.04  ------ Debug Options
% 3.75/1.04  
% 3.75/1.04  --dbg_backtrace                         false
% 3.75/1.04  --dbg_dump_prop_clauses                 false
% 3.75/1.04  --dbg_dump_prop_clauses_file            -
% 3.75/1.04  --dbg_out_stat                          false
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  ------ Proving...
% 3.75/1.04  
% 3.75/1.04  
% 3.75/1.04  % SZS status Theorem for theBenchmark.p
% 3.75/1.04  
% 3.75/1.04   Resolution empty clause
% 3.75/1.04  
% 3.75/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/1.04  
% 3.75/1.04  fof(f6,axiom,(
% 3.75/1.04    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f27,plain,(
% 3.75/1.04    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.75/1.04    inference(cnf_transformation,[],[f6])).
% 3.75/1.04  
% 3.75/1.04  fof(f5,axiom,(
% 3.75/1.04    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f26,plain,(
% 3.75/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f5])).
% 3.75/1.04  
% 3.75/1.04  fof(f4,axiom,(
% 3.75/1.04    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f25,plain,(
% 3.75/1.04    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.75/1.04    inference(cnf_transformation,[],[f4])).
% 3.75/1.04  
% 3.75/1.04  fof(f1,axiom,(
% 3.75/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f22,plain,(
% 3.75/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f1])).
% 3.75/1.04  
% 3.75/1.04  fof(f16,conjecture,(
% 3.75/1.04    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f17,negated_conjecture,(
% 3.75/1.04    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 3.75/1.04    inference(negated_conjecture,[],[f16])).
% 3.75/1.04  
% 3.75/1.04  fof(f19,plain,(
% 3.75/1.04    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 3.75/1.04    inference(ennf_transformation,[],[f17])).
% 3.75/1.04  
% 3.75/1.04  fof(f20,plain,(
% 3.75/1.04    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.75/1.04    introduced(choice_axiom,[])).
% 3.75/1.04  
% 3.75/1.04  fof(f21,plain,(
% 3.75/1.04    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.75/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 3.75/1.04  
% 3.75/1.04  fof(f37,plain,(
% 3.75/1.04    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 3.75/1.04    inference(cnf_transformation,[],[f21])).
% 3.75/1.04  
% 3.75/1.04  fof(f7,axiom,(
% 3.75/1.04    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f28,plain,(
% 3.75/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f7])).
% 3.75/1.04  
% 3.75/1.04  fof(f2,axiom,(
% 3.75/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f23,plain,(
% 3.75/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.75/1.04    inference(cnf_transformation,[],[f2])).
% 3.75/1.04  
% 3.75/1.04  fof(f38,plain,(
% 3.75/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.75/1.04    inference(definition_unfolding,[],[f28,f23])).
% 3.75/1.04  
% 3.75/1.04  fof(f8,axiom,(
% 3.75/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f29,plain,(
% 3.75/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f8])).
% 3.75/1.04  
% 3.75/1.04  fof(f44,plain,(
% 3.75/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.75/1.04    inference(definition_unfolding,[],[f29,f43])).
% 3.75/1.04  
% 3.75/1.04  fof(f9,axiom,(
% 3.75/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f30,plain,(
% 3.75/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f9])).
% 3.75/1.04  
% 3.75/1.04  fof(f10,axiom,(
% 3.75/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f31,plain,(
% 3.75/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f10])).
% 3.75/1.04  
% 3.75/1.04  fof(f11,axiom,(
% 3.75/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f32,plain,(
% 3.75/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.75/1.04    inference(cnf_transformation,[],[f11])).
% 3.75/1.04  
% 3.75/1.04  fof(f12,axiom,(
% 3.75/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.75/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.04  
% 3.75/1.04  fof(f33,plain,(
% 3.75/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.75/1.05    inference(cnf_transformation,[],[f12])).
% 3.75/1.05  
% 3.75/1.05  fof(f13,axiom,(
% 3.75/1.05    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.05  
% 3.75/1.05  fof(f34,plain,(
% 3.75/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/1.05    inference(cnf_transformation,[],[f13])).
% 3.75/1.05  
% 3.75/1.05  fof(f14,axiom,(
% 3.75/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.05  
% 3.75/1.05  fof(f35,plain,(
% 3.75/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.75/1.05    inference(cnf_transformation,[],[f14])).
% 3.75/1.05  
% 3.75/1.05  fof(f39,plain,(
% 3.75/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/1.05    inference(definition_unfolding,[],[f34,f35])).
% 3.75/1.05  
% 3.75/1.05  fof(f40,plain,(
% 3.75/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.75/1.05    inference(definition_unfolding,[],[f33,f39])).
% 3.75/1.05  
% 3.75/1.05  fof(f41,plain,(
% 3.75/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.75/1.05    inference(definition_unfolding,[],[f32,f40])).
% 3.75/1.05  
% 3.75/1.05  fof(f42,plain,(
% 3.75/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.75/1.05    inference(definition_unfolding,[],[f31,f41])).
% 3.75/1.05  
% 3.75/1.05  fof(f43,plain,(
% 3.75/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.75/1.05    inference(definition_unfolding,[],[f30,f42])).
% 3.75/1.05  
% 3.75/1.05  fof(f46,plain,(
% 3.75/1.05    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 3.75/1.05    inference(definition_unfolding,[],[f37,f38,f44,f43,f43])).
% 3.75/1.05  
% 3.75/1.05  fof(f15,axiom,(
% 3.75/1.05    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.05  
% 3.75/1.05  fof(f36,plain,(
% 3.75/1.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.75/1.05    inference(cnf_transformation,[],[f15])).
% 3.75/1.05  
% 3.75/1.05  fof(f45,plain,(
% 3.75/1.05    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.75/1.05    inference(definition_unfolding,[],[f36,f44,f43])).
% 3.75/1.05  
% 3.75/1.05  fof(f3,axiom,(
% 3.75/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.75/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.05  
% 3.75/1.05  fof(f18,plain,(
% 3.75/1.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.75/1.05    inference(ennf_transformation,[],[f3])).
% 3.75/1.05  
% 3.75/1.05  fof(f24,plain,(
% 3.75/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/1.05    inference(cnf_transformation,[],[f18])).
% 3.75/1.05  
% 3.75/1.05  cnf(c_4,plain,
% 3.75/1.05      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.75/1.05      inference(cnf_transformation,[],[f27]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_3,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.75/1.05      inference(cnf_transformation,[],[f26]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_301,plain,
% 3.75/1.05      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_528,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_3,c_301]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_529,plain,
% 3.75/1.05      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_4,c_301]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_2,plain,
% 3.75/1.05      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.75/1.05      inference(cnf_transformation,[],[f25]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_553,plain,
% 3.75/1.05      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.75/1.05      inference(light_normalisation,[status(thm)],[c_529,c_2]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_830,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 3.75/1.05      inference(demodulation,[status(thm)],[c_528,c_553]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_847,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_4,c_830]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_876,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 3.75/1.05      inference(light_normalisation,[status(thm)],[c_847,c_2]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_303,plain,
% 3.75/1.05      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_848,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_303,c_830]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_873,plain,
% 3.75/1.05      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
% 3.75/1.05      inference(light_normalisation,[status(thm)],[c_848,c_2]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_877,plain,
% 3.75/1.05      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.75/1.05      inference(demodulation,[status(thm)],[c_876,c_873]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_0,plain,
% 3.75/1.05      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.75/1.05      inference(cnf_transformation,[],[f22]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_6,negated_conjecture,
% 3.75/1.05      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.75/1.05      inference(cnf_transformation,[],[f46]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_401,plain,
% 3.75/1.05      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_5,plain,
% 3.75/1.05      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.75/1.05      inference(cnf_transformation,[],[f45]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_87,plain,
% 3.75/1.05      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.75/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_1,plain,
% 3.75/1.05      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.75/1.05      inference(cnf_transformation,[],[f24]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_88,plain,
% 3.75/1.05      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.75/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_318,plain,
% 3.75/1.05      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.75/1.05      inference(superposition,[status(thm)],[c_87,c_88]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_1361,plain,
% 3.75/1.05      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.75/1.05      inference(demodulation,[status(thm)],[c_401,c_318]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_10277,plain,
% 3.75/1.05      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 3.75/1.05      inference(demodulation,[status(thm)],[c_877,c_1361]) ).
% 3.75/1.05  
% 3.75/1.05  cnf(c_10281,plain,
% 3.75/1.05      ( $false ),
% 3.75/1.05      inference(equality_resolution_simp,[status(thm)],[c_10277]) ).
% 3.75/1.05  
% 3.75/1.05  
% 3.75/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/1.05  
% 3.75/1.05  ------                               Statistics
% 3.75/1.05  
% 3.75/1.05  ------ Selected
% 3.75/1.05  
% 3.75/1.05  total_time:                             0.354
% 3.75/1.05  
%------------------------------------------------------------------------------
