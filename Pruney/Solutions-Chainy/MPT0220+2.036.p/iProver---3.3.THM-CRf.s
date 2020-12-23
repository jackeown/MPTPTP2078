%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:32 EST 2020

% Result     : Theorem 54.88s
% Output     : CNFRefutation 54.88s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 150 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 158 expanded)
%              Number of equality atoms :   67 ( 147 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f47,f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f40,f41,f47,f46,f46])).

cnf(c_6,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_88,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_89,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_259,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_88,c_89])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_112,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1319,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_259,c_112])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_96,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_1326,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = X1 ),
    inference(demodulation,[status(thm)],[c_1319,c_96])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_363,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_68196,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1326,c_363])).

cnf(c_68197,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_68196])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 54.88/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.88/7.49  
% 54.88/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.88/7.49  
% 54.88/7.49  ------  iProver source info
% 54.88/7.49  
% 54.88/7.49  git: date: 2020-06-30 10:37:57 +0100
% 54.88/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.88/7.49  git: non_committed_changes: false
% 54.88/7.49  git: last_make_outside_of_git: false
% 54.88/7.49  
% 54.88/7.49  ------ 
% 54.88/7.49  
% 54.88/7.49  ------ Input Options
% 54.88/7.49  
% 54.88/7.49  --out_options                           all
% 54.88/7.49  --tptp_safe_out                         true
% 54.88/7.49  --problem_path                          ""
% 54.88/7.49  --include_path                          ""
% 54.88/7.49  --clausifier                            res/vclausify_rel
% 54.88/7.49  --clausifier_options                    --mode clausify
% 54.88/7.49  --stdin                                 false
% 54.88/7.49  --stats_out                             sel
% 54.88/7.49  
% 54.88/7.49  ------ General Options
% 54.88/7.49  
% 54.88/7.49  --fof                                   false
% 54.88/7.49  --time_out_real                         604.99
% 54.88/7.49  --time_out_virtual                      -1.
% 54.88/7.49  --symbol_type_check                     false
% 54.88/7.49  --clausify_out                          false
% 54.88/7.49  --sig_cnt_out                           false
% 54.88/7.49  --trig_cnt_out                          false
% 54.88/7.49  --trig_cnt_out_tolerance                1.
% 54.88/7.49  --trig_cnt_out_sk_spl                   false
% 54.88/7.49  --abstr_cl_out                          false
% 54.88/7.49  
% 54.88/7.49  ------ Global Options
% 54.88/7.49  
% 54.88/7.49  --schedule                              none
% 54.88/7.49  --add_important_lit                     false
% 54.88/7.49  --prop_solver_per_cl                    1000
% 54.88/7.49  --min_unsat_core                        false
% 54.88/7.49  --soft_assumptions                      false
% 54.88/7.49  --soft_lemma_size                       3
% 54.88/7.49  --prop_impl_unit_size                   0
% 54.88/7.49  --prop_impl_unit                        []
% 54.88/7.49  --share_sel_clauses                     true
% 54.88/7.49  --reset_solvers                         false
% 54.88/7.49  --bc_imp_inh                            [conj_cone]
% 54.88/7.49  --conj_cone_tolerance                   3.
% 54.88/7.49  --extra_neg_conj                        none
% 54.88/7.49  --large_theory_mode                     true
% 54.88/7.49  --prolific_symb_bound                   200
% 54.88/7.49  --lt_threshold                          2000
% 54.88/7.49  --clause_weak_htbl                      true
% 54.88/7.49  --gc_record_bc_elim                     false
% 54.88/7.49  
% 54.88/7.49  ------ Preprocessing Options
% 54.88/7.49  
% 54.88/7.49  --preprocessing_flag                    true
% 54.88/7.49  --time_out_prep_mult                    0.1
% 54.88/7.49  --splitting_mode                        input
% 54.88/7.49  --splitting_grd                         true
% 54.88/7.49  --splitting_cvd                         false
% 54.88/7.49  --splitting_cvd_svl                     false
% 54.88/7.49  --splitting_nvd                         32
% 54.88/7.49  --sub_typing                            true
% 54.88/7.49  --prep_gs_sim                           false
% 54.88/7.49  --prep_unflatten                        true
% 54.88/7.49  --prep_res_sim                          true
% 54.88/7.49  --prep_upred                            true
% 54.88/7.49  --prep_sem_filter                       exhaustive
% 54.88/7.49  --prep_sem_filter_out                   false
% 54.88/7.49  --pred_elim                             false
% 54.88/7.49  --res_sim_input                         true
% 54.88/7.49  --eq_ax_congr_red                       true
% 54.88/7.49  --pure_diseq_elim                       true
% 54.88/7.49  --brand_transform                       false
% 54.88/7.49  --non_eq_to_eq                          false
% 54.88/7.49  --prep_def_merge                        true
% 54.88/7.49  --prep_def_merge_prop_impl              false
% 54.88/7.49  --prep_def_merge_mbd                    true
% 54.88/7.49  --prep_def_merge_tr_red                 false
% 54.88/7.49  --prep_def_merge_tr_cl                  false
% 54.88/7.49  --smt_preprocessing                     true
% 54.88/7.49  --smt_ac_axioms                         fast
% 54.88/7.49  --preprocessed_out                      false
% 54.88/7.49  --preprocessed_stats                    false
% 54.88/7.49  
% 54.88/7.49  ------ Abstraction refinement Options
% 54.88/7.49  
% 54.88/7.49  --abstr_ref                             []
% 54.88/7.49  --abstr_ref_prep                        false
% 54.88/7.49  --abstr_ref_until_sat                   false
% 54.88/7.49  --abstr_ref_sig_restrict                funpre
% 54.88/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 54.88/7.49  --abstr_ref_under                       []
% 54.88/7.49  
% 54.88/7.49  ------ SAT Options
% 54.88/7.49  
% 54.88/7.49  --sat_mode                              false
% 54.88/7.49  --sat_fm_restart_options                ""
% 54.88/7.49  --sat_gr_def                            false
% 54.88/7.49  --sat_epr_types                         true
% 54.88/7.49  --sat_non_cyclic_types                  false
% 54.88/7.49  --sat_finite_models                     false
% 54.88/7.49  --sat_fm_lemmas                         false
% 54.88/7.49  --sat_fm_prep                           false
% 54.88/7.49  --sat_fm_uc_incr                        true
% 54.88/7.49  --sat_out_model                         small
% 54.88/7.49  --sat_out_clauses                       false
% 54.88/7.49  
% 54.88/7.49  ------ QBF Options
% 54.88/7.49  
% 54.88/7.49  --qbf_mode                              false
% 54.88/7.49  --qbf_elim_univ                         false
% 54.88/7.49  --qbf_dom_inst                          none
% 54.88/7.49  --qbf_dom_pre_inst                      false
% 54.88/7.49  --qbf_sk_in                             false
% 54.88/7.49  --qbf_pred_elim                         true
% 54.88/7.49  --qbf_split                             512
% 54.88/7.49  
% 54.88/7.49  ------ BMC1 Options
% 54.88/7.49  
% 54.88/7.49  --bmc1_incremental                      false
% 54.88/7.49  --bmc1_axioms                           reachable_all
% 54.88/7.49  --bmc1_min_bound                        0
% 54.88/7.49  --bmc1_max_bound                        -1
% 54.88/7.49  --bmc1_max_bound_default                -1
% 54.88/7.49  --bmc1_symbol_reachability              true
% 54.88/7.49  --bmc1_property_lemmas                  false
% 54.88/7.49  --bmc1_k_induction                      false
% 54.88/7.49  --bmc1_non_equiv_states                 false
% 54.88/7.49  --bmc1_deadlock                         false
% 54.88/7.49  --bmc1_ucm                              false
% 54.88/7.49  --bmc1_add_unsat_core                   none
% 54.88/7.49  --bmc1_unsat_core_children              false
% 54.88/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 54.88/7.49  --bmc1_out_stat                         full
% 54.88/7.49  --bmc1_ground_init                      false
% 54.88/7.49  --bmc1_pre_inst_next_state              false
% 54.88/7.49  --bmc1_pre_inst_state                   false
% 54.88/7.49  --bmc1_pre_inst_reach_state             false
% 54.88/7.49  --bmc1_out_unsat_core                   false
% 54.88/7.49  --bmc1_aig_witness_out                  false
% 54.88/7.49  --bmc1_verbose                          false
% 54.88/7.49  --bmc1_dump_clauses_tptp                false
% 54.88/7.49  --bmc1_dump_unsat_core_tptp             false
% 54.88/7.49  --bmc1_dump_file                        -
% 54.88/7.49  --bmc1_ucm_expand_uc_limit              128
% 54.88/7.49  --bmc1_ucm_n_expand_iterations          6
% 54.88/7.49  --bmc1_ucm_extend_mode                  1
% 54.88/7.49  --bmc1_ucm_init_mode                    2
% 54.88/7.49  --bmc1_ucm_cone_mode                    none
% 54.88/7.49  --bmc1_ucm_reduced_relation_type        0
% 54.88/7.49  --bmc1_ucm_relax_model                  4
% 54.88/7.49  --bmc1_ucm_full_tr_after_sat            true
% 54.88/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 54.88/7.49  --bmc1_ucm_layered_model                none
% 54.88/7.49  --bmc1_ucm_max_lemma_size               10
% 54.88/7.49  
% 54.88/7.49  ------ AIG Options
% 54.88/7.49  
% 54.88/7.49  --aig_mode                              false
% 54.88/7.49  
% 54.88/7.49  ------ Instantiation Options
% 54.88/7.49  
% 54.88/7.49  --instantiation_flag                    true
% 54.88/7.49  --inst_sos_flag                         false
% 54.88/7.49  --inst_sos_phase                        true
% 54.88/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.88/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.88/7.49  --inst_lit_sel_side                     num_symb
% 54.88/7.49  --inst_solver_per_active                1400
% 54.88/7.49  --inst_solver_calls_frac                1.
% 54.88/7.49  --inst_passive_queue_type               priority_queues
% 54.88/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.88/7.49  --inst_passive_queues_freq              [25;2]
% 54.88/7.49  --inst_dismatching                      true
% 54.88/7.49  --inst_eager_unprocessed_to_passive     true
% 54.88/7.49  --inst_prop_sim_given                   true
% 54.88/7.49  --inst_prop_sim_new                     false
% 54.88/7.49  --inst_subs_new                         false
% 54.88/7.49  --inst_eq_res_simp                      false
% 54.88/7.49  --inst_subs_given                       false
% 54.88/7.49  --inst_orphan_elimination               true
% 54.88/7.49  --inst_learning_loop_flag               true
% 54.88/7.49  --inst_learning_start                   3000
% 54.88/7.49  --inst_learning_factor                  2
% 54.88/7.49  --inst_start_prop_sim_after_learn       3
% 54.88/7.49  --inst_sel_renew                        solver
% 54.88/7.49  --inst_lit_activity_flag                true
% 54.88/7.49  --inst_restr_to_given                   false
% 54.88/7.49  --inst_activity_threshold               500
% 54.88/7.49  --inst_out_proof                        true
% 54.88/7.49  
% 54.88/7.49  ------ Resolution Options
% 54.88/7.49  
% 54.88/7.49  --resolution_flag                       true
% 54.88/7.49  --res_lit_sel                           adaptive
% 54.88/7.49  --res_lit_sel_side                      none
% 54.88/7.49  --res_ordering                          kbo
% 54.88/7.49  --res_to_prop_solver                    active
% 54.88/7.49  --res_prop_simpl_new                    false
% 54.88/7.49  --res_prop_simpl_given                  true
% 54.88/7.49  --res_passive_queue_type                priority_queues
% 54.88/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.88/7.49  --res_passive_queues_freq               [15;5]
% 54.88/7.49  --res_forward_subs                      full
% 54.88/7.49  --res_backward_subs                     full
% 54.88/7.49  --res_forward_subs_resolution           true
% 54.88/7.49  --res_backward_subs_resolution          true
% 54.88/7.49  --res_orphan_elimination                true
% 54.88/7.49  --res_time_limit                        2.
% 54.88/7.49  --res_out_proof                         true
% 54.88/7.49  
% 54.88/7.49  ------ Superposition Options
% 54.88/7.49  
% 54.88/7.49  --superposition_flag                    true
% 54.88/7.49  --sup_passive_queue_type                priority_queues
% 54.88/7.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.88/7.49  --sup_passive_queues_freq               [1;4]
% 54.88/7.49  --demod_completeness_check              fast
% 54.88/7.49  --demod_use_ground                      true
% 54.88/7.49  --sup_to_prop_solver                    passive
% 54.88/7.49  --sup_prop_simpl_new                    true
% 54.88/7.49  --sup_prop_simpl_given                  true
% 54.88/7.49  --sup_fun_splitting                     false
% 54.88/7.49  --sup_smt_interval                      50000
% 54.88/7.49  
% 54.88/7.49  ------ Superposition Simplification Setup
% 54.88/7.49  
% 54.88/7.49  --sup_indices_passive                   []
% 54.88/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 54.88/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_full_bw                           [BwDemod]
% 54.88/7.49  --sup_immed_triv                        [TrivRules]
% 54.88/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.88/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_immed_bw_main                     []
% 54.88/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.88/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 54.88/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.88/7.49  
% 54.88/7.49  ------ Combination Options
% 54.88/7.49  
% 54.88/7.49  --comb_res_mult                         3
% 54.88/7.49  --comb_sup_mult                         2
% 54.88/7.49  --comb_inst_mult                        10
% 54.88/7.49  
% 54.88/7.49  ------ Debug Options
% 54.88/7.49  
% 54.88/7.49  --dbg_backtrace                         false
% 54.88/7.49  --dbg_dump_prop_clauses                 false
% 54.88/7.49  --dbg_dump_prop_clauses_file            -
% 54.88/7.49  --dbg_out_stat                          false
% 54.88/7.49  ------ Parsing...
% 54.88/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.88/7.49  
% 54.88/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 54.88/7.49  
% 54.88/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.88/7.49  
% 54.88/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.88/7.49  ------ Proving...
% 54.88/7.49  ------ Problem Properties 
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  clauses                                 8
% 54.88/7.49  conjectures                             1
% 54.88/7.49  EPR                                     0
% 54.88/7.49  Horn                                    8
% 54.88/7.49  unary                                   7
% 54.88/7.49  binary                                  1
% 54.88/7.49  lits                                    9
% 54.88/7.49  lits eq                                 7
% 54.88/7.49  fd_pure                                 0
% 54.88/7.49  fd_pseudo                               0
% 54.88/7.49  fd_cond                                 0
% 54.88/7.49  fd_pseudo_cond                          0
% 54.88/7.49  AC symbols                              1
% 54.88/7.49  
% 54.88/7.49  ------ Input Options Time Limit: Unbounded
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  ------ 
% 54.88/7.49  Current options:
% 54.88/7.49  ------ 
% 54.88/7.49  
% 54.88/7.49  ------ Input Options
% 54.88/7.49  
% 54.88/7.49  --out_options                           all
% 54.88/7.49  --tptp_safe_out                         true
% 54.88/7.49  --problem_path                          ""
% 54.88/7.49  --include_path                          ""
% 54.88/7.49  --clausifier                            res/vclausify_rel
% 54.88/7.49  --clausifier_options                    --mode clausify
% 54.88/7.49  --stdin                                 false
% 54.88/7.49  --stats_out                             sel
% 54.88/7.49  
% 54.88/7.49  ------ General Options
% 54.88/7.49  
% 54.88/7.49  --fof                                   false
% 54.88/7.49  --time_out_real                         604.99
% 54.88/7.49  --time_out_virtual                      -1.
% 54.88/7.49  --symbol_type_check                     false
% 54.88/7.49  --clausify_out                          false
% 54.88/7.49  --sig_cnt_out                           false
% 54.88/7.49  --trig_cnt_out                          false
% 54.88/7.49  --trig_cnt_out_tolerance                1.
% 54.88/7.49  --trig_cnt_out_sk_spl                   false
% 54.88/7.49  --abstr_cl_out                          false
% 54.88/7.49  
% 54.88/7.49  ------ Global Options
% 54.88/7.49  
% 54.88/7.49  --schedule                              none
% 54.88/7.49  --add_important_lit                     false
% 54.88/7.49  --prop_solver_per_cl                    1000
% 54.88/7.49  --min_unsat_core                        false
% 54.88/7.49  --soft_assumptions                      false
% 54.88/7.49  --soft_lemma_size                       3
% 54.88/7.49  --prop_impl_unit_size                   0
% 54.88/7.49  --prop_impl_unit                        []
% 54.88/7.49  --share_sel_clauses                     true
% 54.88/7.49  --reset_solvers                         false
% 54.88/7.49  --bc_imp_inh                            [conj_cone]
% 54.88/7.49  --conj_cone_tolerance                   3.
% 54.88/7.49  --extra_neg_conj                        none
% 54.88/7.49  --large_theory_mode                     true
% 54.88/7.49  --prolific_symb_bound                   200
% 54.88/7.49  --lt_threshold                          2000
% 54.88/7.49  --clause_weak_htbl                      true
% 54.88/7.49  --gc_record_bc_elim                     false
% 54.88/7.49  
% 54.88/7.49  ------ Preprocessing Options
% 54.88/7.49  
% 54.88/7.49  --preprocessing_flag                    true
% 54.88/7.49  --time_out_prep_mult                    0.1
% 54.88/7.49  --splitting_mode                        input
% 54.88/7.49  --splitting_grd                         true
% 54.88/7.49  --splitting_cvd                         false
% 54.88/7.49  --splitting_cvd_svl                     false
% 54.88/7.49  --splitting_nvd                         32
% 54.88/7.49  --sub_typing                            true
% 54.88/7.49  --prep_gs_sim                           false
% 54.88/7.49  --prep_unflatten                        true
% 54.88/7.49  --prep_res_sim                          true
% 54.88/7.49  --prep_upred                            true
% 54.88/7.49  --prep_sem_filter                       exhaustive
% 54.88/7.49  --prep_sem_filter_out                   false
% 54.88/7.49  --pred_elim                             false
% 54.88/7.49  --res_sim_input                         true
% 54.88/7.49  --eq_ax_congr_red                       true
% 54.88/7.49  --pure_diseq_elim                       true
% 54.88/7.49  --brand_transform                       false
% 54.88/7.49  --non_eq_to_eq                          false
% 54.88/7.49  --prep_def_merge                        true
% 54.88/7.49  --prep_def_merge_prop_impl              false
% 54.88/7.49  --prep_def_merge_mbd                    true
% 54.88/7.49  --prep_def_merge_tr_red                 false
% 54.88/7.49  --prep_def_merge_tr_cl                  false
% 54.88/7.49  --smt_preprocessing                     true
% 54.88/7.49  --smt_ac_axioms                         fast
% 54.88/7.49  --preprocessed_out                      false
% 54.88/7.49  --preprocessed_stats                    false
% 54.88/7.49  
% 54.88/7.49  ------ Abstraction refinement Options
% 54.88/7.49  
% 54.88/7.49  --abstr_ref                             []
% 54.88/7.49  --abstr_ref_prep                        false
% 54.88/7.49  --abstr_ref_until_sat                   false
% 54.88/7.49  --abstr_ref_sig_restrict                funpre
% 54.88/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 54.88/7.49  --abstr_ref_under                       []
% 54.88/7.49  
% 54.88/7.49  ------ SAT Options
% 54.88/7.49  
% 54.88/7.49  --sat_mode                              false
% 54.88/7.49  --sat_fm_restart_options                ""
% 54.88/7.49  --sat_gr_def                            false
% 54.88/7.49  --sat_epr_types                         true
% 54.88/7.49  --sat_non_cyclic_types                  false
% 54.88/7.49  --sat_finite_models                     false
% 54.88/7.49  --sat_fm_lemmas                         false
% 54.88/7.49  --sat_fm_prep                           false
% 54.88/7.49  --sat_fm_uc_incr                        true
% 54.88/7.49  --sat_out_model                         small
% 54.88/7.49  --sat_out_clauses                       false
% 54.88/7.49  
% 54.88/7.49  ------ QBF Options
% 54.88/7.49  
% 54.88/7.49  --qbf_mode                              false
% 54.88/7.49  --qbf_elim_univ                         false
% 54.88/7.49  --qbf_dom_inst                          none
% 54.88/7.49  --qbf_dom_pre_inst                      false
% 54.88/7.49  --qbf_sk_in                             false
% 54.88/7.49  --qbf_pred_elim                         true
% 54.88/7.49  --qbf_split                             512
% 54.88/7.49  
% 54.88/7.49  ------ BMC1 Options
% 54.88/7.49  
% 54.88/7.49  --bmc1_incremental                      false
% 54.88/7.49  --bmc1_axioms                           reachable_all
% 54.88/7.49  --bmc1_min_bound                        0
% 54.88/7.49  --bmc1_max_bound                        -1
% 54.88/7.49  --bmc1_max_bound_default                -1
% 54.88/7.49  --bmc1_symbol_reachability              true
% 54.88/7.49  --bmc1_property_lemmas                  false
% 54.88/7.49  --bmc1_k_induction                      false
% 54.88/7.49  --bmc1_non_equiv_states                 false
% 54.88/7.49  --bmc1_deadlock                         false
% 54.88/7.49  --bmc1_ucm                              false
% 54.88/7.49  --bmc1_add_unsat_core                   none
% 54.88/7.49  --bmc1_unsat_core_children              false
% 54.88/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 54.88/7.49  --bmc1_out_stat                         full
% 54.88/7.49  --bmc1_ground_init                      false
% 54.88/7.49  --bmc1_pre_inst_next_state              false
% 54.88/7.49  --bmc1_pre_inst_state                   false
% 54.88/7.49  --bmc1_pre_inst_reach_state             false
% 54.88/7.49  --bmc1_out_unsat_core                   false
% 54.88/7.49  --bmc1_aig_witness_out                  false
% 54.88/7.49  --bmc1_verbose                          false
% 54.88/7.49  --bmc1_dump_clauses_tptp                false
% 54.88/7.49  --bmc1_dump_unsat_core_tptp             false
% 54.88/7.49  --bmc1_dump_file                        -
% 54.88/7.49  --bmc1_ucm_expand_uc_limit              128
% 54.88/7.49  --bmc1_ucm_n_expand_iterations          6
% 54.88/7.49  --bmc1_ucm_extend_mode                  1
% 54.88/7.49  --bmc1_ucm_init_mode                    2
% 54.88/7.49  --bmc1_ucm_cone_mode                    none
% 54.88/7.49  --bmc1_ucm_reduced_relation_type        0
% 54.88/7.49  --bmc1_ucm_relax_model                  4
% 54.88/7.49  --bmc1_ucm_full_tr_after_sat            true
% 54.88/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 54.88/7.49  --bmc1_ucm_layered_model                none
% 54.88/7.49  --bmc1_ucm_max_lemma_size               10
% 54.88/7.49  
% 54.88/7.49  ------ AIG Options
% 54.88/7.49  
% 54.88/7.49  --aig_mode                              false
% 54.88/7.49  
% 54.88/7.49  ------ Instantiation Options
% 54.88/7.49  
% 54.88/7.49  --instantiation_flag                    true
% 54.88/7.49  --inst_sos_flag                         false
% 54.88/7.49  --inst_sos_phase                        true
% 54.88/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.88/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.88/7.49  --inst_lit_sel_side                     num_symb
% 54.88/7.49  --inst_solver_per_active                1400
% 54.88/7.49  --inst_solver_calls_frac                1.
% 54.88/7.49  --inst_passive_queue_type               priority_queues
% 54.88/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.88/7.49  --inst_passive_queues_freq              [25;2]
% 54.88/7.49  --inst_dismatching                      true
% 54.88/7.49  --inst_eager_unprocessed_to_passive     true
% 54.88/7.49  --inst_prop_sim_given                   true
% 54.88/7.49  --inst_prop_sim_new                     false
% 54.88/7.49  --inst_subs_new                         false
% 54.88/7.49  --inst_eq_res_simp                      false
% 54.88/7.49  --inst_subs_given                       false
% 54.88/7.49  --inst_orphan_elimination               true
% 54.88/7.49  --inst_learning_loop_flag               true
% 54.88/7.49  --inst_learning_start                   3000
% 54.88/7.49  --inst_learning_factor                  2
% 54.88/7.49  --inst_start_prop_sim_after_learn       3
% 54.88/7.49  --inst_sel_renew                        solver
% 54.88/7.49  --inst_lit_activity_flag                true
% 54.88/7.49  --inst_restr_to_given                   false
% 54.88/7.49  --inst_activity_threshold               500
% 54.88/7.49  --inst_out_proof                        true
% 54.88/7.49  
% 54.88/7.49  ------ Resolution Options
% 54.88/7.49  
% 54.88/7.49  --resolution_flag                       true
% 54.88/7.49  --res_lit_sel                           adaptive
% 54.88/7.49  --res_lit_sel_side                      none
% 54.88/7.49  --res_ordering                          kbo
% 54.88/7.49  --res_to_prop_solver                    active
% 54.88/7.49  --res_prop_simpl_new                    false
% 54.88/7.49  --res_prop_simpl_given                  true
% 54.88/7.49  --res_passive_queue_type                priority_queues
% 54.88/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.88/7.49  --res_passive_queues_freq               [15;5]
% 54.88/7.49  --res_forward_subs                      full
% 54.88/7.49  --res_backward_subs                     full
% 54.88/7.49  --res_forward_subs_resolution           true
% 54.88/7.49  --res_backward_subs_resolution          true
% 54.88/7.49  --res_orphan_elimination                true
% 54.88/7.49  --res_time_limit                        2.
% 54.88/7.49  --res_out_proof                         true
% 54.88/7.49  
% 54.88/7.49  ------ Superposition Options
% 54.88/7.49  
% 54.88/7.49  --superposition_flag                    true
% 54.88/7.49  --sup_passive_queue_type                priority_queues
% 54.88/7.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.88/7.49  --sup_passive_queues_freq               [1;4]
% 54.88/7.49  --demod_completeness_check              fast
% 54.88/7.49  --demod_use_ground                      true
% 54.88/7.49  --sup_to_prop_solver                    passive
% 54.88/7.49  --sup_prop_simpl_new                    true
% 54.88/7.49  --sup_prop_simpl_given                  true
% 54.88/7.49  --sup_fun_splitting                     false
% 54.88/7.49  --sup_smt_interval                      50000
% 54.88/7.49  
% 54.88/7.49  ------ Superposition Simplification Setup
% 54.88/7.49  
% 54.88/7.49  --sup_indices_passive                   []
% 54.88/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.88/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 54.88/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_full_bw                           [BwDemod]
% 54.88/7.49  --sup_immed_triv                        [TrivRules]
% 54.88/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.88/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_immed_bw_main                     []
% 54.88/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.88/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 54.88/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.88/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.88/7.49  
% 54.88/7.49  ------ Combination Options
% 54.88/7.49  
% 54.88/7.49  --comb_res_mult                         3
% 54.88/7.49  --comb_sup_mult                         2
% 54.88/7.49  --comb_inst_mult                        10
% 54.88/7.49  
% 54.88/7.49  ------ Debug Options
% 54.88/7.49  
% 54.88/7.49  --dbg_backtrace                         false
% 54.88/7.49  --dbg_dump_prop_clauses                 false
% 54.88/7.49  --dbg_dump_prop_clauses_file            -
% 54.88/7.49  --dbg_out_stat                          false
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  ------ Proving...
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  % SZS status Theorem for theBenchmark.p
% 54.88/7.49  
% 54.88/7.49   Resolution empty clause
% 54.88/7.49  
% 54.88/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 54.88/7.49  
% 54.88/7.49  fof(f16,axiom,(
% 54.88/7.49    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f39,plain,(
% 54.88/7.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 54.88/7.49    inference(cnf_transformation,[],[f16])).
% 54.88/7.49  
% 54.88/7.49  fof(f9,axiom,(
% 54.88/7.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f32,plain,(
% 54.88/7.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f9])).
% 54.88/7.49  
% 54.88/7.49  fof(f47,plain,(
% 54.88/7.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f32,f46])).
% 54.88/7.49  
% 54.88/7.49  fof(f10,axiom,(
% 54.88/7.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f33,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f10])).
% 54.88/7.49  
% 54.88/7.49  fof(f11,axiom,(
% 54.88/7.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f34,plain,(
% 54.88/7.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f11])).
% 54.88/7.49  
% 54.88/7.49  fof(f12,axiom,(
% 54.88/7.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f35,plain,(
% 54.88/7.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f12])).
% 54.88/7.49  
% 54.88/7.49  fof(f13,axiom,(
% 54.88/7.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f36,plain,(
% 54.88/7.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f13])).
% 54.88/7.49  
% 54.88/7.49  fof(f14,axiom,(
% 54.88/7.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f37,plain,(
% 54.88/7.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f14])).
% 54.88/7.49  
% 54.88/7.49  fof(f15,axiom,(
% 54.88/7.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f38,plain,(
% 54.88/7.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f15])).
% 54.88/7.49  
% 54.88/7.49  fof(f42,plain,(
% 54.88/7.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f37,f38])).
% 54.88/7.49  
% 54.88/7.49  fof(f43,plain,(
% 54.88/7.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f36,f42])).
% 54.88/7.49  
% 54.88/7.49  fof(f44,plain,(
% 54.88/7.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f35,f43])).
% 54.88/7.49  
% 54.88/7.49  fof(f45,plain,(
% 54.88/7.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f34,f44])).
% 54.88/7.49  
% 54.88/7.49  fof(f46,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f33,f45])).
% 54.88/7.49  
% 54.88/7.49  fof(f51,plain,(
% 54.88/7.49    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 54.88/7.49    inference(definition_unfolding,[],[f39,f47,f46])).
% 54.88/7.49  
% 54.88/7.49  fof(f3,axiom,(
% 54.88/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f19,plain,(
% 54.88/7.49    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 54.88/7.49    inference(unused_predicate_definition_removal,[],[f3])).
% 54.88/7.49  
% 54.88/7.49  fof(f20,plain,(
% 54.88/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 54.88/7.49    inference(ennf_transformation,[],[f19])).
% 54.88/7.49  
% 54.88/7.49  fof(f26,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f20])).
% 54.88/7.49  
% 54.88/7.49  fof(f4,axiom,(
% 54.88/7.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f27,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f4])).
% 54.88/7.49  
% 54.88/7.49  fof(f48,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f26,f27])).
% 54.88/7.49  
% 54.88/7.49  fof(f7,axiom,(
% 54.88/7.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f30,plain,(
% 54.88/7.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f7])).
% 54.88/7.49  
% 54.88/7.49  fof(f2,axiom,(
% 54.88/7.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f25,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f2])).
% 54.88/7.49  
% 54.88/7.49  fof(f5,axiom,(
% 54.88/7.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f28,plain,(
% 54.88/7.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 54.88/7.49    inference(cnf_transformation,[],[f5])).
% 54.88/7.49  
% 54.88/7.49  fof(f8,axiom,(
% 54.88/7.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f31,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f8])).
% 54.88/7.49  
% 54.88/7.49  fof(f41,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 54.88/7.49    inference(definition_unfolding,[],[f31,f27])).
% 54.88/7.49  
% 54.88/7.49  fof(f49,plain,(
% 54.88/7.49    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 54.88/7.49    inference(definition_unfolding,[],[f28,f41])).
% 54.88/7.49  
% 54.88/7.49  fof(f6,axiom,(
% 54.88/7.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f29,plain,(
% 54.88/7.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 54.88/7.49    inference(cnf_transformation,[],[f6])).
% 54.88/7.49  
% 54.88/7.49  fof(f50,plain,(
% 54.88/7.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 54.88/7.49    inference(definition_unfolding,[],[f29,f27])).
% 54.88/7.49  
% 54.88/7.49  fof(f1,axiom,(
% 54.88/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f24,plain,(
% 54.88/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 54.88/7.49    inference(cnf_transformation,[],[f1])).
% 54.88/7.49  
% 54.88/7.49  fof(f17,conjecture,(
% 54.88/7.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 54.88/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.88/7.49  
% 54.88/7.49  fof(f18,negated_conjecture,(
% 54.88/7.49    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 54.88/7.49    inference(negated_conjecture,[],[f17])).
% 54.88/7.49  
% 54.88/7.49  fof(f21,plain,(
% 54.88/7.49    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 54.88/7.49    inference(ennf_transformation,[],[f18])).
% 54.88/7.49  
% 54.88/7.49  fof(f22,plain,(
% 54.88/7.49    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 54.88/7.49    introduced(choice_axiom,[])).
% 54.88/7.49  
% 54.88/7.49  fof(f23,plain,(
% 54.88/7.49    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 54.88/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 54.88/7.49  
% 54.88/7.49  fof(f40,plain,(
% 54.88/7.49    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 54.88/7.49    inference(cnf_transformation,[],[f23])).
% 54.88/7.49  
% 54.88/7.49  fof(f52,plain,(
% 54.88/7.49    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 54.88/7.49    inference(definition_unfolding,[],[f40,f41,f47,f46,f46])).
% 54.88/7.49  
% 54.88/7.49  cnf(c_6,plain,
% 54.88/7.49      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 54.88/7.49      inference(cnf_transformation,[],[f51]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_88,plain,
% 54.88/7.49      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 54.88/7.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_2,plain,
% 54.88/7.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 54.88/7.49      inference(cnf_transformation,[],[f48]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_89,plain,
% 54.88/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 54.88/7.49      | r1_tarski(X0,X1) != iProver_top ),
% 54.88/7.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_259,plain,
% 54.88/7.49      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 54.88/7.49      inference(superposition,[status(thm)],[c_88,c_89]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_5,plain,
% 54.88/7.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 54.88/7.49      inference(cnf_transformation,[],[f30]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_1,plain,
% 54.88/7.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 54.88/7.49      inference(cnf_transformation,[],[f25]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_112,plain,
% 54.88/7.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 54.88/7.49      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_1319,plain,
% 54.88/7.49      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = k5_xboole_0(X1,k1_xboole_0) ),
% 54.88/7.49      inference(superposition,[status(thm)],[c_259,c_112]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_3,plain,
% 54.88/7.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 54.88/7.49      inference(cnf_transformation,[],[f49]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_4,plain,
% 54.88/7.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 54.88/7.49      inference(cnf_transformation,[],[f50]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_96,plain,
% 54.88/7.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 54.88/7.49      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_1326,plain,
% 54.88/7.49      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) = X1 ),
% 54.88/7.49      inference(demodulation,[status(thm)],[c_1319,c_96]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_0,plain,
% 54.88/7.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 54.88/7.49      inference(cnf_transformation,[],[f24]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_7,negated_conjecture,
% 54.88/7.49      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 54.88/7.49      inference(cnf_transformation,[],[f52]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_363,plain,
% 54.88/7.49      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 54.88/7.49      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_68196,plain,
% 54.88/7.49      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 54.88/7.49      inference(demodulation,[status(thm)],[c_1326,c_363]) ).
% 54.88/7.49  
% 54.88/7.49  cnf(c_68197,plain,
% 54.88/7.49      ( $false ),
% 54.88/7.49      inference(theory_normalisation,[status(thm)],[c_68196]) ).
% 54.88/7.49  
% 54.88/7.49  
% 54.88/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 54.88/7.49  
% 54.88/7.49  ------                               Statistics
% 54.88/7.49  
% 54.88/7.49  ------ Selected
% 54.88/7.49  
% 54.88/7.49  total_time:                             6.664
% 54.88/7.49  
%------------------------------------------------------------------------------
