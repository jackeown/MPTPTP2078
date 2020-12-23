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
% DateTime   : Thu Dec  3 11:28:59 EST 2020

% Result     : CounterSatisfiable 3.70s
% Output     : Saturation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 173 expanded)
%              Number of clauses        :   24 (  44 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 294 expanded)
%              Number of equality atoms :  107 ( 282 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f38,f30,f54,f42])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).

fof(f49,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f56,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f39,f50,f52])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_479,plain,
    ( ~ iProver_ARSWP_18
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_591,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_18 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_10,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_832,plain,
    ( ~ iProver_ARSWP_18
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(resolution,[status(thm)],[c_479,c_10])).

cnf(c_833,plain,
    ( X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_18 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_835,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
    | sK0 = sK1
    | iProver_ARSWP_18 != iProver_top ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_915,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_18 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_10,c_835])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_476,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_3])).

cnf(c_594,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_924,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_18 != iProver_top
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_594])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_473,plain,
    ( ~ iProver_ARSWP_12
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_597,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_1070,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_18 != iProver_top
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_597])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_474,plain,
    ( ~ iProver_ARSWP_13
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_596,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_13 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_923,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_18 != iProver_top
    | iProver_ARSWP_13 != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_596])).

cnf(c_697,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_13 != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_596])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_475,plain,
    ( ~ iProver_ARSWP_14
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_595,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_14 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.70/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.01  
% 3.70/1.01  ------  iProver source info
% 3.70/1.01  
% 3.70/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.01  git: non_committed_changes: false
% 3.70/1.01  git: last_make_outside_of_git: false
% 3.70/1.01  
% 3.70/1.01  ------ 
% 3.70/1.01  ------ Parsing...
% 3.70/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  ------ Proving...
% 3.70/1.01  ------ Problem Properties 
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  clauses                                 12
% 3.70/1.01  conjectures                             2
% 3.70/1.01  EPR                                     1
% 3.70/1.01  Horn                                    11
% 3.70/1.01  unary                                   11
% 3.70/1.01  binary                                  0
% 3.70/1.01  lits                                    14
% 3.70/1.01  lits eq                                 14
% 3.70/1.01  fd_pure                                 0
% 3.70/1.01  fd_pseudo                               0
% 3.70/1.01  fd_cond                                 0
% 3.70/1.01  fd_pseudo_cond                          1
% 3.70/1.01  AC symbols                              0
% 3.70/1.01  
% 3.70/1.01  ------ Input Options Time Limit: Unbounded
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.70/1.01  Current options:
% 3.70/1.01  ------ 
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Proving...
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  
% 3.70/1.01  ------ Proving...
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  
% 3.70/1.01  ------ Proving...
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.01  
% 3.70/1.01  ------ Proving...
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  % SZS output start Saturation for theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  fof(f11,axiom,(
% 3.70/1.01    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f25,plain,(
% 3.70/1.01    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.70/1.01    inference(ennf_transformation,[],[f11])).
% 3.70/1.01  
% 3.70/1.01  fof(f38,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.70/1.01    inference(cnf_transformation,[],[f25])).
% 3.70/1.01  
% 3.70/1.01  fof(f3,axiom,(
% 3.70/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f30,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.70/1.01    inference(cnf_transformation,[],[f3])).
% 3.70/1.01  
% 3.70/1.01  fof(f14,axiom,(
% 3.70/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f41,plain,(
% 3.70/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f14])).
% 3.70/1.01  
% 3.70/1.01  fof(f54,plain,(
% 3.70/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f41,f42])).
% 3.70/1.01  
% 3.70/1.01  fof(f15,axiom,(
% 3.70/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f42,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f15])).
% 3.70/1.01  
% 3.70/1.01  fof(f62,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.70/1.01    inference(definition_unfolding,[],[f38,f30,f54,f42])).
% 3.70/1.01  
% 3.70/1.01  fof(f21,conjecture,(
% 3.70/1.01    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f22,negated_conjecture,(
% 3.70/1.01    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.70/1.01    inference(negated_conjecture,[],[f21])).
% 3.70/1.01  
% 3.70/1.01  fof(f26,plain,(
% 3.70/1.01    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.70/1.01    inference(ennf_transformation,[],[f22])).
% 3.70/1.01  
% 3.70/1.01  fof(f27,plain,(
% 3.70/1.01    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 3.70/1.01    introduced(choice_axiom,[])).
% 3.70/1.01  
% 3.70/1.01  fof(f28,plain,(
% 3.70/1.01    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 3.70/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).
% 3.70/1.01  
% 3.70/1.01  fof(f49,plain,(
% 3.70/1.01    sK0 != sK1),
% 3.70/1.01    inference(cnf_transformation,[],[f28])).
% 3.70/1.01  
% 3.70/1.01  fof(f4,axiom,(
% 3.70/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f31,plain,(
% 3.70/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f4])).
% 3.70/1.01  
% 3.70/1.01  fof(f16,axiom,(
% 3.70/1.01    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f43,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f16])).
% 3.70/1.01  
% 3.70/1.01  fof(f17,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f44,plain,(
% 3.70/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f17])).
% 3.70/1.01  
% 3.70/1.01  fof(f18,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f45,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f18])).
% 3.70/1.01  
% 3.70/1.01  fof(f19,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f46,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f19])).
% 3.70/1.01  
% 3.70/1.01  fof(f20,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f47,plain,(
% 3.70/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f20])).
% 3.70/1.01  
% 3.70/1.01  fof(f51,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f46,f47])).
% 3.70/1.01  
% 3.70/1.01  fof(f52,plain,(
% 3.70/1.01    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f45,f51])).
% 3.70/1.01  
% 3.70/1.01  fof(f53,plain,(
% 3.70/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f44,f52])).
% 3.70/1.01  
% 3.70/1.01  fof(f56,plain,(
% 3.70/1.01    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f43,f53])).
% 3.70/1.01  
% 3.70/1.01  fof(f12,axiom,(
% 3.70/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f39,plain,(
% 3.70/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f12])).
% 3.70/1.01  
% 3.70/1.01  fof(f5,axiom,(
% 3.70/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f32,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.70/1.01    inference(cnf_transformation,[],[f5])).
% 3.70/1.01  
% 3.70/1.01  fof(f50,plain,(
% 3.70/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f32,f30])).
% 3.70/1.01  
% 3.70/1.01  fof(f57,plain,(
% 3.70/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.70/1.01    inference(definition_unfolding,[],[f39,f50,f52])).
% 3.70/1.01  
% 3.70/1.01  fof(f2,axiom,(
% 3.70/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.70/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.01  
% 3.70/1.01  fof(f23,plain,(
% 3.70/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.70/1.01    inference(rectify,[],[f2])).
% 3.70/1.01  
% 3.70/1.01  fof(f29,plain,(
% 3.70/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.70/1.01    inference(cnf_transformation,[],[f23])).
% 3.70/1.01  
% 3.70/1.01  cnf(c_8,plain,
% 3.70/1.01      ( X0 = X1
% 3.70/1.01      | X2 = X1
% 3.70/1.01      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 3.70/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_479,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_18
% 3.70/1.01      | X0 = X1
% 3.70/1.01      | X2 = X1
% 3.70/1.01      | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.70/1.01      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_591,plain,
% 3.70/1.01      ( X0 = X1
% 3.70/1.01      | X2 = X1
% 3.70/1.01      | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_10,negated_conjecture,
% 3.70/1.01      ( sK0 != sK1 ),
% 3.70/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_832,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_18
% 3.70/1.01      | X0 = sK1
% 3.70/1.01      | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.70/1.01      inference(resolution,[status(thm)],[c_479,c_10]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_833,plain,
% 3.70/1.01      ( X0 = sK1
% 3.70/1.01      | arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_835,plain,
% 3.70/1.01      ( arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
% 3.70/1.01      | sK0 = sK1
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top ),
% 3.70/1.01      inference(instantiation,[status(thm)],[c_833]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_915,plain,
% 3.70/1.01      ( arAF0_k5_xboole_0_0 = arAF0_k1_enumset1_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top ),
% 3.70/1.01      inference(global_propositional_subsumption,
% 3.70/1.01                [status(thm)],
% 3.70/1.01                [c_591,c_10,c_835]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_3,plain,
% 3.70/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_476,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_15 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.70/1.01      inference(arg_filter_abstr,[status(unp)],[c_3]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_594,plain,
% 3.70/1.01      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_15 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_924,plain,
% 3.70/1.01      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top
% 3.70/1.01      | iProver_ARSWP_15 != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_915,c_594]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_0,plain,
% 3.70/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 3.70/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_473,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_12 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 3.70/1.01      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_597,plain,
% 3.70/1.01      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.70/1.01      | iProver_ARSWP_12 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1070,plain,
% 3.70/1.01      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top
% 3.70/1.01      | iProver_ARSWP_15 != iProver_top
% 3.70/1.01      | iProver_ARSWP_12 != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_924,c_597]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_1,plain,
% 3.70/1.01      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.70/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_474,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_13 | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.70/1.01      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_596,plain,
% 3.70/1.01      ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.70/1.01      | iProver_ARSWP_13 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_923,plain,
% 3.70/1.01      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.70/1.01      | iProver_ARSWP_18 != iProver_top
% 3.70/1.01      | iProver_ARSWP_13 != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_915,c_596]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_697,plain,
% 3.70/1.01      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.70/1.01      | iProver_ARSWP_15 != iProver_top
% 3.70/1.01      | iProver_ARSWP_13 != iProver_top ),
% 3.70/1.01      inference(superposition,[status(thm)],[c_594,c_596]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_2,plain,
% 3.70/1.01      ( k3_xboole_0(X0,X0) = X0 ),
% 3.70/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_475,plain,
% 3.70/1.01      ( ~ iProver_ARSWP_14 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.70/1.01      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.70/1.01  
% 3.70/1.01  cnf(c_595,plain,
% 3.70/1.01      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_14 != iProver_top ),
% 3.70/1.01      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 3.70/1.01  
% 3.70/1.01  
% 3.70/1.01  % SZS output end Saturation for theBenchmark.p
% 3.70/1.01  
% 3.70/1.01  ------                               Statistics
% 3.70/1.01  
% 3.70/1.01  ------ Selected
% 3.70/1.01  
% 3.70/1.01  total_time:                             0.076
% 3.70/1.01  
%------------------------------------------------------------------------------
