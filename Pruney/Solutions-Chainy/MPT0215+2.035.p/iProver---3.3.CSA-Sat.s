%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:59 EST 2020

% Result     : CounterSatisfiable 3.50s
% Output     : Saturation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   91 (1198 expanded)
%              Number of clauses        :   48 ( 155 expanded)
%              Number of leaves         :   17 ( 382 expanded)
%              Depth                    :   19
%              Number of atoms          :  198 (1680 expanded)
%              Number of equality atoms :  185 (1635 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f52,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f53,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f36,f29,f52,f54,f53])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f47,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f37,f48,f49,f53])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_384,plain,
    ( ~ iProver_ARSWP_12
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_484,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_6,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_387,plain,
    ( ~ iProver_ARSWP_15
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_481,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_722,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_481])).

cnf(c_1027,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_722])).

cnf(c_1349,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1027])).

cnf(c_1484,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1349])).

cnf(c_8,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_943,plain,
    ( ~ iProver_ARSWP_15
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_387,c_8])).

cnf(c_945,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1092,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_8,c_945])).

cnf(c_22,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_21,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_599,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_1222,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_1092,c_599])).

cnf(c_1239,plain,
    ( ~ iProver_ARSWP_15
    | X0 != arAF0_k5_xboole_0_0
    | arAF0_k6_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_1222,c_22])).

cnf(c_617,plain,
    ( ~ iProver_ARSWP_12
    | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_599,c_384])).

cnf(c_1641,plain,
    ( ~ iProver_ARSWP_15
    | ~ iProver_ARSWP_12
    | arAF0_k6_enumset1_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1239,c_617])).

cnf(c_1642,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_1708,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1484,c_1642])).

cnf(c_723,plain,
    ( arAF0_k6_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_481])).

cnf(c_1725,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_723])).

cnf(c_725,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_481])).

cnf(c_1724,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_725])).

cnf(c_1495,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1349])).

cnf(c_708,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_8])).

cnf(c_28,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_174,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_175,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_713,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_8])).

cnf(c_882,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_15 != iProver_top ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_899,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_8,c_28,c_175,c_882])).

cnf(c_724,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_481])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_382,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_486,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_706,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_486])).

cnf(c_717,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_481])).

cnf(c_847,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_706,c_717])).

cnf(c_615,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_599,c_382])).

cnf(c_616,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_1307,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_616])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_383,plain,
    ( ~ iProver_ARSWP_11
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_485,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.00  
% 3.50/1.00  ------  iProver source info
% 3.50/1.00  
% 3.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.00  git: non_committed_changes: false
% 3.50/1.00  git: last_make_outside_of_git: false
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  ------ Parsing...
% 3.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  ------ Proving...
% 3.50/1.00  ------ Problem Properties 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  clauses                                 10
% 3.50/1.00  conjectures                             2
% 3.50/1.00  EPR                                     1
% 3.50/1.00  Horn                                    9
% 3.50/1.00  unary                                   9
% 3.50/1.00  binary                                  0
% 3.50/1.00  lits                                    12
% 3.50/1.00  lits eq                                 12
% 3.50/1.00  fd_pure                                 0
% 3.50/1.00  fd_pseudo                               0
% 3.50/1.00  fd_cond                                 0
% 3.50/1.00  fd_pseudo_cond                          1
% 3.50/1.00  AC symbols                              0
% 3.50/1.00  
% 3.50/1.00  ------ Input Options Time Limit: Unbounded
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.50/1.00  Current options:
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  % SZS output start Saturation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  fof(f4,axiom,(
% 3.50/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f30,plain,(
% 3.50/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f4])).
% 3.50/1.00  
% 3.50/1.00  fof(f10,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f24,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.50/1.00    inference(ennf_transformation,[],[f10])).
% 3.50/1.00  
% 3.50/1.00  fof(f36,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.50/1.00    inference(cnf_transformation,[],[f24])).
% 3.50/1.00  
% 3.50/1.00  fof(f3,axiom,(
% 3.50/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f29,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f3])).
% 3.50/1.00  
% 3.50/1.00  fof(f13,axiom,(
% 3.50/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f39,plain,(
% 3.50/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f13])).
% 3.50/1.00  
% 3.50/1.00  fof(f54,plain,(
% 3.50/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f39,f53])).
% 3.50/1.00  
% 3.50/1.00  fof(f14,axiom,(
% 3.50/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f40,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f14])).
% 3.50/1.00  
% 3.50/1.00  fof(f15,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f41,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f15])).
% 3.50/1.00  
% 3.50/1.00  fof(f16,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f42,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f16])).
% 3.50/1.00  
% 3.50/1.00  fof(f17,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f43,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f17])).
% 3.50/1.00  
% 3.50/1.00  fof(f18,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f44,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f18])).
% 3.50/1.00  
% 3.50/1.00  fof(f19,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f45,plain,(
% 3.50/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f19])).
% 3.50/1.00  
% 3.50/1.00  fof(f49,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f44,f45])).
% 3.50/1.00  
% 3.50/1.00  fof(f50,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f43,f49])).
% 3.50/1.00  
% 3.50/1.00  fof(f51,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f42,f50])).
% 3.50/1.00  
% 3.50/1.00  fof(f52,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f41,f51])).
% 3.50/1.00  
% 3.50/1.00  fof(f53,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f40,f52])).
% 3.50/1.00  
% 3.50/1.00  fof(f60,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.50/1.00    inference(definition_unfolding,[],[f36,f29,f52,f54,f53])).
% 3.50/1.00  
% 3.50/1.00  fof(f20,conjecture,(
% 3.50/1.00    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f21,negated_conjecture,(
% 3.50/1.00    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.50/1.00    inference(negated_conjecture,[],[f20])).
% 3.50/1.00  
% 3.50/1.00  fof(f25,plain,(
% 3.50/1.00    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.50/1.00    inference(ennf_transformation,[],[f21])).
% 3.50/1.00  
% 3.50/1.00  fof(f26,plain,(
% 3.50/1.00    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f27,plain,(
% 3.50/1.00    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 3.50/1.00  
% 3.50/1.00  fof(f47,plain,(
% 3.50/1.00    sK0 != sK1),
% 3.50/1.00    inference(cnf_transformation,[],[f27])).
% 3.50/1.00  
% 3.50/1.00  fof(f11,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f37,plain,(
% 3.50/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f11])).
% 3.50/1.00  
% 3.50/1.00  fof(f5,axiom,(
% 3.50/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f31,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f5])).
% 3.50/1.00  
% 3.50/1.00  fof(f48,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f31,f29])).
% 3.50/1.00  
% 3.50/1.00  fof(f56,plain,(
% 3.50/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f37,f48,f49,f53])).
% 3.50/1.00  
% 3.50/1.00  fof(f2,axiom,(
% 3.50/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f22,plain,(
% 3.50/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.50/1.00    inference(rectify,[],[f2])).
% 3.50/1.00  
% 3.50/1.00  fof(f28,plain,(
% 3.50/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f22])).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2,plain,
% 3.50/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_384,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_12 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.50/1.00      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_484,plain,
% 3.50/1.00      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_6,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | X2 = X1
% 3.50/1.00      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 3.50/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_387,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15
% 3.50/1.00      | X0 = X1
% 3.50/1.00      | X2 = X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.50/1.00      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_481,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | X2 = X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_722,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = X0
% 3.50/1.00      | arAF0_k6_enumset1_0 = X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 != X0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_481]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1027,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = X0
% 3.50/1.00      | arAF0_k6_enumset1_0 = X1
% 3.50/1.00      | k1_xboole_0 != X0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_484,c_722]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1349,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = X0
% 3.50/1.00      | arAF0_k6_enumset1_0 = k1_xboole_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_1027]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1484,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = k1_xboole_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1349,c_1349]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_8,negated_conjecture,
% 3.50/1.00      ( sK0 != sK1 ),
% 3.50/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_943,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15
% 3.50/1.00      | X0 = sK1
% 3.50/1.00      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_387,c_8]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_945,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15
% 3.50/1.00      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.50/1.00      | sK0 = sK1 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_943]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1092,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15 | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_943,c_8,c_945]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_22,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_21,plain,( X0 = X0 ),theory(equality) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_599,plain,
% 3.50/1.00      ( X0 != X1 | X1 = X0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1222,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15 | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_1092,c_599]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1239,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15
% 3.50/1.00      | X0 != arAF0_k5_xboole_0_0
% 3.50/1.00      | arAF0_k6_enumset1_0 = X0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_1222,c_22]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_617,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_12 | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_599,c_384]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1641,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_15
% 3.50/1.00      | ~ iProver_ARSWP_12
% 3.50/1.00      | arAF0_k6_enumset1_0 = k1_xboole_0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_1239,c_617]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1642,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1708,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1484,c_1642]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_723,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 != X0
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X0
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_481]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1725,plain,
% 3.50/1.00      ( arAF0_k5_xboole_0_0 = X0
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.50/1.00      | k1_xboole_0 != X0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1708,c_723]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_725,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 != X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_481]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1724,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.50/1.00      | k1_xboole_0 != X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1708,c_725]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1495,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = X0
% 3.50/1.00      | k1_xboole_0 != X0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_12 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_1349]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_708,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | sK0 != X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_481,c_8]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_28,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_21]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_174,plain,
% 3.50/1.00      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_175,plain,
% 3.50/1.00      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_174]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_713,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | sK1 = X0
% 3.50/1.00      | sK0 != X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_481,c_8]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_882,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | sK1 = sK0
% 3.50/1.00      | sK0 != sK0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_713]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_899,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_708,c_8,c_28,c_175,c_882]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_724,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = X1
% 3.50/1.00      | arAF0_k5_xboole_0_0 != X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_481]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_0,plain,
% 3.50/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.50/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_382,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_10 | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.50/1.00      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_486,plain,
% 3.50/1.00      ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.50/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_706,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | arAF0_k5_xboole_0_0 = X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_481,c_486]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_717,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | arAF0_k5_xboole_0_0 != X1
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top ),
% 3.50/1.00      inference(equality_factoring,[status(thm)],[c_481]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_847,plain,
% 3.50/1.00      ( X0 = X1
% 3.50/1.00      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | iProver_ARSWP_15 != iProver_top
% 3.50/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_706,c_717]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_615,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_10 | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.50/1.00      inference(resolution,[status(thm)],[c_599,c_382]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_616,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1307,plain,
% 3.50/1.00      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.50/1.00      | iProver_ARSWP_10 != iProver_top ),
% 3.50/1.00      inference(global_propositional_subsumption,[status(thm)],[c_847,c_616]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1,plain,
% 3.50/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_383,plain,
% 3.50/1.00      ( ~ iProver_ARSWP_11 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.50/1.00      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_485,plain,
% 3.50/1.00      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_11 != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS output end Saturation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  ------                               Statistics
% 3.50/1.00  
% 3.50/1.00  ------ Selected
% 3.50/1.00  
% 3.50/1.00  total_time:                             0.105
% 3.50/1.00  
%------------------------------------------------------------------------------
