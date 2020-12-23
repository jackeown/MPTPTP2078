%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:59 EST 2020

% Result     : CounterSatisfiable 3.40s
% Output     : Saturation 3.40s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f51,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f34,f28,f50,f52,f51])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f35,f46,f47,f51])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_373,plain,
    ( ~ iProver_ARSWP_11
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_464,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_5,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_375,plain,
    ( ~ iProver_ARSWP_13
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_462,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_13 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_702,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_13 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_462])).

cnf(c_988,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(superposition,[status(thm)],[c_464,c_702])).

cnf(c_1336,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_988])).

cnf(c_1477,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_1336])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1053,plain,
    ( ~ iProver_ARSWP_13
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_375,c_7])).

cnf(c_1055,plain,
    ( ~ iProver_ARSWP_13
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1090,plain,
    ( ~ iProver_ARSWP_13
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_7,c_1055])).

cnf(c_20,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_19,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_579,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_20,c_19])).

cnf(c_1220,plain,
    ( ~ iProver_ARSWP_13
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_1090,c_579])).

cnf(c_1362,plain,
    ( ~ iProver_ARSWP_13
    | X0 != arAF0_k5_xboole_0_0
    | arAF0_k6_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_1220,c_20])).

cnf(c_597,plain,
    ( ~ iProver_ARSWP_11
    | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_579,c_373])).

cnf(c_1634,plain,
    ( ~ iProver_ARSWP_13
    | ~ iProver_ARSWP_11
    | arAF0_k6_enumset1_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1362,c_597])).

cnf(c_1635,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_1701,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1477,c_1635])).

cnf(c_703,plain,
    ( arAF0_k6_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_462])).

cnf(c_1718,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_703])).

cnf(c_705,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_462])).

cnf(c_1717,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_705])).

cnf(c_1488,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_11 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1336])).

cnf(c_688,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(superposition,[status(thm)],[c_462,c_7])).

cnf(c_26,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_163,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_164,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_693,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(superposition,[status(thm)],[c_462,c_7])).

cnf(c_862,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_13 != iProver_top ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_879,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_13 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_7,c_26,c_164,c_862])).

cnf(c_704,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_462])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_371,plain,
    ( ~ iProver_ARSWP_9
    | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_466,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_9 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_686,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_9 != iProver_top ),
    inference(superposition,[status(thm)],[c_462,c_466])).

cnf(c_697,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_13 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_462])).

cnf(c_827,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_13 != iProver_top
    | iProver_ARSWP_9 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_686,c_697])).

cnf(c_595,plain,
    ( ~ iProver_ARSWP_9
    | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_579,c_371])).

cnf(c_596,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_9 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1294,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_9 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_596])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_372,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_465,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.40/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.98  
% 3.40/0.98  ------  iProver source info
% 3.40/0.98  
% 3.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.98  git: non_committed_changes: false
% 3.40/0.98  git: last_make_outside_of_git: false
% 3.40/0.98  
% 3.40/0.98  ------ 
% 3.40/0.98  ------ Parsing...
% 3.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  ------ Proving...
% 3.40/0.98  ------ Problem Properties 
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  clauses                                 9
% 3.40/0.98  conjectures                             2
% 3.40/0.98  EPR                                     1
% 3.40/0.98  Horn                                    8
% 3.40/0.98  unary                                   8
% 3.40/0.98  binary                                  0
% 3.40/0.98  lits                                    11
% 3.40/0.98  lits eq                                 11
% 3.40/0.98  fd_pure                                 0
% 3.40/0.98  fd_pseudo                               0
% 3.40/0.98  fd_cond                                 0
% 3.40/0.98  fd_pseudo_cond                          1
% 3.40/0.98  AC symbols                              0
% 3.40/0.98  
% 3.40/0.98  ------ Input Options Time Limit: Unbounded
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.40/0.98  Current options:
% 3.40/0.98  ------ 
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  % SZS output start Saturation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  fof(f4,axiom,(
% 3.40/0.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f29,plain,(
% 3.40/0.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f4])).
% 3.40/0.98  
% 3.40/0.98  fof(f9,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f23,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.40/0.98    inference(ennf_transformation,[],[f9])).
% 3.40/0.98  
% 3.40/0.98  fof(f34,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.40/0.98    inference(cnf_transformation,[],[f23])).
% 3.40/0.98  
% 3.40/0.98  fof(f3,axiom,(
% 3.40/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f28,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.40/0.98    inference(cnf_transformation,[],[f3])).
% 3.40/0.98  
% 3.40/0.98  fof(f12,axiom,(
% 3.40/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f37,plain,(
% 3.40/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f12])).
% 3.40/0.98  
% 3.40/0.98  fof(f52,plain,(
% 3.40/0.98    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f37,f51])).
% 3.40/0.98  
% 3.40/0.98  fof(f13,axiom,(
% 3.40/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f38,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f13])).
% 3.40/0.98  
% 3.40/0.98  fof(f14,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f39,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f14])).
% 3.40/0.98  
% 3.40/0.98  fof(f15,axiom,(
% 3.40/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f40,plain,(
% 3.40/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f15])).
% 3.40/0.98  
% 3.40/0.98  fof(f16,axiom,(
% 3.40/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f41,plain,(
% 3.40/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f16])).
% 3.40/0.98  
% 3.40/0.98  fof(f17,axiom,(
% 3.40/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f42,plain,(
% 3.40/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f17])).
% 3.40/0.98  
% 3.40/0.98  fof(f18,axiom,(
% 3.40/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f43,plain,(
% 3.40/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f18])).
% 3.40/0.98  
% 3.40/0.98  fof(f47,plain,(
% 3.40/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f42,f43])).
% 3.40/0.98  
% 3.40/0.98  fof(f48,plain,(
% 3.40/0.98    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f41,f47])).
% 3.40/0.98  
% 3.40/0.98  fof(f49,plain,(
% 3.40/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f40,f48])).
% 3.40/0.98  
% 3.40/0.98  fof(f50,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f39,f49])).
% 3.40/0.98  
% 3.40/0.98  fof(f51,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f38,f50])).
% 3.40/0.98  
% 3.40/0.98  fof(f57,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.40/0.98    inference(definition_unfolding,[],[f34,f28,f50,f52,f51])).
% 3.40/0.98  
% 3.40/0.98  fof(f19,conjecture,(
% 3.40/0.98    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f20,negated_conjecture,(
% 3.40/0.98    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.40/0.98    inference(negated_conjecture,[],[f19])).
% 3.40/0.98  
% 3.40/0.98  fof(f24,plain,(
% 3.40/0.98    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.40/0.98    inference(ennf_transformation,[],[f20])).
% 3.40/0.98  
% 3.40/0.98  fof(f25,plain,(
% 3.40/0.98    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 3.40/0.98    introduced(choice_axiom,[])).
% 3.40/0.98  
% 3.40/0.98  fof(f26,plain,(
% 3.40/0.98    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 3.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f45,plain,(
% 3.40/0.98    sK0 != sK1),
% 3.40/0.98    inference(cnf_transformation,[],[f26])).
% 3.40/0.98  
% 3.40/0.98  fof(f10,axiom,(
% 3.40/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f35,plain,(
% 3.40/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f10])).
% 3.40/0.98  
% 3.40/0.98  fof(f5,axiom,(
% 3.40/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f30,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f5])).
% 3.40/0.98  
% 3.40/0.98  fof(f46,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f30,f28])).
% 3.40/0.98  
% 3.40/0.98  fof(f54,plain,(
% 3.40/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f35,f46,f47,f51])).
% 3.40/0.98  
% 3.40/0.98  fof(f2,axiom,(
% 3.40/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f21,plain,(
% 3.40/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.40/0.98    inference(rectify,[],[f2])).
% 3.40/0.98  
% 3.40/0.98  fof(f27,plain,(
% 3.40/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.40/0.98    inference(cnf_transformation,[],[f21])).
% 3.40/0.98  
% 3.40/0.98  cnf(c_2,plain,
% 3.40/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.40/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_373,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_11 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.40/0.98      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_464,plain,
% 3.40/0.98      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | X2 = X1
% 3.40/0.98      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_375,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13
% 3.40/0.98      | X0 = X1
% 3.40/0.98      | X2 = X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.40/0.98      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_462,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | X2 = X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_702,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.40/0.98      | arAF0_k6_enumset1_0 = X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 != X0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_462]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_988,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.40/0.98      | arAF0_k6_enumset1_0 = X1
% 3.40/0.98      | k1_xboole_0 != X0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_464,c_702]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1336,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.40/0.98      | arAF0_k6_enumset1_0 = k1_xboole_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(equality_resolution,[status(thm)],[c_988]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1477,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = k1_xboole_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_1336,c_1336]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_7,negated_conjecture,
% 3.40/0.98      ( sK0 != sK1 ),
% 3.40/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1053,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13
% 3.40/0.98      | X0 = sK1
% 3.40/0.98      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_375,c_7]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1055,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13
% 3.40/0.98      | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.40/0.98      | sK0 = sK1 ),
% 3.40/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1090,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13 | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.40/0.98      inference(global_propositional_subsumption,
% 3.40/0.98                [status(thm)],
% 3.40/0.98                [c_1053,c_7,c_1055]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_20,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_19,plain,( X0 = X0 ),theory(equality) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_579,plain,
% 3.40/0.98      ( X0 != X1 | X1 = X0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_20,c_19]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1220,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13 | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_1090,c_579]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1362,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13
% 3.40/0.98      | X0 != arAF0_k5_xboole_0_0
% 3.40/0.98      | arAF0_k6_enumset1_0 = X0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_1220,c_20]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_597,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_11 | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_579,c_373]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1634,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_13
% 3.40/0.98      | ~ iProver_ARSWP_11
% 3.40/0.98      | arAF0_k6_enumset1_0 = k1_xboole_0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_1362,c_597]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1635,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1701,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1477,c_1635]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_703,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 != X0
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X0
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_462]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1718,plain,
% 3.40/0.98      ( arAF0_k5_xboole_0_0 = X0
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X1
% 3.40/0.98      | k1_xboole_0 != X0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_1701,c_703]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_705,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 != X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_462]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1717,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X1
% 3.40/0.98      | k1_xboole_0 != X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_1701,c_705]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1488,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.40/0.98      | k1_xboole_0 != X0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_11 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_1336]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_688,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | sK0 != X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_462,c_7]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_26,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_19]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_163,plain,
% 3.40/0.98      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.40/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_164,plain,
% 3.40/0.98      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.40/0.98      inference(instantiation,[status(thm)],[c_163]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_693,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | sK1 = X0
% 3.40/0.98      | sK0 != X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_462,c_7]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_862,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | sK1 = sK0
% 3.40/0.98      | sK0 != sK0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(instantiation,[status(thm)],[c_693]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_879,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(global_propositional_subsumption,
% 3.40/0.98                [status(thm)],
% 3.40/0.98                [c_688,c_7,c_26,c_164,c_862]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_704,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = X1
% 3.40/0.98      | arAF0_k5_xboole_0_0 != X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_462]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_0,plain,
% 3.40/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.40/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_371,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_9 | arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.40/0.98      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_466,plain,
% 3.40/0.98      ( arAF0_k5_xboole_0_0 = arAF0_k6_enumset1_0
% 3.40/0.98      | iProver_ARSWP_9 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_686,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | arAF0_k5_xboole_0_0 = X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_9 != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_462,c_466]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_697,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | arAF0_k5_xboole_0_0 != X1
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top ),
% 3.40/0.98      inference(equality_factoring,[status(thm)],[c_462]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_827,plain,
% 3.40/0.98      ( X0 = X1
% 3.40/0.98      | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | iProver_ARSWP_13 != iProver_top
% 3.40/0.98      | iProver_ARSWP_9 != iProver_top ),
% 3.40/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_686,c_697]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_595,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_9 | arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.40/0.98      inference(resolution,[status(thm)],[c_579,c_371]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_596,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | iProver_ARSWP_9 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1294,plain,
% 3.40/0.98      ( arAF0_k6_enumset1_0 = arAF0_k5_xboole_0_0
% 3.40/0.98      | iProver_ARSWP_9 != iProver_top ),
% 3.40/0.98      inference(global_propositional_subsumption,[status(thm)],[c_827,c_596]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1,plain,
% 3.40/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 3.40/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_372,plain,
% 3.40/0.98      ( ~ iProver_ARSWP_10 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.40/0.98      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_465,plain,
% 3.40/0.98      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_10 != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS output end Saturation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  ------                               Statistics
% 3.40/0.98  
% 3.40/0.98  ------ Selected
% 3.40/0.98  
% 3.40/0.98  total_time:                             0.108
% 3.40/0.98  
%------------------------------------------------------------------------------
