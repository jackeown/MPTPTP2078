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
% DateTime   : Thu Dec  3 11:28:58 EST 2020

% Result     : CounterSatisfiable 3.71s
% Output     : Saturation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   88 (1048 expanded)
%              Number of clauses        :   48 ( 155 expanded)
%              Number of leaves         :   16 ( 332 expanded)
%              Depth                    :   18
%              Number of atoms          :  195 (1530 expanded)
%              Number of equality atoms :  182 (1485 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f33,f60,f62,f61])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f55,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f44,f56,f52,f62])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_390,plain,
    ( ~ iProver_ARSWP_12
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_490,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_8,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_393,plain,
    ( ~ iProver_ARSWP_15
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_487,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_728,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_487])).

cnf(c_1033,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_490,c_728])).

cnf(c_1355,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1033])).

cnf(c_1490,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1355])).

cnf(c_12,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_949,plain,
    ( ~ iProver_ARSWP_15
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(resolution,[status(thm)],[c_393,c_12])).

cnf(c_951,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_1098,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_12,c_951])).

cnf(c_28,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_27,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_605,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_28,c_27])).

cnf(c_1228,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_1098,c_605])).

cnf(c_1245,plain,
    ( ~ iProver_ARSWP_15
    | X0 != arAF0_k5_xboole_0_0
    | arAF0_k5_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_1228,c_28])).

cnf(c_623,plain,
    ( ~ iProver_ARSWP_12
    | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_605,c_390])).

cnf(c_1647,plain,
    ( ~ iProver_ARSWP_15
    | ~ iProver_ARSWP_12
    | arAF0_k5_enumset1_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1245,c_623])).

cnf(c_1648,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_1714,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_1648])).

cnf(c_729,plain,
    ( arAF0_k5_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_487])).

cnf(c_1731,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_729])).

cnf(c_731,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_487])).

cnf(c_1730,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_731])).

cnf(c_1501,plain,
    ( arAF0_k5_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1355])).

cnf(c_714,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_12])).

cnf(c_34,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_180,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_181,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_719,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_12])).

cnf(c_888,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_15 != iProver_top ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_905,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_12,c_34,c_181,c_888])).

cnf(c_730,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_487])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_388,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_492,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_712,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_492])).

cnf(c_723,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_487])).

cnf(c_853,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_712,c_723])).

cnf(c_621,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_605,c_388])).

cnf(c_622,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1313,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_622])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_389,plain,
    ( ~ iProver_ARSWP_11
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_491,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.99  
% 3.71/0.99  ------  iProver source info
% 3.71/0.99  
% 3.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.99  git: non_committed_changes: false
% 3.71/0.99  git: last_make_outside_of_git: false
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  ------ Parsing...
% 3.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  ------ Proving...
% 3.71/0.99  ------ Problem Properties 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  clauses                                 14
% 3.71/0.99  conjectures                             2
% 3.71/0.99  EPR                                     1
% 3.71/0.99  Horn                                    13
% 3.71/0.99  unary                                   13
% 3.71/0.99  binary                                  0
% 3.71/0.99  lits                                    16
% 3.71/0.99  lits eq                                 16
% 3.71/0.99  fd_pure                                 0
% 3.71/0.99  fd_pseudo                               0
% 3.71/0.99  fd_cond                                 0
% 3.71/0.99  fd_pseudo_cond                          1
% 3.71/0.99  AC symbols                              0
% 3.71/0.99  
% 3.71/0.99  ------ Input Options Time Limit: Unbounded
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.71/0.99  Current options:
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  % SZS output start Saturation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  fof(f4,axiom,(
% 3.71/0.99    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f34,plain,(
% 3.71/0.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f4])).
% 3.71/0.99  
% 3.71/0.99  fof(f13,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f28,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.71/0.99    inference(ennf_transformation,[],[f13])).
% 3.71/0.99  
% 3.71/0.99  fof(f43,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.71/0.99    inference(cnf_transformation,[],[f28])).
% 3.71/0.99  
% 3.71/0.99  fof(f3,axiom,(
% 3.71/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f33,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f3])).
% 3.71/0.99  
% 3.71/0.99  fof(f17,axiom,(
% 3.71/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f47,plain,(
% 3.71/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f17])).
% 3.71/0.99  
% 3.71/0.99  fof(f62,plain,(
% 3.71/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f47,f61])).
% 3.71/0.99  
% 3.71/0.99  fof(f18,axiom,(
% 3.71/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f48,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f18])).
% 3.71/0.99  
% 3.71/0.99  fof(f19,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f49,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f19])).
% 3.71/0.99  
% 3.71/0.99  fof(f20,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f50,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f20])).
% 3.71/0.99  
% 3.71/0.99  fof(f21,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f51,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f21])).
% 3.71/0.99  
% 3.71/0.99  fof(f22,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f52,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f22])).
% 3.71/0.99  
% 3.71/0.99  fof(f57,plain,(
% 3.71/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f51,f52])).
% 3.71/0.99  
% 3.71/0.99  fof(f58,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f50,f57])).
% 3.71/0.99  
% 3.71/0.99  fof(f60,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f49,f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f61,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f48,f60])).
% 3.71/0.99  
% 3.71/0.99  fof(f70,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.71/0.99    inference(definition_unfolding,[],[f43,f33,f60,f62,f61])).
% 3.71/0.99  
% 3.71/0.99  fof(f24,conjecture,(
% 3.71/0.99    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f25,negated_conjecture,(
% 3.71/0.99    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.71/0.99    inference(negated_conjecture,[],[f24])).
% 3.71/0.99  
% 3.71/0.99  fof(f29,plain,(
% 3.71/0.99    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.71/0.99    inference(ennf_transformation,[],[f25])).
% 3.71/0.99  
% 3.71/0.99  fof(f30,plain,(
% 3.71/0.99    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f31,plain,(
% 3.71/0.99    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 3.71/0.99  
% 3.71/0.99  fof(f55,plain,(
% 3.71/0.99    sK0 != sK1),
% 3.71/0.99    inference(cnf_transformation,[],[f31])).
% 3.71/0.99  
% 3.71/0.99  fof(f14,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f44,plain,(
% 3.71/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f14])).
% 3.71/0.99  
% 3.71/0.99  fof(f5,axiom,(
% 3.71/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f35,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f5])).
% 3.71/0.99  
% 3.71/0.99  fof(f56,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f35,f33])).
% 3.71/0.99  
% 3.71/0.99  fof(f64,plain,(
% 3.71/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f44,f56,f52,f62])).
% 3.71/0.99  
% 3.71/0.99  fof(f2,axiom,(
% 3.71/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f26,plain,(
% 3.71/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.71/0.99    inference(rectify,[],[f2])).
% 3.71/0.99  
% 3.71/0.99  fof(f32,plain,(
% 3.71/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.71/0.99    inference(cnf_transformation,[],[f26])).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2,plain,
% 3.71/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.71/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_390,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_12 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.71/0.99      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_490,plain,
% 3.71/0.99      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | X2 = X1
% 3.71/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_393,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15
% 3.71/0.99      | X0 = X1
% 3.71/0.99      | X2 = X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.71/0.99      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_487,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | X2 = X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_728,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.71/0.99      | arAF0_k5_enumset1_0 = X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 != X0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_487]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1033,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.71/0.99      | arAF0_k5_enumset1_0 = X1
% 3.71/0.99      | k1_xboole_0 != X0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_490,c_728]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1355,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.71/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(equality_resolution,[status(thm)],[c_1033]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1490,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1355,c_1355]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_12,negated_conjecture,
% 3.71/0.99      ( sK0 != sK1 ),
% 3.71/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_949,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15
% 3.71/0.99      | X0 = sK1
% 3.71/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_393,c_12]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_951,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15
% 3.71/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.71/0.99      | sK0 = sK1 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1098,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_949,c_12,c_951]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_28,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_27,plain,( X0 = X0 ),theory(equality) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_605,plain,
% 3.71/0.99      ( X0 != X1 | X1 = X0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_28,c_27]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1228,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_1098,c_605]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1245,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15
% 3.71/0.99      | X0 != arAF0_k5_xboole_0_0
% 3.71/0.99      | arAF0_k5_enumset1_0 = X0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_1228,c_28]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_623,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_12 | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_605,c_390]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1647,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_15
% 3.71/0.99      | ~ iProver_ARSWP_12
% 3.71/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_1245,c_623]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1648,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1714,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1490,c_1648]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_729,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 != X0
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X0
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_487]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1731,plain,
% 3.71/0.99      ( arAF0_k5_xboole_0_0 = X0
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.71/0.99      | k1_xboole_0 != X0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1714,c_729]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_731,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 != X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_487]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1730,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.71/0.99      | k1_xboole_0 != X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1714,c_731]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1501,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.71/0.99      | k1_xboole_0 != X0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_1355]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_714,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | sK0 != X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_487,c_12]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_34,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_27]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_180,plain,
% 3.71/0.99      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_181,plain,
% 3.71/0.99      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_180]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_719,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | sK1 = X0
% 3.71/0.99      | sK0 != X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_487,c_12]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_888,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | sK1 = sK0
% 3.71/0.99      | sK0 != sK0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_719]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_905,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_714,c_12,c_34,c_181,c_888]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_730,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = X1
% 3.71/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_487]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_0,plain,
% 3.71/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.71/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_388,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_10 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.71/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_492,plain,
% 3.71/0.99      ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.71/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_712,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_487,c_492]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_723,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.71/0.99      inference(equality_factoring,[status(thm)],[c_487]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_853,plain,
% 3.71/0.99      ( X0 = X1
% 3.71/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | iProver_ARSWP_15 != iProver_top
% 3.71/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.71/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_712,c_723]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_621,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_10 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_605,c_388]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_622,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1313,plain,
% 3.71/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.71/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_853,c_622]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1,plain,
% 3.71/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.71/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_389,plain,
% 3.71/0.99      ( ~ iProver_ARSWP_11 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.71/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_491,plain,
% 3.71/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_11 != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS output end Saturation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  ------                               Statistics
% 3.71/0.99  
% 3.71/0.99  ------ Selected
% 3.71/0.99  
% 3.71/0.99  total_time:                             0.12
% 3.71/0.99  
%------------------------------------------------------------------------------
