%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:58 EST 2020

% Result     : CounterSatisfiable 3.72s
% Output     : Saturation 3.72s
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

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f32,f58,f61,f59])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X1,X2) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k2_tarski(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k2_tarski(X1,X2) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k2_tarski(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK0 != sK1
    & k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f42,f54,f50,f61])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_388,plain,
    ( ~ iProver_ARSWP_12
    | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_488,plain,
    ( arAF0_k5_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_7,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_391,plain,
    ( ~ iProver_ARSWP_15
    | X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_485,plain,
    ( X0 = X1
    | X2 = X1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_726,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X0
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_485])).

cnf(c_1031,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_488,c_726])).

cnf(c_1353,plain,
    ( arAF0_k5_enumset1_0 = X0
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1031])).

cnf(c_1488,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1353])).

cnf(c_11,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_947,plain,
    ( ~ iProver_ARSWP_15
    | X0 = sK1
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(resolution,[status(thm)],[c_391,c_11])).

cnf(c_949,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1096,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_11,c_949])).

cnf(c_26,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_25,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_603,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_26,c_25])).

cnf(c_1226,plain,
    ( ~ iProver_ARSWP_15
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_1096,c_603])).

cnf(c_1243,plain,
    ( ~ iProver_ARSWP_15
    | X0 != arAF0_k5_xboole_0_0
    | arAF0_k5_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_1226,c_26])).

cnf(c_621,plain,
    ( ~ iProver_ARSWP_12
    | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_603,c_388])).

cnf(c_1645,plain,
    ( ~ iProver_ARSWP_15
    | ~ iProver_ARSWP_12
    | arAF0_k5_enumset1_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1243,c_621])).

cnf(c_1646,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_1712,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_1646])).

cnf(c_727,plain,
    ( arAF0_k5_enumset1_0 != X0
    | arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_485])).

cnf(c_1729,plain,
    ( arAF0_k5_xboole_0_0 = X0
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_727])).

cnf(c_729,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 != X1
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_485])).

cnf(c_1728,plain,
    ( X0 = X1
    | arAF0_k5_xboole_0_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_729])).

cnf(c_1499,plain,
    ( arAF0_k5_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_12 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1353])).

cnf(c_712,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_11])).

cnf(c_32,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_178,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_179,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_717,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = X0
    | sK0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_11])).

cnf(c_886,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | sK1 = sK0
    | sK0 != sK0
    | iProver_ARSWP_15 != iProver_top ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_903,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_11,c_32,c_179,c_886])).

cnf(c_728,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = X1
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_485])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_386,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_490,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_710,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 = X1
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_490])).

cnf(c_721,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | arAF0_k5_xboole_0_0 != X1
    | iProver_ARSWP_15 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_485])).

cnf(c_851,plain,
    ( X0 = X1
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_15 != iProver_top
    | iProver_ARSWP_10 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_710,c_721])).

cnf(c_619,plain,
    ( ~ iProver_ARSWP_10
    | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_603,c_386])).

cnf(c_620,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1311,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_10 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_851,c_620])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_387,plain,
    ( ~ iProver_ARSWP_11
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_489,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_11 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.72/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.99  
% 3.72/0.99  ------  iProver source info
% 3.72/0.99  
% 3.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.99  git: non_committed_changes: false
% 3.72/0.99  git: last_make_outside_of_git: false
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  ------ Parsing...
% 3.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  ------ Proving...
% 3.72/0.99  ------ Problem Properties 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  clauses                                 13
% 3.72/0.99  conjectures                             2
% 3.72/0.99  EPR                                     1
% 3.72/0.99  Horn                                    12
% 3.72/0.99  unary                                   12
% 3.72/0.99  binary                                  0
% 3.72/0.99  lits                                    15
% 3.72/0.99  lits eq                                 15
% 3.72/0.99  fd_pure                                 0
% 3.72/0.99  fd_pseudo                               0
% 3.72/0.99  fd_cond                                 0
% 3.72/0.99  fd_pseudo_cond                          1
% 3.72/0.99  AC symbols                              0
% 3.72/0.99  
% 3.72/0.99  ------ Input Options Time Limit: Unbounded
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.72/0.99  Current options:
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  % SZS output start Saturation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  fof(f4,axiom,(
% 3.72/0.99    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f4])).
% 3.72/0.99  
% 3.72/0.99  fof(f12,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f27,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.72/0.99    inference(ennf_transformation,[],[f12])).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  fof(f3,axiom,(
% 3.72/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f3])).
% 3.72/0.99  
% 3.72/0.99  fof(f16,axiom,(
% 3.72/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f45,plain,(
% 3.72/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f16])).
% 3.72/0.99  
% 3.72/0.99  fof(f61,plain,(
% 3.72/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f45,f59])).
% 3.72/0.99  
% 3.72/0.99  fof(f17,axiom,(
% 3.72/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f17])).
% 3.72/0.99  
% 3.72/0.99  fof(f18,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f19,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f48,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f19])).
% 3.72/0.99  
% 3.72/0.99  fof(f20,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f49,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f20])).
% 3.72/0.99  
% 3.72/0.99  fof(f21,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f21])).
% 3.72/0.99  
% 3.72/0.99  fof(f55,plain,(
% 3.72/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f56,plain,(
% 3.72/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f48,f55])).
% 3.72/0.99  
% 3.72/0.99  fof(f58,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f47,f56])).
% 3.72/0.99  
% 3.72/0.99  fof(f59,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f46,f58])).
% 3.72/0.99  
% 3.72/0.99  fof(f67,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.72/0.99    inference(definition_unfolding,[],[f41,f32,f58,f61,f59])).
% 3.72/0.99  
% 3.72/0.99  fof(f23,conjecture,(
% 3.72/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f24,negated_conjecture,(
% 3.72/0.99    ~! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 3.72/0.99    inference(negated_conjecture,[],[f23])).
% 3.72/0.99  
% 3.72/0.99  fof(f28,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0))),
% 3.72/0.99    inference(ennf_transformation,[],[f24])).
% 3.72/0.99  
% 3.72/0.99  fof(f29,plain,(
% 3.72/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0)) => (sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f30,plain,(
% 3.72/0.99    sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0)),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    sK0 != sK1),
% 3.72/0.99    inference(cnf_transformation,[],[f30])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f5,axiom,(
% 3.72/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f34,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f5])).
% 3.72/0.99  
% 3.72/0.99  fof(f54,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f34,f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f42,f54,f50,f61])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f25,plain,(
% 3.72/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.72/0.99    inference(rectify,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f31,plain,(
% 3.72/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f25])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2,plain,
% 3.72/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_388,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_12 | arAF0_k5_xboole_0_0 = k1_xboole_0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_488,plain,
% 3.72/0.99      ( arAF0_k5_xboole_0_0 = k1_xboole_0 | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_391,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15
% 3.72/0.99      | X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_485,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | X2 = X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_726,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.72/0.99      | arAF0_k5_enumset1_0 = X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 != X0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_485]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1031,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.72/0.99      | arAF0_k5_enumset1_0 = X1
% 3.72/0.99      | k1_xboole_0 != X0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_488,c_726]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1353,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.72/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(equality_resolution,[status(thm)],[c_1031]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1488,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1353,c_1353]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11,negated_conjecture,
% 3.72/0.99      ( sK0 != sK1 ),
% 3.72/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_947,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15
% 3.72/0.99      | X0 = sK1
% 3.72/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_391,c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_949,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15
% 3.72/0.99      | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.72/0.99      | sK0 = sK1 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_947]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1096,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_947,c_11,c_949]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_26,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_25,plain,( X0 = X0 ),theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_603,plain,
% 3.72/0.99      ( X0 != X1 | X1 = X0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_26,c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1226,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_1096,c_603]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1243,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15
% 3.72/0.99      | X0 != arAF0_k5_xboole_0_0
% 3.72/0.99      | arAF0_k5_enumset1_0 = X0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_1226,c_26]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_621,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_12 | k1_xboole_0 = arAF0_k5_xboole_0_0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_603,c_388]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1645,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_15
% 3.72/0.99      | ~ iProver_ARSWP_12
% 3.72/0.99      | arAF0_k5_enumset1_0 = k1_xboole_0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_1243,c_621]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1646,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1712,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1488,c_1646]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_727,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 != X0
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X0
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_485]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1729,plain,
% 3.72/0.99      ( arAF0_k5_xboole_0_0 = X0
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.72/0.99      | k1_xboole_0 != X0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1712,c_727]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_729,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 != X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_485]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1728,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.72/0.99      | k1_xboole_0 != X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1712,c_729]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1499,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = X0
% 3.72/0.99      | k1_xboole_0 != X0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_12 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_1353]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_712,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | sK0 != X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_485,c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_32,plain,( sK0 = sK0 ),inference(instantiation,[status(thm)],[c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_178,plain,
% 3.72/0.99      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_179,plain,
% 3.72/0.99      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_178]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_717,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | sK1 = X0
% 3.72/0.99      | sK0 != X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_485,c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_886,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | sK1 = sK0
% 3.72/0.99      | sK0 != sK0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_717]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_903,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_712,c_11,c_32,c_179,c_886]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_728,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = X1
% 3.72/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_485]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_0,plain,
% 3.72/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_386,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_10 | arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_490,plain,
% 3.72/0.99      ( arAF0_k5_xboole_0_0 = arAF0_k5_enumset1_0
% 3.72/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_710,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | arAF0_k5_xboole_0_0 = X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_485,c_490]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_721,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | arAF0_k5_xboole_0_0 != X1
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top ),
% 3.72/0.99      inference(equality_factoring,[status(thm)],[c_485]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_851,plain,
% 3.72/0.99      ( X0 = X1
% 3.72/0.99      | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | iProver_ARSWP_15 != iProver_top
% 3.72/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.72/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_710,c_721]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_619,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_10 | arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0 ),
% 3.72/0.99      inference(resolution,[status(thm)],[c_603,c_386]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_620,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1311,plain,
% 3.72/0.99      ( arAF0_k5_enumset1_0 = arAF0_k5_xboole_0_0
% 3.72/0.99      | iProver_ARSWP_10 != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,[status(thm)],[c_851,c_620]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_387,plain,
% 3.72/0.99      ( ~ iProver_ARSWP_11 | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.72/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_489,plain,
% 3.72/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0 | iProver_ARSWP_11 != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end Saturation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ Selected
% 3.72/0.99  
% 3.72/0.99  total_time:                             0.099
% 3.72/0.99  
%------------------------------------------------------------------------------
