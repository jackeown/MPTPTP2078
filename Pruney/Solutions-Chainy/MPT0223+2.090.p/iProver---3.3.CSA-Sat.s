%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:00 EST 2020

% Result     : CounterSatisfiable 3.64s
% Output     : Saturation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  127 (3414 expanded)
%              Number of clauses        :   81 ( 757 expanded)
%              Number of leaves         :   18 ( 998 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 (5616 expanded)
%              Number of equality atoms :  332 (5426 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK0 != sK1
    & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f45,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f58,plain,(
    k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) = k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f48,f48,f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f35,f29,f48,f39])).

fof(f46,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f37,f47,f44,f48])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f36,f47,f48,f44])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_8,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) = k1_enumset1(sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1150,negated_conjecture,
    ( ~ iProver_ARSWP_27
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_1232,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1145,plain,
    ( ~ iProver_ARSWP_22
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1237,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_22 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_5,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1148,plain,
    ( ~ iProver_ARSWP_25
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_1234,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1301,plain,
    ( ~ iProver_ARSWP_25
    | X0 = sK1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1302,plain,
    ( X0 = sK1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK0 = sK1
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_1304,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK0 = sK1
    | iProver_ARSWP_25 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_1637,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_25 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_7,c_1304])).

cnf(c_6,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1149,plain,
    ( ~ iProver_ARSWP_26
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_1233,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_1645,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1233])).

cnf(c_5516,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1645])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5541,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5516,c_3])).

cnf(c_5585,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_5541,c_1233])).

cnf(c_7196,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_5585])).

cnf(c_7484,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_7196])).

cnf(c_1643,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1637])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1146,plain,
    ( ~ iProver_ARSWP_23
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1236,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_23 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_2900,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1236])).

cnf(c_2905,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2900,c_3])).

cnf(c_3108,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_1236])).

cnf(c_4396,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_3108])).

cnf(c_7176,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_4396])).

cnf(c_3099,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_1643])).

cnf(c_1529,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1236])).

cnf(c_4359,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_1529])).

cnf(c_4588,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_4359])).

cnf(c_6605,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_4588])).

cnf(c_5558,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_5541,c_1645])).

cnf(c_5890,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_5558])).

cnf(c_1406,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1233])).

cnf(c_5576,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_5541,c_1406])).

cnf(c_5575,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_5541,c_1643])).

cnf(c_1530,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1236])).

cnf(c_5521,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1645,c_1530])).

cnf(c_4361,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1529])).

cnf(c_4358,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1529])).

cnf(c_1644,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1637])).

cnf(c_1655,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1644,c_3])).

cnf(c_1673,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1637])).

cnf(c_1845,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1673])).

cnf(c_1678,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1237])).

cnf(c_1677,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1233])).

cnf(c_2725,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1677])).

cnf(c_3391,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_2725])).

cnf(c_3621,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_3391])).

cnf(c_3823,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_3621])).

cnf(c_3624,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_3391])).

cnf(c_3396,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_2725])).

cnf(c_3109,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_1233])).

cnf(c_2897,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1643])).

cnf(c_2761,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1406])).

cnf(c_1676,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1236])).

cnf(c_2322,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1676])).

cnf(c_2348,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_2322])).

cnf(c_2535,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_2348])).

cnf(c_1957,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1530])).

cnf(c_2570,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_1957])).

cnf(c_2537,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_2348])).

cnf(c_2184,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1957])).

cnf(c_2004,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1845])).

cnf(c_1674,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1530])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1707,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1674,c_2])).

cnf(c_2157,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_1707])).

cnf(c_22,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_21,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1427,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_1569,plain,
    ( ~ iProver_ARSWP_22
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1427,c_1145])).

cnf(c_1570,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_22 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_2873,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_22 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2157,c_1570])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 9
% 3.64/0.99  conjectures                             2
% 3.64/0.99  EPR                                     1
% 3.64/0.99  Horn                                    8
% 3.64/0.99  unary                                   8
% 3.64/0.99  binary                                  0
% 3.64/0.99  lits                                    11
% 3.64/0.99  lits eq                                 11
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          1
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Input Options Time Limit: Unbounded
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  % SZS output start Saturation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f20,conjecture,(
% 3.64/0.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f21,negated_conjecture,(
% 3.64/0.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.64/0.99    inference(negated_conjecture,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f21])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK0 != sK1 & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f28,plain,(
% 3.64/0.99    sK0 != sK1 & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 3.64/0.99  
% 3.64/0.99  fof(f45,plain,(
% 3.64/0.99    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 3.64/0.99    inference(cnf_transformation,[],[f28])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,axiom,(
% 3.64/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f38,plain,(
% 3.64/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f13,axiom,(
% 3.64/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f39,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f13])).
% 3.64/0.99  
% 3.64/0.99  fof(f48,plain,(
% 3.64/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f38,f39])).
% 3.64/0.99  
% 3.64/0.99  fof(f58,plain,(
% 3.64/0.99    k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) = k1_enumset1(sK0,sK0,sK0)),
% 3.64/0.99    inference(definition_unfolding,[],[f45,f48,f48,f48])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f40,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f15,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f41,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f16,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f42,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f17,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f43,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f18,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f44,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f49,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f43,f44])).
% 3.64/0.99  
% 3.64/0.99  fof(f50,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f42,f49])).
% 3.64/0.99  
% 3.64/0.99  fof(f51,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f41,f50])).
% 3.64/0.99  
% 3.64/0.99  fof(f53,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f40,f51])).
% 3.64/0.99  
% 3.64/0.99  fof(f9,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.64/0.99    inference(ennf_transformation,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f35,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.64/0.99    inference(cnf_transformation,[],[f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f29,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f56,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.64/0.99    inference(definition_unfolding,[],[f35,f29,f48,f39])).
% 3.64/0.99  
% 3.64/0.99  fof(f46,plain,(
% 3.64/0.99    sK0 != sK1),
% 3.64/0.99    inference(cnf_transformation,[],[f28])).
% 3.64/0.99  
% 3.64/0.99  fof(f11,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f37,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f32,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f47,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f32,f29])).
% 3.64/0.99  
% 3.64/0.99  fof(f57,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f37,f47,f44,f48])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.64/0.99    inference(cnf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f36,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f54,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f36,f47,f48,f44])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.64/0.99    inference(cnf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_8,negated_conjecture,
% 3.64/0.99      ( k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) = k1_enumset1(sK0,sK0,sK0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1150,negated_conjecture,
% 3.64/0.99      ( ~ iProver_ARSWP_27 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.64/0.99      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1232,plain,
% 3.64/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1145,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_22 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 3.64/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1237,plain,
% 3.64/0.99      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( X0 = X1
% 3.64/0.99      | X2 = X1
% 3.64/0.99      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1148,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_25
% 3.64/0.99      | X0 = X1
% 3.64/0.99      | X2 = X1
% 3.64/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 3.64/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1234,plain,
% 3.64/0.99      ( X0 = X1
% 3.64/0.99      | X2 = X1
% 3.64/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7,negated_conjecture,
% 3.64/0.99      ( sK0 != sK1 ),
% 3.64/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1301,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_25
% 3.64/0.99      | X0 = sK1
% 3.64/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | sK0 = sK1 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1148]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1302,plain,
% 3.64/0.99      ( X0 = sK1
% 3.64/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | sK0 = sK1
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1304,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | sK0 = sK1
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1302]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1637,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_1234,c_7,c_1304]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6,plain,
% 3.64/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.64/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1149,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_26
% 3.64/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.64/0.99      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1233,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1645,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1637,c_1233]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5516,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1645]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5541,plain,
% 3.64/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_5516,c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5585,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5541,c_1233]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7196,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_5585]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7484,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_7196]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1643,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1637]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1,plain,
% 3.64/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.64/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1146,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_23
% 3.64/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.64/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1236,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1146]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2900,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1643,c_1236]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2905,plain,
% 3.64/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_2900,c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3108,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2905,c_1236]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4396,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_3108]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7176,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_4396]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3099,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2905,c_1643]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1529,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1236]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4359,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2905,c_1529]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4588,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3099,c_4359]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6605,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_4588]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5558,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5541,c_1645]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5890,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_5558]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1406,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1233]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5576,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5541,c_1406]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5575,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5541,c_1643]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1530,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1236]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5521,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1645,c_1530]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4361,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1529]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4358,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1643,c_1529]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1644,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1637]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1655,plain,
% 3.64/0.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_1644,c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1673,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1655,c_1637]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1845,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1673]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1678,plain,
% 3.64/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1655,c_1237]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1677,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1655,c_1233]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2725,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1677]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3391,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1678,c_2725]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3621,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1845,c_3391]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3823,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_3621]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3624,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_3391]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3396,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_2725]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3109,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2905,c_1233]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2897,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1643]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2761,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_26 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1406]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1676,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1655,c_1236]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2322,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1232,c_1676]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2348,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1678,c_2322]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2535,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1845,c_2348]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1957,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1678,c_1530]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2570,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2535,c_1957]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2537,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_2348]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2184,plain,
% 3.64/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1957]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2004,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1237,c_1845]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1674,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1655,c_1530]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,
% 3.64/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1707,plain,
% 3.64/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_1674,c_2]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2157,plain,
% 3.64/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_27 != iProver_top
% 3.64/0.99      | iProver_ARSWP_25 != iProver_top
% 3.64/0.99      | iProver_ARSWP_23 != iProver_top
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2004,c_1707]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_22,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_21,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1427,plain,
% 3.64/0.99      ( X0 != X1 | X1 = X0 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1569,plain,
% 3.64/0.99      ( ~ iProver_ARSWP_22 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_1427,c_1145]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1570,plain,
% 3.64/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2873,plain,
% 3.64/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.64/0.99      | iProver_ARSWP_22 != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2157,c_1570]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end Saturation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ Selected
% 3.64/0.99  
% 3.64/0.99  total_time:                             0.252
% 3.64/0.99  
%------------------------------------------------------------------------------
