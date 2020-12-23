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
% DateTime   : Thu Dec  3 11:30:41 EST 2020

% Result     : CounterSatisfiable 3.31s
% Output     : Saturation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   94 (3484 expanded)
%              Number of clauses        :   44 ( 300 expanded)
%              Number of leaves         :   18 (1116 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 (4218 expanded)
%              Number of equality atoms :  164 (3919 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f47,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f55,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f56,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f61,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f47,f56,f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f30,f55,f56,f56])).

fof(f48,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f56,f55,f56])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f37,f49,f51,f53])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

cnf(c_30,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2716,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0)
    | ~ iProver_ARSWP_44 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_2806,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2716])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2712,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_2810,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2712])).

cnf(c_3115,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2806,c_2810])).

cnf(c_6,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2715,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_2807,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2715])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2885,plain,
    ( ~ iProver_ARSWP_43
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2715])).

cnf(c_2886,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK0 = sK1
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2885])).

cnf(c_3206,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2807,c_7,c_2886])).

cnf(c_3212,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3115,c_3206])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3233,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3212,c_3])).

cnf(c_3447,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_3115])).

cnf(c_3445,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_3206])).

cnf(c_4122,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3445])).

cnf(c_5,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2714,plain,
    ( ~ iProver_ARSWP_42
    | arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_2808,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2714])).

cnf(c_3213,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3206])).

cnf(c_3225,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3213,c_3])).

cnf(c_3406,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3225,c_2808])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2711,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2811,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2711])).

cnf(c_3214,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_2811])).

cnf(c_3218,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3214,c_3])).

cnf(c_3248,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_2811])).

cnf(c_4082,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_3248])).

cnf(c_4081,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3248])).

cnf(c_3245,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_3206])).

cnf(c_4079,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_3248])).

cnf(c_3400,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3225,c_3206])).

cnf(c_3963,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_3400])).

cnf(c_3452,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_2806])).

cnf(c_3700,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3452,c_2810])).

cnf(c_3407,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3225,c_2806])).

cnf(c_3252,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_2806])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.31/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.01  
% 3.31/1.01  ------  iProver source info
% 3.31/1.01  
% 3.31/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.01  git: non_committed_changes: false
% 3.31/1.01  git: last_make_outside_of_git: false
% 3.31/1.01  
% 3.31/1.01  ------ 
% 3.31/1.01  ------ Parsing...
% 3.31/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  ------ Proving...
% 3.31/1.01  ------ Problem Properties 
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  clauses                                 9
% 3.31/1.01  conjectures                             2
% 3.31/1.01  EPR                                     1
% 3.31/1.01  Horn                                    8
% 3.31/1.01  unary                                   7
% 3.31/1.01  binary                                  2
% 3.31/1.01  lits                                    11
% 3.31/1.01  lits eq                                 9
% 3.31/1.01  fd_pure                                 0
% 3.31/1.01  fd_pseudo                               0
% 3.31/1.01  fd_cond                                 0
% 3.31/1.01  fd_pseudo_cond                          1
% 3.31/1.01  AC symbols                              0
% 3.31/1.01  
% 3.31/1.01  ------ Input Options Time Limit: Unbounded
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.31/1.01  Current options:
% 3.31/1.01  ------ 
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.01  
% 3.31/1.01  ------ Proving...
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  % SZS output start Saturation for theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  fof(f20,conjecture,(
% 3.31/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f21,negated_conjecture,(
% 3.31/1.01    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.31/1.01    inference(negated_conjecture,[],[f20])).
% 3.31/1.01  
% 3.31/1.01  fof(f27,plain,(
% 3.31/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.31/1.01    inference(ennf_transformation,[],[f21])).
% 3.31/1.01  
% 3.31/1.01  fof(f28,plain,(
% 3.31/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.31/1.01    introduced(choice_axiom,[])).
% 3.31/1.01  
% 3.31/1.01  fof(f29,plain,(
% 3.31/1.01    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 3.31/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 3.31/1.01  
% 3.31/1.01  fof(f47,plain,(
% 3.31/1.01    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 3.31/1.01    inference(cnf_transformation,[],[f29])).
% 3.31/1.01  
% 3.31/1.01  fof(f11,axiom,(
% 3.31/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f38,plain,(
% 3.31/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f11])).
% 3.31/1.01  
% 3.31/1.01  fof(f12,axiom,(
% 3.31/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f39,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f12])).
% 3.31/1.01  
% 3.31/1.01  fof(f13,axiom,(
% 3.31/1.01    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f40,plain,(
% 3.31/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f13])).
% 3.31/1.01  
% 3.31/1.01  fof(f14,axiom,(
% 3.31/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f41,plain,(
% 3.31/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f14])).
% 3.31/1.01  
% 3.31/1.01  fof(f15,axiom,(
% 3.31/1.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f42,plain,(
% 3.31/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f15])).
% 3.31/1.01  
% 3.31/1.01  fof(f16,axiom,(
% 3.31/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f43,plain,(
% 3.31/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f16])).
% 3.31/1.01  
% 3.31/1.01  fof(f17,axiom,(
% 3.31/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f44,plain,(
% 3.31/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f17])).
% 3.31/1.01  
% 3.31/1.01  fof(f50,plain,(
% 3.31/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f43,f44])).
% 3.31/1.01  
% 3.31/1.01  fof(f51,plain,(
% 3.31/1.01    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f42,f50])).
% 3.31/1.01  
% 3.31/1.01  fof(f52,plain,(
% 3.31/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f41,f51])).
% 3.31/1.01  
% 3.31/1.01  fof(f53,plain,(
% 3.31/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f40,f52])).
% 3.31/1.01  
% 3.31/1.01  fof(f55,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f39,f53])).
% 3.31/1.01  
% 3.31/1.01  fof(f56,plain,(
% 3.31/1.01    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f38,f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f61,plain,(
% 3.31/1.01    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.31/1.01    inference(definition_unfolding,[],[f47,f56,f56])).
% 3.31/1.01  
% 3.31/1.01  fof(f3,axiom,(
% 3.31/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f25,plain,(
% 3.31/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.31/1.01    inference(ennf_transformation,[],[f3])).
% 3.31/1.01  
% 3.31/1.01  fof(f31,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f25])).
% 3.31/1.01  
% 3.31/1.01  fof(f19,axiom,(
% 3.31/1.01    ! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f26,plain,(
% 3.31/1.01    ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1)),
% 3.31/1.01    inference(ennf_transformation,[],[f19])).
% 3.31/1.01  
% 3.31/1.01  fof(f46,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.31/1.01    inference(cnf_transformation,[],[f26])).
% 3.31/1.01  
% 3.31/1.01  fof(f2,axiom,(
% 3.31/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f30,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.31/1.01    inference(cnf_transformation,[],[f2])).
% 3.31/1.01  
% 3.31/1.01  fof(f60,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.31/1.01    inference(definition_unfolding,[],[f46,f30,f55,f56,f56])).
% 3.31/1.01  
% 3.31/1.01  fof(f48,plain,(
% 3.31/1.01    sK0 != sK1),
% 3.31/1.01    inference(cnf_transformation,[],[f29])).
% 3.31/1.01  
% 3.31/1.01  fof(f6,axiom,(
% 3.31/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f33,plain,(
% 3.31/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f6])).
% 3.31/1.01  
% 3.31/1.01  fof(f18,axiom,(
% 3.31/1.01    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f45,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f18])).
% 3.31/1.01  
% 3.31/1.01  fof(f59,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f45,f56,f55,f56])).
% 3.31/1.01  
% 3.31/1.01  fof(f10,axiom,(
% 3.31/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f37,plain,(
% 3.31/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f10])).
% 3.31/1.01  
% 3.31/1.01  fof(f7,axiom,(
% 3.31/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f34,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f7])).
% 3.31/1.01  
% 3.31/1.01  fof(f49,plain,(
% 3.31/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f34,f30])).
% 3.31/1.01  
% 3.31/1.01  fof(f57,plain,(
% 3.31/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.31/1.01    inference(definition_unfolding,[],[f37,f49,f51,f53])).
% 3.31/1.01  
% 3.31/1.01  fof(f4,axiom,(
% 3.31/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f32,plain,(
% 3.31/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.31/1.01    inference(cnf_transformation,[],[f4])).
% 3.31/1.01  
% 3.31/1.01  cnf(c_30,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8,negated_conjecture,
% 3.31/1.01      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.31/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2716,negated_conjecture,
% 3.31/1.01      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) | ~ iProver_ARSWP_44 ),
% 3.31/1.01      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2806,plain,
% 3.31/1.01      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2716]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1,plain,
% 3.31/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.31/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2712,plain,
% 3.31/1.01      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.31/1.01      | ~ iProver_ARSWP_40
% 3.31/1.01      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.31/1.01      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2810,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.31/1.01      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2712]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3115,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2806,c_2810]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6,plain,
% 3.31/1.01      ( X0 = X1
% 3.31/1.01      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2715,plain,
% 3.31/1.01      ( ~ iProver_ARSWP_43
% 3.31/1.01      | X0 = X1
% 3.31/1.01      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
% 3.31/1.01      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2807,plain,
% 3.31/1.01      ( X0 = X1
% 3.31/1.01      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2715]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7,negated_conjecture,
% 3.31/1.01      ( sK0 != sK1 ),
% 3.31/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2885,plain,
% 3.31/1.01      ( ~ iProver_ARSWP_43
% 3.31/1.01      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | sK0 = sK1 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2715]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2886,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | sK0 = sK1
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2885]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3206,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_2807,c_7,c_2886]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3212,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3115,c_3206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3,plain,
% 3.31/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.31/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3233,plain,
% 3.31/1.01      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_3212,c_3]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3447,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3233,c_3115]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3445,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3233,c_3206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4122,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3447,c_3445]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5,plain,
% 3.31/1.01      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2714,plain,
% 3.31/1.01      ( ~ iProver_ARSWP_42
% 3.31/1.01      | arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0 ),
% 3.31/1.01      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2808,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2714]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3213,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2808,c_3206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3225,plain,
% 3.31/1.01      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_3213,c_3]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3406,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3225,c_2808]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_0,plain,
% 3.31/1.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.31/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2711,plain,
% 3.31/1.01      ( ~ iProver_ARSWP_39
% 3.31/1.01      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
% 3.31/1.01      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2811,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2711]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3214,plain,
% 3.31/1.01      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3206,c_2811]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3218,plain,
% 3.31/1.01      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_3214,c_3]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3248,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3218,c_2811]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4082,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3406,c_3248]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4081,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3447,c_3248]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3245,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3218,c_3206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4079,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3245,c_3248]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3400,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3225,c_3206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3963,plain,
% 3.31/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3406,c_3400]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3452,plain,
% 3.31/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3233,c_2806]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3700,plain,
% 3.31/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_40 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3452,c_2810]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3407,plain,
% 3.31/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3225,c_2806]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3252,plain,
% 3.31/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.31/1.01      | iProver_ARSWP_44 != iProver_top
% 3.31/1.01      | iProver_ARSWP_43 != iProver_top
% 3.31/1.01      | iProver_ARSWP_39 != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3218,c_2806]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2,plain,
% 3.31/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.31/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  % SZS output end Saturation for theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  ------                               Statistics
% 3.31/1.01  
% 3.31/1.01  ------ Selected
% 3.31/1.01  
% 3.31/1.01  total_time:                             0.182
% 3.31/1.01  
%------------------------------------------------------------------------------
