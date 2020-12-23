%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:40 EST 2020

% Result     : CounterSatisfiable 3.50s
% Output     : Saturation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   94 (3064 expanded)
%              Number of clauses        :   44 ( 300 expanded)
%              Number of leaves         :   18 ( 976 expanded)
%              Depth                    :   16
%              Number of atoms          :  185 (3798 expanded)
%              Number of equality atoms :  164 (3499 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f49,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f64,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f49,f58,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f48,f31,f57,f58,f58])).

fof(f50,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f58,f57,f58])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f36,f51,f53,f53])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

cnf(c_32,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2736,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0)
    | ~ iProver_ARSWP_48 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_2833,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
    | iProver_ARSWP_48 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2736])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2731,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_43
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_2838,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_3143,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_2838])).

cnf(c_7,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2735,plain,
    ( ~ iProver_ARSWP_47
    | X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_2834,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2735])).

cnf(c_8,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2913,plain,
    ( ~ iProver_ARSWP_47
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2735])).

cnf(c_2914,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | sK0 = sK1
    | iProver_ARSWP_47 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2913])).

cnf(c_3234,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2834,c_8,c_2914])).

cnf(c_3240,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3143,c_3234])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3261,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3240,c_3])).

cnf(c_3467,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_3143])).

cnf(c_3465,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_3234])).

cnf(c_4119,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3467,c_3465])).

cnf(c_6,plain,
    ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2734,plain,
    ( ~ iProver_ARSWP_46
    | arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_2835,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_46 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2734])).

cnf(c_3241,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_3234])).

cnf(c_3253,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3241,c_3])).

cnf(c_3426,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3253,c_2835])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2730,plain,
    ( ~ iProver_ARSWP_42
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2839,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_3242,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_2839])).

cnf(c_3246,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3242,c_3])).

cnf(c_3276,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_2839])).

cnf(c_4079,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3426,c_3276])).

cnf(c_4078,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3467,c_3276])).

cnf(c_3273,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_3234])).

cnf(c_4076,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3273,c_3276])).

cnf(c_3420,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3253,c_3234])).

cnf(c_3959,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3426,c_3420])).

cnf(c_3472,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_2833])).

cnf(c_3703,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_43 != iProver_top ),
    inference(superposition,[status(thm)],[c_3472,c_2838])).

cnf(c_3427,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_46 != iProver_top ),
    inference(superposition,[status(thm)],[c_3253,c_2833])).

cnf(c_3280,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_47 != iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_2833])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.01  
% 3.50/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.01  
% 3.50/1.01  ------  iProver source info
% 3.50/1.01  
% 3.50/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.01  git: non_committed_changes: false
% 3.50/1.01  git: last_make_outside_of_git: false
% 3.50/1.01  
% 3.50/1.01  ------ 
% 3.50/1.01  ------ Parsing...
% 3.50/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  ------ Proving...
% 3.50/1.01  ------ Problem Properties 
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  clauses                                 10
% 3.50/1.01  conjectures                             2
% 3.50/1.01  EPR                                     1
% 3.50/1.01  Horn                                    9
% 3.50/1.01  unary                                   8
% 3.50/1.01  binary                                  2
% 3.50/1.01  lits                                    12
% 3.50/1.01  lits eq                                 10
% 3.50/1.01  fd_pure                                 0
% 3.50/1.01  fd_pseudo                               0
% 3.50/1.01  fd_cond                                 0
% 3.50/1.01  fd_pseudo_cond                          1
% 3.50/1.01  AC symbols                              0
% 3.50/1.01  
% 3.50/1.01  ------ Input Options Time Limit: Unbounded
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.50/1.01  Current options:
% 3.50/1.01  ------ 
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.50/1.01  
% 3.50/1.01  ------ Proving...
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.50/1.01  
% 3.50/1.01  % SZS output start Saturation for theBenchmark.p
% 3.50/1.01  
% 3.50/1.01  fof(f21,conjecture,(
% 3.50/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f22,negated_conjecture,(
% 3.50/1.01    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.50/1.01    inference(negated_conjecture,[],[f21])).
% 3.50/1.01  
% 3.50/1.01  fof(f28,plain,(
% 3.50/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.50/1.01    inference(ennf_transformation,[],[f22])).
% 3.50/1.01  
% 3.50/1.01  fof(f29,plain,(
% 3.50/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.50/1.01    introduced(choice_axiom,[])).
% 3.50/1.01  
% 3.50/1.01  fof(f30,plain,(
% 3.50/1.01    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 3.50/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 3.50/1.01  
% 3.50/1.01  fof(f49,plain,(
% 3.50/1.01    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 3.50/1.01    inference(cnf_transformation,[],[f30])).
% 3.50/1.01  
% 3.50/1.01  fof(f12,axiom,(
% 3.50/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f40,plain,(
% 3.50/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f12])).
% 3.50/1.01  
% 3.50/1.01  fof(f13,axiom,(
% 3.50/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f41,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f13])).
% 3.50/1.01  
% 3.50/1.01  fof(f14,axiom,(
% 3.50/1.01    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f42,plain,(
% 3.50/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f14])).
% 3.50/1.01  
% 3.50/1.01  fof(f15,axiom,(
% 3.50/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f43,plain,(
% 3.50/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f15])).
% 3.50/1.01  
% 3.50/1.01  fof(f16,axiom,(
% 3.50/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f44,plain,(
% 3.50/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f16])).
% 3.50/1.01  
% 3.50/1.01  fof(f17,axiom,(
% 3.50/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f45,plain,(
% 3.50/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f17])).
% 3.50/1.01  
% 3.50/1.01  fof(f52,plain,(
% 3.50/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f44,f45])).
% 3.50/1.01  
% 3.50/1.01  fof(f53,plain,(
% 3.50/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f43,f52])).
% 3.50/1.01  
% 3.50/1.01  fof(f56,plain,(
% 3.50/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f42,f53])).
% 3.50/1.01  
% 3.50/1.01  fof(f57,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f41,f56])).
% 3.50/1.01  
% 3.50/1.01  fof(f58,plain,(
% 3.50/1.01    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f40,f57])).
% 3.50/1.01  
% 3.50/1.01  fof(f64,plain,(
% 3.50/1.01    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.50/1.01    inference(definition_unfolding,[],[f49,f58,f58])).
% 3.50/1.01  
% 3.50/1.01  fof(f3,axiom,(
% 3.50/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f26,plain,(
% 3.50/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.50/1.01    inference(ennf_transformation,[],[f3])).
% 3.50/1.01  
% 3.50/1.01  fof(f32,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f26])).
% 3.50/1.01  
% 3.50/1.01  fof(f20,axiom,(
% 3.50/1.01    ! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f27,plain,(
% 3.50/1.01    ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1)),
% 3.50/1.01    inference(ennf_transformation,[],[f20])).
% 3.50/1.01  
% 3.50/1.01  fof(f48,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.50/1.01    inference(cnf_transformation,[],[f27])).
% 3.50/1.01  
% 3.50/1.01  fof(f2,axiom,(
% 3.50/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f31,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.50/1.01    inference(cnf_transformation,[],[f2])).
% 3.50/1.01  
% 3.50/1.01  fof(f63,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.50/1.01    inference(definition_unfolding,[],[f48,f31,f57,f58,f58])).
% 3.50/1.01  
% 3.50/1.01  fof(f50,plain,(
% 3.50/1.01    sK0 != sK1),
% 3.50/1.01    inference(cnf_transformation,[],[f30])).
% 3.50/1.01  
% 3.50/1.01  fof(f6,axiom,(
% 3.50/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f34,plain,(
% 3.50/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f6])).
% 3.50/1.01  
% 3.50/1.01  fof(f19,axiom,(
% 3.50/1.01    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f47,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f19])).
% 3.50/1.01  
% 3.50/1.01  fof(f62,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f47,f58,f57,f58])).
% 3.50/1.01  
% 3.50/1.01  fof(f18,axiom,(
% 3.50/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f46,plain,(
% 3.50/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f18])).
% 3.50/1.01  
% 3.50/1.01  fof(f8,axiom,(
% 3.50/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f36,plain,(
% 3.50/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f8])).
% 3.50/1.01  
% 3.50/1.01  fof(f7,axiom,(
% 3.50/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f35,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f7])).
% 3.50/1.01  
% 3.50/1.01  fof(f51,plain,(
% 3.50/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f35,f31])).
% 3.50/1.01  
% 3.50/1.01  fof(f54,plain,(
% 3.50/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f36,f51,f53,f53])).
% 3.50/1.01  
% 3.50/1.01  fof(f59,plain,(
% 3.50/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/1.01    inference(definition_unfolding,[],[f46,f54])).
% 3.50/1.01  
% 3.50/1.01  fof(f4,axiom,(
% 3.50/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.01  
% 3.50/1.01  fof(f33,plain,(
% 3.50/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.50/1.01    inference(cnf_transformation,[],[f4])).
% 3.50/1.01  
% 3.50/1.01  cnf(c_32,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9,negated_conjecture,
% 3.50/1.01      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.50/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2736,negated_conjecture,
% 3.50/1.01      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) | ~ iProver_ARSWP_48 ),
% 3.50/1.01      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2833,plain,
% 3.50/1.01      ( arAF0_r1_tarski_0_1(arAF0_k5_enumset1_0) = iProver_top
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2736]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1,plain,
% 3.50/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2731,plain,
% 3.50/1.01      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.50/1.01      | ~ iProver_ARSWP_43
% 3.50/1.01      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.50/1.01      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2838,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.50/1.01      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3143,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2833,c_2838]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_7,plain,
% 3.50/1.01      ( X0 = X1
% 3.50/1.01      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
% 3.50/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2735,plain,
% 3.50/1.01      ( ~ iProver_ARSWP_47
% 3.50/1.01      | X0 = X1
% 3.50/1.01      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0 ),
% 3.50/1.01      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2834,plain,
% 3.50/1.01      ( X0 = X1
% 3.50/1.01      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2735]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8,negated_conjecture,
% 3.50/1.01      ( sK0 != sK1 ),
% 3.50/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2913,plain,
% 3.50/1.01      ( ~ iProver_ARSWP_47
% 3.50/1.01      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | sK0 = sK1 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2735]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2914,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | sK0 = sK1
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2913]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3234,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_2834,c_8,c_2914]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3240,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3143,c_3234]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3,plain,
% 3.50/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3261,plain,
% 3.50/1.01      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_3240,c_3]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3467,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3261,c_3143]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3465,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3261,c_3234]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4119,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3467,c_3465]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6,plain,
% 3.50/1.01      ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2734,plain,
% 3.50/1.01      ( ~ iProver_ARSWP_46
% 3.50/1.01      | arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0 ),
% 3.50/1.01      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2835,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2734]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3241,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2835,c_3234]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3253,plain,
% 3.50/1.01      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_3241,c_3]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3426,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3253,c_2835]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_0,plain,
% 3.50/1.01      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.50/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2730,plain,
% 3.50/1.01      ( ~ iProver_ARSWP_42
% 3.50/1.01      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0 ),
% 3.50/1.01      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2839,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k5_enumset1_0))) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2730]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3242,plain,
% 3.50/1.01      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3234,c_2839]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3246,plain,
% 3.50/1.01      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_3242,c_3]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3276,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3246,c_2839]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4079,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3426,c_3276]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4078,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3467,c_3276]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3273,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3246,c_3234]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4076,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3273,c_3276]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3420,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3253,c_3234]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3959,plain,
% 3.50/1.01      ( k5_xboole_0(k1_xboole_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3426,c_3420]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3472,plain,
% 3.50/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3261,c_2833]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3703,plain,
% 3.50/1.01      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_43 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3472,c_2838]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3427,plain,
% 3.50/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_46 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3253,c_2833]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3280,plain,
% 3.50/1.01      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.50/1.01      | iProver_ARSWP_48 != iProver_top
% 3.50/1.01      | iProver_ARSWP_47 != iProver_top
% 3.50/1.01      | iProver_ARSWP_42 != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_3246,c_2833]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2,plain,
% 3.50/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  % SZS output end Saturation for theBenchmark.p
% 3.50/1.01  
% 3.50/1.01  ------                               Statistics
% 3.50/1.01  
% 3.50/1.01  ------ Selected
% 3.50/1.01  
% 3.50/1.01  total_time:                             0.224
% 3.50/1.01  
%------------------------------------------------------------------------------
