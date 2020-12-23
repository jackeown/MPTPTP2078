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
% DateTime   : Thu Dec  3 11:31:02 EST 2020

% Result     : CounterSatisfiable 3.58s
% Output     : Saturation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   84 (1985 expanded)
%              Number of clauses        :   36 ( 208 expanded)
%              Number of leaves         :   17 ( 625 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 (2781 expanded)
%              Number of equality atoms :  154 (2549 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f52,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
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

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f70,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f52,f62,f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f42,f32,f59,f62,f60])).

fof(f54,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f43,f55,f56,f60])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

cnf(c_34,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2600,negated_conjecture,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0)
    | ~ iProver_ARSWP_44 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_2688,plain,
    ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2596,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_40
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_2692,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2596])).

cnf(c_2946,plain,
    ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2688,c_2692])).

cnf(c_8,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2599,plain,
    ( ~ iProver_ARSWP_43
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_2689,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_10,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2830,plain,
    ( ~ iProver_ARSWP_43
    | X0 = sK2
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_2831,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK0 = sK2
    | iProver_ARSWP_43 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2830])).

cnf(c_2833,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | sK0 = sK2
    | iProver_ARSWP_43 != iProver_top ),
    inference(instantiation,[status(thm)],[c_2831])).

cnf(c_3023,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2689,c_10,c_2833])).

cnf(c_3029,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_2946,c_3023])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3042,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3029,c_3])).

cnf(c_3156,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_2946])).

cnf(c_3154,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_3023])).

cnf(c_3608,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_3154])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2595,plain,
    ( ~ iProver_ARSWP_39
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_2693,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2595])).

cnf(c_3030,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_2693])).

cnf(c_3034,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3030,c_3])).

cnf(c_3056,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_2693])).

cnf(c_3376,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_3056])).

cnf(c_3160,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_2688])).

cnf(c_3369,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_40 != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_2692])).

cnf(c_3053,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_3023])).

cnf(c_3260,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_3056])).

cnf(c_3059,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_44 != iProver_top
    | iProver_ARSWP_43 != iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_2688])).

cnf(c_11,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.58/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/1.02  
% 3.58/1.02  ------  iProver source info
% 3.58/1.02  
% 3.58/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.58/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/1.02  git: non_committed_changes: false
% 3.58/1.02  git: last_make_outside_of_git: false
% 3.58/1.02  
% 3.58/1.02  ------ 
% 3.58/1.02  ------ Parsing...
% 3.58/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  ------ Proving...
% 3.58/1.02  ------ Problem Properties 
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  clauses                                 13
% 3.58/1.02  conjectures                             3
% 3.58/1.02  EPR                                     2
% 3.58/1.02  Horn                                    12
% 3.58/1.02  unary                                   11
% 3.58/1.02  binary                                  1
% 3.58/1.02  lits                                    16
% 3.58/1.02  lits eq                                 14
% 3.58/1.02  fd_pure                                 0
% 3.58/1.02  fd_pseudo                               0
% 3.58/1.02  fd_cond                                 0
% 3.58/1.02  fd_pseudo_cond                          1
% 3.58/1.02  AC symbols                              0
% 3.58/1.02  
% 3.58/1.02  ------ Input Options Time Limit: Unbounded
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.58/1.02  Current options:
% 3.58/1.02  ------ 
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/1.02  
% 3.58/1.02  ------ Proving...
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  % SZS output start Saturation for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  fof(f23,conjecture,(
% 3.58/1.02    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f24,negated_conjecture,(
% 3.58/1.02    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.58/1.02    inference(negated_conjecture,[],[f23])).
% 3.58/1.02  
% 3.58/1.02  fof(f29,plain,(
% 3.58/1.02    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.58/1.02    inference(ennf_transformation,[],[f24])).
% 3.58/1.02  
% 3.58/1.02  fof(f30,plain,(
% 3.58/1.02    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 3.58/1.02    introduced(choice_axiom,[])).
% 3.58/1.02  
% 3.58/1.02  fof(f31,plain,(
% 3.58/1.02    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 3.58/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 3.58/1.02  
% 3.58/1.02  fof(f52,plain,(
% 3.58/1.02    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 3.58/1.02    inference(cnf_transformation,[],[f31])).
% 3.58/1.02  
% 3.58/1.02  fof(f16,axiom,(
% 3.58/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f45,plain,(
% 3.58/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f16])).
% 3.58/1.02  
% 3.58/1.02  fof(f62,plain,(
% 3.58/1.02    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f45,f60])).
% 3.58/1.02  
% 3.58/1.02  fof(f17,axiom,(
% 3.58/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f46,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f17])).
% 3.58/1.02  
% 3.58/1.02  fof(f18,axiom,(
% 3.58/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f47,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f18])).
% 3.58/1.02  
% 3.58/1.02  fof(f19,axiom,(
% 3.58/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f48,plain,(
% 3.58/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f19])).
% 3.58/1.02  
% 3.58/1.02  fof(f20,axiom,(
% 3.58/1.02    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f49,plain,(
% 3.58/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f20])).
% 3.58/1.02  
% 3.58/1.02  fof(f21,axiom,(
% 3.58/1.02    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f50,plain,(
% 3.58/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f21])).
% 3.58/1.02  
% 3.58/1.02  fof(f22,axiom,(
% 3.58/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f51,plain,(
% 3.58/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f22])).
% 3.58/1.02  
% 3.58/1.02  fof(f56,plain,(
% 3.58/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f50,f51])).
% 3.58/1.02  
% 3.58/1.02  fof(f57,plain,(
% 3.58/1.02    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f49,f56])).
% 3.58/1.02  
% 3.58/1.02  fof(f58,plain,(
% 3.58/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f48,f57])).
% 3.58/1.02  
% 3.58/1.02  fof(f59,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f47,f58])).
% 3.58/1.02  
% 3.58/1.02  fof(f60,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f46,f59])).
% 3.58/1.02  
% 3.58/1.02  fof(f70,plain,(
% 3.58/1.02    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.58/1.02    inference(definition_unfolding,[],[f52,f62,f60])).
% 3.58/1.02  
% 3.58/1.02  fof(f3,axiom,(
% 3.58/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f27,plain,(
% 3.58/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.58/1.02    inference(ennf_transformation,[],[f3])).
% 3.58/1.02  
% 3.58/1.02  fof(f33,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f27])).
% 3.58/1.02  
% 3.58/1.02  fof(f13,axiom,(
% 3.58/1.02    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f28,plain,(
% 3.58/1.02    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.58/1.02    inference(ennf_transformation,[],[f13])).
% 3.58/1.02  
% 3.58/1.02  fof(f42,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.58/1.02    inference(cnf_transformation,[],[f28])).
% 3.58/1.02  
% 3.58/1.02  fof(f2,axiom,(
% 3.58/1.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f32,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f2])).
% 3.58/1.02  
% 3.58/1.02  fof(f68,plain,(
% 3.58/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.58/1.02    inference(definition_unfolding,[],[f42,f32,f59,f62,f60])).
% 3.58/1.02  
% 3.58/1.02  fof(f54,plain,(
% 3.58/1.02    sK0 != sK2),
% 3.58/1.02    inference(cnf_transformation,[],[f31])).
% 3.58/1.02  
% 3.58/1.02  fof(f6,axiom,(
% 3.58/1.02    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f35,plain,(
% 3.58/1.02    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.58/1.02    inference(cnf_transformation,[],[f6])).
% 3.58/1.02  
% 3.58/1.02  fof(f14,axiom,(
% 3.58/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f43,plain,(
% 3.58/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f14])).
% 3.58/1.02  
% 3.58/1.02  fof(f7,axiom,(
% 3.58/1.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f36,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.58/1.02    inference(cnf_transformation,[],[f7])).
% 3.58/1.02  
% 3.58/1.02  fof(f55,plain,(
% 3.58/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f36,f32])).
% 3.58/1.02  
% 3.58/1.02  fof(f63,plain,(
% 3.58/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.58/1.02    inference(definition_unfolding,[],[f43,f55,f56,f60])).
% 3.58/1.02  
% 3.58/1.02  fof(f53,plain,(
% 3.58/1.02    sK0 != sK1),
% 3.58/1.02    inference(cnf_transformation,[],[f31])).
% 3.58/1.02  
% 3.58/1.02  fof(f4,axiom,(
% 3.58/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.02  
% 3.58/1.02  fof(f34,plain,(
% 3.58/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.58/1.02    inference(cnf_transformation,[],[f4])).
% 3.58/1.02  
% 3.58/1.02  cnf(c_34,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_12,negated_conjecture,
% 3.58/1.02      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.58/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2600,negated_conjecture,
% 3.58/1.02      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) | ~ iProver_ARSWP_44 ),
% 3.58/1.02      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2688,plain,
% 3.58/1.02      ( arAF0_r1_tarski_0_1(arAF0_k6_enumset1_0) = iProver_top
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_1,plain,
% 3.58/1.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.58/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2596,plain,
% 3.58/1.02      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.58/1.02      | ~ iProver_ARSWP_40
% 3.58/1.02      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.58/1.02      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2692,plain,
% 3.58/1.02      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.58/1.02      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_2596]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2946,plain,
% 3.58/1.02      ( arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_2688,c_2692]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_8,plain,
% 3.58/1.02      ( X0 = X1
% 3.58/1.02      | X2 = X1
% 3.58/1.02      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 3.58/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2599,plain,
% 3.58/1.02      ( ~ iProver_ARSWP_43
% 3.58/1.02      | X0 = X1
% 3.58/1.02      | X2 = X1
% 3.58/1.02      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0 ),
% 3.58/1.02      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2689,plain,
% 3.58/1.02      ( X0 = X1
% 3.58/1.02      | X2 = X1
% 3.58/1.02      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_10,negated_conjecture,
% 3.58/1.02      ( sK0 != sK2 ),
% 3.58/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2830,plain,
% 3.58/1.02      ( ~ iProver_ARSWP_43
% 3.58/1.02      | X0 = sK2
% 3.58/1.02      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | sK0 = sK2 ),
% 3.58/1.02      inference(instantiation,[status(thm)],[c_2599]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2831,plain,
% 3.58/1.02      ( X0 = sK2
% 3.58/1.02      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | sK0 = sK2
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_2830]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2833,plain,
% 3.58/1.02      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | sK0 = sK2
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top ),
% 3.58/1.02      inference(instantiation,[status(thm)],[c_2831]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3023,plain,
% 3.58/1.02      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top ),
% 3.58/1.02      inference(global_propositional_subsumption,
% 3.58/1.02                [status(thm)],
% 3.58/1.02                [c_2689,c_10,c_2833]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3029,plain,
% 3.58/1.02      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_2946,c_3023]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3,plain,
% 3.58/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.58/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3042,plain,
% 3.58/1.02      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(demodulation,[status(thm)],[c_3029,c_3]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3156,plain,
% 3.58/1.02      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3042,c_2946]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3154,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3042,c_3023]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3608,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3156,c_3154]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_0,plain,
% 3.58/1.02      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.58/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2595,plain,
% 3.58/1.02      ( ~ iProver_ARSWP_39
% 3.58/1.02      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0 ),
% 3.58/1.02      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2693,plain,
% 3.58/1.02      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0_1(arAF0_k6_enumset1_0))) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(predicate_to_equality,[status(thm)],[c_2595]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3030,plain,
% 3.58/1.02      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3023,c_2693]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3034,plain,
% 3.58/1.02      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(demodulation,[status(thm)],[c_3030,c_3]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3056,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0))) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3034,c_2693]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3376,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3156,c_3056]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3160,plain,
% 3.58/1.02      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3042,c_2688]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3369,plain,
% 3.58/1.02      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_40 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3160,c_2692]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3053,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0_1(k1_xboole_0)) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3034,c_3023]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3260,plain,
% 3.58/1.02      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3053,c_3056]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_3059,plain,
% 3.58/1.02      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.58/1.02      | iProver_ARSWP_44 != iProver_top
% 3.58/1.02      | iProver_ARSWP_43 != iProver_top
% 3.58/1.02      | iProver_ARSWP_39 != iProver_top ),
% 3.58/1.02      inference(superposition,[status(thm)],[c_3034,c_2688]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_11,negated_conjecture,
% 3.58/1.02      ( sK0 != sK1 ),
% 3.58/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.58/1.02  
% 3.58/1.02  cnf(c_2,plain,
% 3.58/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.58/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.58/1.02  
% 3.58/1.02  
% 3.58/1.02  % SZS output end Saturation for theBenchmark.p
% 3.58/1.02  
% 3.58/1.02  ------                               Statistics
% 3.58/1.02  
% 3.58/1.02  ------ Selected
% 3.58/1.02  
% 3.58/1.02  total_time:                             0.158
% 3.58/1.02  
%------------------------------------------------------------------------------
