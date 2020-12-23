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
% DateTime   : Thu Dec  3 11:35:37 EST 2020

% Result     : CounterSatisfiable 3.72s
% Output     : Saturation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  142 (2357 expanded)
%              Number of clauses        :   85 ( 438 expanded)
%              Number of leaves         :   21 ( 665 expanded)
%              Depth                    :   19
%              Number of atoms          :  442 (4030 expanded)
%              Number of equality atoms :  348 (2664 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f56,f56])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
      & ( ~ r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).

fof(f49,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(definition_unfolding,[],[f49,f37,f56])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK2 ),
    inference(definition_unfolding,[],[f50,f37,f56])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_102,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_753,plain,
    ( r2_hidden(arAF0_sK1_0,X0)
    | ~ iProver_ARSWP_24
    | k1_xboole_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_3])).

cnf(c_894,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(arAF0_sK1_0,X0) = iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_5,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_754,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1)
    | ~ iProver_ARSWP_25 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_893,plain,
    ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1) = iProver_top
    | iProver_ARSWP_25 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_751,plain,
    ( ~ r2_hidden(X0,arAF0_k3_xboole_0_0)
    | ~ r1_xboole_0(X1,X2)
    | ~ iProver_ARSWP_22 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_896,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_1165,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_896])).

cnf(c_1247,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_1165])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_756,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ iProver_ARSWP_27
    | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_891,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | r2_hidden(X0,X1) != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_1246,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | k1_xboole_0 = X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_891])).

cnf(c_1487,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1246])).

cnf(c_4605,plain,
    ( arAF0_k6_enumset1_0 = X0
    | arAF0_k3_xboole_0_0 != X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1487])).

cnf(c_5015,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_4605])).

cnf(c_1503,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | arAF0_k3_xboole_0_0 != k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1246])).

cnf(c_4047,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1503])).

cnf(c_4604,plain,
    ( arAF0_k6_enumset1_0 != X0
    | arAF0_k3_xboole_0_0 = X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1487])).

cnf(c_4824,plain,
    ( arAF0_k3_xboole_0_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_4047,c_4604])).

cnf(c_4603,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 != X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1487])).

cnf(c_4628,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4603,c_1487])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_755,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(arAF0_k6_enumset1_0,X1)
    | ~ iProver_ARSWP_26 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_892,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(arAF0_k6_enumset1_0,X1) = iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_758,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | ~ iProver_ARSWP_29
    | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2 ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_889,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r2_hidden(sK3,sK2) != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_1359,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k6_enumset1_0,sK2) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_889])).

cnf(c_4669,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k3_xboole_0_0,sK2) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_1359])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_752,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0)
    | r1_xboole_0(X0,X1)
    | ~ iProver_ARSWP_23 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_895,plain,
    ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_1395,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_23 != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_891])).

cnf(c_3639,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1395,c_896])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_757,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | ~ iProver_ARSWP_28
    | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) != sK2 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_890,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) != sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1497,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != sK2
    | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_890])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1756,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | sK2 != sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1497,c_4])).

cnf(c_1757,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1756])).

cnf(c_2431,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_891])).

cnf(c_1973,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_896])).

cnf(c_2061,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_1973])).

cnf(c_2757,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2061])).

cnf(c_1504,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 != k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1246])).

cnf(c_2063,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_1973])).

cnf(c_114,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1138,plain,
    ( r1_xboole_0(X0,arAF0_k3_xboole_0_0)
    | ~ r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)
    | X0 != arAF0_k6_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_2409,plain,
    ( ~ r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)
    | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0)
    | arAF0_k3_xboole_0_0 != arAF0_k6_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_2410,plain,
    ( arAF0_k3_xboole_0_0 != arAF0_k6_enumset1_0
    | r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) != iProver_top
    | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_112,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1109,plain,
    ( X0 != X1
    | arAF0_k3_xboole_0_0 != X1
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_1151,plain,
    ( X0 != arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 = X0
    | arAF0_k3_xboole_0_0 != arAF0_k3_xboole_0_0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1152,plain,
    ( X0 != arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1151])).

cnf(c_2531,plain,
    ( arAF0_k6_enumset1_0 != arAF0_k3_xboole_0_0
    | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_3483,plain,
    ( iProver_ARSWP_29 != iProver_top
    | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
    | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_1504,c_2061,c_2063,c_2410,c_2531])).

cnf(c_3484,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(renaming,[status(thm)],[c_3483])).

cnf(c_1659,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_890])).

cnf(c_1666,plain,
    ( sK2 != sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1659,c_4])).

cnf(c_1667,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1666])).

cnf(c_2127,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_891])).

cnf(c_3329,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2127,c_1247,c_1504])).

cnf(c_3127,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(sK3,sK2) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2063,c_890])).

cnf(c_1358,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_891])).

cnf(c_2976,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_896])).

cnf(c_2758,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(arAF0_k3_xboole_0_0,sK2) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_1359])).

cnf(c_1394,plain,
    ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_896])).

cnf(c_2578,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_1394])).

cnf(c_2128,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_889])).

cnf(c_2291,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_28 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_893])).

cnf(c_2062,plain,
    ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_1973])).

cnf(c_1658,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_893])).

cnf(c_1677,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1658,c_4])).

cnf(c_1657,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1165])).

cnf(c_1496,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_893])).

cnf(c_1768,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1496,c_4])).

cnf(c_1502,plain,
    ( arAF0_k6_enumset1_0 != k1_xboole_0
    | arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1246])).

cnf(c_1488,plain,
    ( k5_xboole_0(X0,X1) = X0
    | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_24 != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_4])).

cnf(c_1396,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_23 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_1165])).

cnf(c_1360,plain,
    ( r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = iProver_top
    | iProver_ARSWP_26 != iProver_top
    | iProver_ARSWP_25 != iProver_top
    | iProver_ARSWP_22 != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_1165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:18:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.72/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.97  
% 3.72/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.97  
% 3.72/0.97  ------  iProver source info
% 3.72/0.97  
% 3.72/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.97  git: non_committed_changes: false
% 3.72/0.97  git: last_make_outside_of_git: false
% 3.72/0.97  
% 3.72/0.97  ------ 
% 3.72/0.97  ------ Parsing...
% 3.72/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.97  
% 3.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/0.97  
% 3.72/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.97  
% 3.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.97  ------ Proving...
% 3.72/0.97  ------ Problem Properties 
% 3.72/0.97  
% 3.72/0.97  
% 3.72/0.97  clauses                                 10
% 3.72/0.97  conjectures                             2
% 3.72/0.97  EPR                                     0
% 3.72/0.97  Horn                                    7
% 3.72/0.97  unary                                   3
% 3.72/0.97  binary                                  7
% 3.72/0.97  lits                                    17
% 3.72/0.97  lits eq                                 6
% 3.72/0.97  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 1
% 3.72/0.98  fd_pseudo_cond                          0
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Input Options Time Limit: Unbounded
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start Saturation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f4,axiom,(
% 3.72/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f22,plain,(
% 3.72/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.72/0.98    inference(ennf_transformation,[],[f4])).
% 3.72/0.98  
% 3.72/0.98  fof(f28,plain,(
% 3.72/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f29,plain,(
% 3.72/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f29])).
% 3.72/0.98  
% 3.72/0.98  fof(f7,axiom,(
% 3.72/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f39,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f7])).
% 3.72/0.98  
% 3.72/0.98  fof(f5,axiom,(
% 3.72/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f5])).
% 3.72/0.98  
% 3.72/0.98  fof(f57,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f39,f37])).
% 3.72/0.98  
% 3.72/0.98  fof(f3,axiom,(
% 3.72/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f19,plain,(
% 3.72/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.98    inference(rectify,[],[f3])).
% 3.72/0.98  
% 3.72/0.98  fof(f21,plain,(
% 3.72/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.98    inference(ennf_transformation,[],[f19])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f27,plain,(
% 3.72/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f26])).
% 3.72/0.98  
% 3.72/0.98  fof(f35,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f27])).
% 3.72/0.98  
% 3.72/0.98  fof(f16,axiom,(
% 3.72/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f24,plain,(
% 3.72/0.98    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 3.72/0.98    inference(ennf_transformation,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f48,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f24])).
% 3.72/0.98  
% 3.72/0.98  fof(f8,axiom,(
% 3.72/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f40,plain,(
% 3.72/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f41,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f10,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f42,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f10])).
% 3.72/0.98  
% 3.72/0.98  fof(f11,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f43,plain,(
% 3.72/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f11])).
% 3.72/0.98  
% 3.72/0.98  fof(f12,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f44,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f12])).
% 3.72/0.98  
% 3.72/0.98  fof(f13,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f45,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f13])).
% 3.72/0.98  
% 3.72/0.98  fof(f14,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f46,plain,(
% 3.72/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f51,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f45,f46])).
% 3.72/0.98  
% 3.72/0.98  fof(f52,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f44,f51])).
% 3.72/0.98  
% 3.72/0.98  fof(f53,plain,(
% 3.72/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f43,f52])).
% 3.72/0.98  
% 3.72/0.98  fof(f54,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f42,f53])).
% 3.72/0.98  
% 3.72/0.98  fof(f55,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f41,f54])).
% 3.72/0.98  
% 3.72/0.98  fof(f56,plain,(
% 3.72/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f40,f55])).
% 3.72/0.98  
% 3.72/0.98  fof(f59,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f48,f56,f56])).
% 3.72/0.98  
% 3.72/0.98  fof(f15,axiom,(
% 3.72/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f23,plain,(
% 3.72/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.72/0.98    inference(ennf_transformation,[],[f15])).
% 3.72/0.98  
% 3.72/0.98  fof(f47,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f23])).
% 3.72/0.98  
% 3.72/0.98  fof(f58,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f47,f56])).
% 3.72/0.98  
% 3.72/0.98  fof(f17,conjecture,(
% 3.72/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f18,negated_conjecture,(
% 3.72/0.98    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.72/0.98    inference(negated_conjecture,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.72/0.98    inference(ennf_transformation,[],[f18])).
% 3.72/0.98  
% 3.72/0.98  fof(f30,plain,(
% 3.72/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.72/0.98    inference(nnf_transformation,[],[f25])).
% 3.72/0.98  
% 3.72/0.98  fof(f31,plain,(
% 3.72/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f32,plain,(
% 3.72/0.98    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f49,plain,(
% 3.72/0.98    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f32])).
% 3.72/0.98  
% 3.72/0.98  fof(f61,plain,(
% 3.72/0.98    ~r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK2),
% 3.72/0.98    inference(definition_unfolding,[],[f49,f37,f56])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f27])).
% 3.72/0.98  
% 3.72/0.98  fof(f50,plain,(
% 3.72/0.98    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f32])).
% 3.72/0.98  
% 3.72/0.98  fof(f60,plain,(
% 3.72/0.98    r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK2),
% 3.72/0.98    inference(definition_unfolding,[],[f50,f37,f56])).
% 3.72/0.98  
% 3.72/0.98  fof(f6,axiom,(
% 3.72/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f6])).
% 3.72/0.98  
% 3.72/0.98  cnf(c_102,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3,plain,
% 3.72/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_753,plain,
% 3.72/0.98      ( r2_hidden(arAF0_sK1_0,X0) | ~ iProver_ARSWP_24 | k1_xboole_0 = X0 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_3]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_894,plain,
% 3.72/0.98      ( k1_xboole_0 = X0
% 3.72/0.98      | r2_hidden(arAF0_sK1_0,X0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5,plain,
% 3.72/0.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_754,plain,
% 3.72/0.98      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1)
% 3.72/0.98      | ~ iProver_ARSWP_25 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_893,plain,
% 3.72/0.98      ( r1_xboole_0(k5_xboole_0(X0,arAF0_k3_xboole_0_0),X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.72/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_751,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | ~ r1_xboole_0(X1,X2)
% 3.72/0.98      | ~ iProver_ARSWP_22 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_896,plain,
% 3.72/0.98      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | r1_xboole_0(X1,X2) != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1165,plain,
% 3.72/0.98      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_893,c_896]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1247,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_894,c_1165]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,X1)
% 3.72/0.98      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_756,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,X1)
% 3.72/0.98      | ~ iProver_ARSWP_27
% 3.72/0.98      | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_891,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.72/0.98      | r2_hidden(X0,X1) != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1246,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | k1_xboole_0 = X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_894,c_891]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1487,plain,
% 3.72/0.98      ( X0 = X1
% 3.72/0.98      | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1246,c_1246]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4605,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.72/0.98      | arAF0_k3_xboole_0_0 != X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1487]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5015,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = X0
% 3.72/0.98      | k1_xboole_0 != X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1247,c_4605]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1503,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 != k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1246]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4047,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1247,c_1503]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4604,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 != X0
% 3.72/0.98      | arAF0_k3_xboole_0_0 = X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1487]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4824,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 = X0
% 3.72/0.98      | k1_xboole_0 != X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_4047,c_4604]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4603,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 != X0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1487]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4628,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4603,c_1487]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6,plain,
% 3.72/0.98      ( r2_hidden(X0,X1)
% 3.72/0.98      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_755,plain,
% 3.72/0.98      ( r2_hidden(X0,X1)
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,X1)
% 3.72/0.98      | ~ iProver_ARSWP_26 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_892,plain,
% 3.72/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9,negated_conjecture,
% 3.72/0.98      ( ~ r2_hidden(sK3,sK2)
% 3.72/0.98      | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_758,negated_conjecture,
% 3.72/0.98      ( ~ r2_hidden(sK3,sK2)
% 3.72/0.98      | ~ iProver_ARSWP_29
% 3.72/0.98      | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_889,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r2_hidden(sK3,sK2) != iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1359,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_892,c_889]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4669,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_4628,c_1359]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_752,plain,
% 3.72/0.98      ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | r1_xboole_0(X0,X1)
% 3.72/0.98      | ~ iProver_ARSWP_23 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_895,plain,
% 3.72/0.98      ( r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1395,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_895,c_891]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3639,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1395,c_896]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_8,negated_conjecture,
% 3.72/0.98      ( r2_hidden(sK3,sK2)
% 3.72/0.98      | k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_757,negated_conjecture,
% 3.72/0.98      ( r2_hidden(sK3,sK2)
% 3.72/0.98      | ~ iProver_ARSWP_28
% 3.72/0.98      | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) != sK2 ),
% 3.72/0.98      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_890,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) != sK2
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1497,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,k1_xboole_0) != sK2
% 3.72/0.98      | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1246,c_890]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4,plain,
% 3.72/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1756,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | sK2 != sK2
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_1497,c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1757,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_resolution_simp,[status(thm)],[c_1756]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2431,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1757,c_891]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1973,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1359,c_896]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2061,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_892,c_1973]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2757,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2431,c_2061]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1504,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 != k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1246]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2063,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | arAF0_k3_xboole_0_0 = k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_894,c_1973]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_114,plain,
% 3.72/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.72/0.98      theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1138,plain,
% 3.72/0.98      ( r1_xboole_0(X0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | ~ r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | X0 != arAF0_k6_enumset1_0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2409,plain,
% 3.72/0.98      ( ~ r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0)
% 3.72/0.98      | arAF0_k3_xboole_0_0 != arAF0_k6_enumset1_0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1138]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2410,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 != arAF0_k6_enumset1_0
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_112,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1109,plain,
% 3.72/0.98      ( X0 != X1 | arAF0_k3_xboole_0_0 != X1 | arAF0_k3_xboole_0_0 = X0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_112]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1151,plain,
% 3.72/0.98      ( X0 != arAF0_k3_xboole_0_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 = X0
% 3.72/0.98      | arAF0_k3_xboole_0_0 != arAF0_k3_xboole_0_0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1109]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1152,plain,
% 3.72/0.98      ( X0 != arAF0_k3_xboole_0_0 | arAF0_k3_xboole_0_0 = X0 ),
% 3.72/0.98      inference(equality_resolution_simp,[status(thm)],[c_1151]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2531,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 != arAF0_k3_xboole_0_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1152]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3483,plain,
% 3.72/0.98      ( iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2757,c_1504,c_2061,c_2063,c_2410,c_2531]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3484,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_3483]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1659,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,k1_xboole_0) != sK2
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1247,c_890]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1666,plain,
% 3.72/0.98      ( sK2 != sK2
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_1659,c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1667,plain,
% 3.72/0.98      ( r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(equality_resolution_simp,[status(thm)],[c_1666]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2127,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1667,c_891]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3329,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_2127,c_1247,c_1504]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3127,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 3.72/0.98      | r2_hidden(sK3,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2063,c_890]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1358,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r1_xboole_0(arAF0_k6_enumset1_0,X0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_892,c_891]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2976,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1358,c_896]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2758,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(arAF0_k3_xboole_0_0,sK2) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2431,c_1359]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1394,plain,
% 3.72/0.98      ( r2_hidden(X0,arAF0_k3_xboole_0_0) != iProver_top
% 3.72/0.98      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_895,c_896]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2578,plain,
% 3.72/0.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 3.72/0.98      | r2_hidden(arAF0_sK0_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_894,c_1394]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2128,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1667,c_889]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2291,plain,
% 3.72/0.98      ( r1_xboole_0(sK2,X0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_28 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2128,c_893]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2062,plain,
% 3.72/0.98      ( k5_xboole_0(sK2,arAF0_k3_xboole_0_0) = sK2
% 3.72/0.98      | r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_29 != iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_895,c_1973]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1658,plain,
% 3.72/0.98      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1247,c_893]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1677,plain,
% 3.72/0.98      ( r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_1658,c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1657,plain,
% 3.72/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1247,c_1165]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1496,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1246,c_893]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1768,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_1496,c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1502,plain,
% 3.72/0.98      ( arAF0_k6_enumset1_0 != k1_xboole_0
% 3.72/0.98      | arAF0_k3_xboole_0_0 = k1_xboole_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(equality_factoring,[status(thm)],[c_1246]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1488,plain,
% 3.72/0.98      ( k5_xboole_0(X0,X1) = X0
% 3.72/0.98      | arAF0_k6_enumset1_0 = arAF0_k3_xboole_0_0
% 3.72/0.98      | iProver_ARSWP_27 != iProver_top
% 3.72/0.98      | iProver_ARSWP_24 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1246,c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1396,plain,
% 3.72/0.98      ( r1_xboole_0(X0,X1) = iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_23 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_895,c_1165]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1360,plain,
% 3.72/0.98      ( r1_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = iProver_top
% 3.72/0.98      | iProver_ARSWP_26 != iProver_top
% 3.72/0.98      | iProver_ARSWP_25 != iProver_top
% 3.72/0.98      | iProver_ARSWP_22 != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_892,c_1165]) ).
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS output end Saturation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  ------                               Statistics
% 3.72/0.98  
% 3.72/0.98  ------ Selected
% 3.72/0.98  
% 3.72/0.98  total_time:                             0.185
% 3.72/0.98  
%------------------------------------------------------------------------------
