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
% DateTime   : Thu Dec  3 11:29:50 EST 2020

% Result     : CounterSatisfiable 11.69s
% Output     : Saturation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  276 (17460 expanded)
%              Number of clauses        :  221 (4230 expanded)
%              Number of leaves         :   24 (5047 expanded)
%              Depth                    :   18
%              Number of atoms          :  964 (30636 expanded)
%              Number of equality atoms :  914 (29677 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f63,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f60])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f44,f37,f61,f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f45,f57,f49,f58])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X6,X7),k3_xboole_0(k1_enumset1(X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f46,f57,f58,f49])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f31])).

fof(f55,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f55,f61,f61,f61])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_57,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_56,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_50,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1234,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1344,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1239,plain,
    ( ~ iProver_ARSWP_31
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1339,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_1856,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | arAF0_k1_enumset1_0 != X1
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1339])).

cnf(c_1909,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1856,c_1339])).

cnf(c_1928,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1909])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1235,plain,
    ( ~ iProver_ARSWP_27
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1343,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_3330,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1928,c_1343])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4316,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3330,c_7])).

cnf(c_7425,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4316])).

cnf(c_7455,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7425,c_4316])).

cnf(c_1613,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1343])).

cnf(c_3328,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1928,c_1613])).

cnf(c_23379,plain,
    ( X0 = X1
    | k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_3328])).

cnf(c_24755,plain,
    ( X0 = X1
    | k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_23379])).

cnf(c_26475,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_24755])).

cnf(c_32355,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_26475])).

cnf(c_32865,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_32355])).

cnf(c_25271,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_23379])).

cnf(c_31069,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_25271])).

cnf(c_32587,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_31069])).

cnf(c_23900,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3328])).

cnf(c_30807,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_23900])).

cnf(c_32412,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_30807])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X6,X7),k3_xboole_0(k1_enumset1(X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1240,plain,
    ( ~ iProver_ARSWP_32
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1338,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1932,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1338])).

cnf(c_3664,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1932])).

cnf(c_4057,plain,
    ( X0 = X1
    | arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3664,c_7])).

cnf(c_5483,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4057])).

cnf(c_5513,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5483,c_4057])).

cnf(c_3762,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1932])).

cnf(c_27991,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_3762])).

cnf(c_31376,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_27991])).

cnf(c_31641,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_31376])).

cnf(c_31707,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_31641])).

cnf(c_3761,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1932])).

cnf(c_27602,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_3761])).

cnf(c_31132,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_27602])).

cnf(c_1984,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1909])).

cnf(c_18299,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1984])).

cnf(c_18728,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_18299])).

cnf(c_23948,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_18728])).

cnf(c_1982,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1909])).

cnf(c_2002,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1982,c_1909])).

cnf(c_29004,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23948,c_2002])).

cnf(c_29245,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_29004,c_1338])).

cnf(c_29196,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_29004,c_23948])).

cnf(c_29001,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_23948])).

cnf(c_3426,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1928])).

cnf(c_27194,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_3426])).

cnf(c_28575,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_27194])).

cnf(c_18727,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_18299])).

cnf(c_21563,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_18727])).

cnf(c_28233,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21563,c_2002])).

cnf(c_28326,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28233,c_1343])).

cnf(c_28285,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28233,c_3426])).

cnf(c_28280,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28233,c_21563])).

cnf(c_28230,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_21563])).

cnf(c_14,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1241,negated_conjecture,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_14])).

cnf(c_1337,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_1931,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1909])).

cnf(c_2265,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1931,c_7])).

cnf(c_2597,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2265])).

cnf(c_2622,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2597,c_2265])).

cnf(c_3327,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1928])).

cnf(c_4754,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3327])).

cnf(c_4784,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4754,c_3327])).

cnf(c_27600,plain,
    ( arAF0_k1_enumset1_0 != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4784,c_3761])).

cnf(c_2009,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2002])).

cnf(c_3461,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1239,c_2009])).

cnf(c_64,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_63,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1524,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_64,c_63])).

cnf(c_6609,plain,
    ( ~ iProver_ARSWP_31
    | arAF0_k1_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
    inference(resolution,[status(thm)],[c_3461,c_1524])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1522,plain,
    ( X0 != X1
    | k5_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_64,c_6])).

cnf(c_1658,plain,
    ( X0 != X1
    | X2 != X0
    | k5_xboole_0(X1,k1_xboole_0) = X2 ),
    inference(resolution,[status(thm)],[c_1522,c_64])).

cnf(c_15352,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0 ),
    inference(resolution,[status(thm)],[c_6609,c_1658])).

cnf(c_15353,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15352])).

cnf(c_1525,plain,
    ( ~ iProver_ARSWP_26
    | X0 != arAF0_k1_enumset1_0
    | arAF0_k6_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_64,c_1234])).

cnf(c_7042,plain,
    ( ~ iProver_ARSWP_31
    | ~ iProver_ARSWP_26
    | arAF0_k6_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
    inference(resolution,[status(thm)],[c_1525,c_3461])).

cnf(c_16426,plain,
    ( ~ iProver_ARSWP_31
    | ~ iProver_ARSWP_26
    | X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | arAF0_k6_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_7042,c_64])).

cnf(c_16435,plain,
    ( X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16426])).

cnf(c_6611,plain,
    ( ~ iProver_ARSWP_31
    | X0 != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0 ),
    inference(resolution,[status(thm)],[c_3461,c_64])).

cnf(c_1640,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1524,c_6])).

cnf(c_3504,plain,
    ( X0 = X1
    | X1 != k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1640,c_64])).

cnf(c_19513,plain,
    ( ~ iProver_ARSWP_31
    | X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0 ),
    inference(resolution,[status(thm)],[c_6611,c_3504])).

cnf(c_19514,plain,
    ( X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19513])).

cnf(c_27774,plain,
    ( arAF0_k1_enumset1_0 != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27600,c_1984,c_15353,c_16435,c_19514])).

cnf(c_27785,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_27774])).

cnf(c_27193,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_3426])).

cnf(c_3425,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1928])).

cnf(c_27046,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_3425])).

cnf(c_27045,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_3425])).

cnf(c_18730,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_18299])).

cnf(c_1983,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1909])).

cnf(c_26623,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_18730,c_1983])).

cnf(c_27003,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_26623])).

cnf(c_27002,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_26623])).

cnf(c_26618,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_18730])).

cnf(c_26871,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_26618,c_1343])).

cnf(c_26862,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_26618])).

cnf(c_26861,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_26618])).

cnf(c_8635,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_1338])).

cnf(c_26622,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_18730,c_8635])).

cnf(c_26473,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_24755])).

cnf(c_26503,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_26473,c_24755])).

cnf(c_26474,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_24755])).

cnf(c_3424,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1928])).

cnf(c_3449,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3424,c_1928])).

cnf(c_25689,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_3449])).

cnf(c_25688,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_3449])).

cnf(c_2648,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1344])).

cnf(c_3324,plain,
    ( X0 = X1
    | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_1928])).

cnf(c_15245,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3324])).

cnf(c_22842,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_15245])).

cnf(c_25337,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_22842])).

cnf(c_25269,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_23379])).

cnf(c_25299,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25269,c_23379])).

cnf(c_25270,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_23379])).

cnf(c_23898,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3328])).

cnf(c_23928,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23898,c_3328])).

cnf(c_23899,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3328])).

cnf(c_22841,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_15245])).

cnf(c_8741,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_1343])).

cnf(c_19329,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_8741])).

cnf(c_21540,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_19329])).

cnf(c_17761,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_8635])).

cnf(c_20954,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_17761])).

cnf(c_20929,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_8635])).

cnf(c_18298,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1984])).

cnf(c_18720,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_18298])).

cnf(c_19791,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_18720])).

cnf(c_19827,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_19791])).

cnf(c_19792,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_18720])).

cnf(c_16762,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1983])).

cnf(c_16787,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_16762])).

cnf(c_17177,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16787])).

cnf(c_16788,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16762])).

cnf(c_4756,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3327])).

cnf(c_5535,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_4756])).

cnf(c_9255,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5535])).

cnf(c_11928,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_9255])).

cnf(c_14321,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_11928])).

cnf(c_5534,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_4756])).

cnf(c_9019,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5534])).

cnf(c_11520,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_9019])).

cnf(c_14289,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_11520])).

cnf(c_1614,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1343])).

cnf(c_3666,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_1614])).

cnf(c_6932,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3666])).

cnf(c_11145,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_6932])).

cnf(c_13881,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11145])).

cnf(c_2647,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1338])).

cnf(c_12428,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_2647])).

cnf(c_13088,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_12428])).

cnf(c_2646,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1343])).

cnf(c_11971,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_2646])).

cnf(c_6931,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3666])).

cnf(c_10825,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_6931])).

cnf(c_10836,plain,
    ( arAF0_k1_enumset1_0 != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_10825,c_6])).

cnf(c_2598,plain,
    ( arAF0_k1_enumset1_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2265])).

cnf(c_7427,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4316])).

cnf(c_11187,plain,
    ( iProver_ARSWP_33 != iProver_top
    | arAF0_k6_enumset1_0 = X0
    | arAF0_k1_enumset1_0 != X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10836,c_2598,c_7427])).

cnf(c_11188,plain,
    ( arAF0_k1_enumset1_0 != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_11187])).

cnf(c_10823,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
    | arAF0_k6_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_6931])).

cnf(c_4813,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_4784])).

cnf(c_1503,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1338])).

cnf(c_2125,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1503])).

cnf(c_3236,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_2125])).

cnf(c_8294,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4813,c_3236])).

cnf(c_9554,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_8294,c_3236])).

cnf(c_8733,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_1613])).

cnf(c_8631,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_1503])).

cnf(c_4755,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3327])).

cnf(c_5094,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_4755])).

cnf(c_8339,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_5094])).

cnf(c_8291,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_4813])).

cnf(c_7426,plain,
    ( arAF0_k6_enumset1_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4316])).

cnf(c_6930,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3666])).

cnf(c_6965,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6930,c_3666])).

cnf(c_3036,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1613])).

cnf(c_3801,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_3036])).

cnf(c_6740,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_3801])).

cnf(c_3240,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_1614])).

cnf(c_6474,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_3240])).

cnf(c_6445,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_3236])).

cnf(c_4816,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4784,c_3036])).

cnf(c_6132,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4816,c_1614])).

cnf(c_6124,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_4816])).

cnf(c_5485,plain,
    ( arAF0_k6_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4057])).

cnf(c_5484,plain,
    ( arAF0_k6_enumset1_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4057])).

cnf(c_5095,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_4755])).

cnf(c_5109,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5095,c_6])).

cnf(c_3760,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1932])).

cnf(c_3785,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3760,c_1932])).

cnf(c_2873,plain,
    ( arAF0_k6_enumset1_0 != X0
    | k1_xboole_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_2598])).

cnf(c_2644,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_1614])).

cnf(c_2677,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2644,c_6])).

cnf(c_2599,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2265])).

cnf(c_4814,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_4784])).

cnf(c_4844,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4814,c_6])).

cnf(c_1645,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1524,c_1234])).

cnf(c_1646,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_5137,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4844,c_1646])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f56])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.69/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/1.99  
% 11.69/1.99  ------  iProver source info
% 11.69/1.99  
% 11.69/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.69/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/1.99  git: non_committed_changes: false
% 11.69/1.99  git: last_make_outside_of_git: false
% 11.69/1.99  
% 11.69/1.99  ------ 
% 11.69/1.99  ------ Parsing...
% 11.69/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  ------ Proving...
% 11.69/1.99  ------ Problem Properties 
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  clauses                                 12
% 11.69/1.99  conjectures                             2
% 11.69/1.99  EPR                                     1
% 11.69/1.99  Horn                                    11
% 11.69/1.99  unary                                   11
% 11.69/1.99  binary                                  0
% 11.69/1.99  lits                                    14
% 11.69/1.99  lits eq                                 14
% 11.69/1.99  fd_pure                                 0
% 11.69/1.99  fd_pseudo                               0
% 11.69/1.99  fd_cond                                 0
% 11.69/1.99  fd_pseudo_cond                          1
% 11.69/1.99  AC symbols                              0
% 11.69/1.99  
% 11.69/1.99  ------ Input Options Time Limit: Unbounded
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 11.69/1.99  Current options:
% 11.69/1.99  ------ 
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.69/1.99  
% 11.69/1.99  ------ Proving...
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  % SZS status CounterSatisfiable for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  % SZS output start Saturation for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  fof(f4,axiom,(
% 11.69/1.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f36,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 11.69/1.99    inference(cnf_transformation,[],[f4])).
% 11.69/1.99  
% 11.69/1.99  fof(f3,axiom,(
% 11.69/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f25,plain,(
% 11.69/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.69/1.99    inference(rectify,[],[f3])).
% 11.69/1.99  
% 11.69/1.99  fof(f26,plain,(
% 11.69/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.69/1.99    inference(ennf_transformation,[],[f25])).
% 11.69/1.99  
% 11.69/1.99  fof(f29,plain,(
% 11.69/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.69/1.99    introduced(choice_axiom,[])).
% 11.69/1.99  
% 11.69/1.99  fof(f30,plain,(
% 11.69/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.69/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).
% 11.69/1.99  
% 11.69/1.99  fof(f34,plain,(
% 11.69/1.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f30])).
% 11.69/1.99  
% 11.69/1.99  fof(f35,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.69/1.99    inference(cnf_transformation,[],[f30])).
% 11.69/1.99  
% 11.69/1.99  fof(f18,axiom,(
% 11.69/1.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f50,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f18])).
% 11.69/1.99  
% 11.69/1.99  fof(f19,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f51,plain,(
% 11.69/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f19])).
% 11.69/1.99  
% 11.69/1.99  fof(f20,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f52,plain,(
% 11.69/1.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f20])).
% 11.69/1.99  
% 11.69/1.99  fof(f21,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f53,plain,(
% 11.69/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f21])).
% 11.69/1.99  
% 11.69/1.99  fof(f22,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f54,plain,(
% 11.69/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f22])).
% 11.69/1.99  
% 11.69/1.99  fof(f58,plain,(
% 11.69/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f53,f54])).
% 11.69/1.99  
% 11.69/1.99  fof(f59,plain,(
% 11.69/1.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f52,f58])).
% 11.69/1.99  
% 11.69/1.99  fof(f60,plain,(
% 11.69/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f51,f59])).
% 11.69/1.99  
% 11.69/1.99  fof(f63,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f50,f60])).
% 11.69/1.99  
% 11.69/1.99  fof(f12,axiom,(
% 11.69/1.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f27,plain,(
% 11.69/1.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 11.69/1.99    inference(ennf_transformation,[],[f12])).
% 11.69/1.99  
% 11.69/1.99  fof(f44,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 11.69/1.99    inference(cnf_transformation,[],[f27])).
% 11.69/1.99  
% 11.69/1.99  fof(f5,axiom,(
% 11.69/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f37,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f5])).
% 11.69/1.99  
% 11.69/1.99  fof(f16,axiom,(
% 11.69/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f48,plain,(
% 11.69/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f16])).
% 11.69/1.99  
% 11.69/1.99  fof(f61,plain,(
% 11.69/1.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f48,f49])).
% 11.69/1.99  
% 11.69/1.99  fof(f17,axiom,(
% 11.69/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f49,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f17])).
% 11.69/1.99  
% 11.69/1.99  fof(f67,plain,(
% 11.69/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 11.69/1.99    inference(definition_unfolding,[],[f44,f37,f61,f49])).
% 11.69/1.99  
% 11.69/1.99  fof(f13,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f45,plain,(
% 11.69/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f13])).
% 11.69/1.99  
% 11.69/1.99  fof(f8,axiom,(
% 11.69/1.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f40,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f8])).
% 11.69/1.99  
% 11.69/1.99  fof(f57,plain,(
% 11.69/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f40,f37])).
% 11.69/1.99  
% 11.69/1.99  fof(f64,plain,(
% 11.69/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f45,f57,f49,f58])).
% 11.69/1.99  
% 11.69/1.99  fof(f7,axiom,(
% 11.69/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f39,plain,(
% 11.69/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.69/1.99    inference(cnf_transformation,[],[f7])).
% 11.69/1.99  
% 11.69/1.99  fof(f14,axiom,(
% 11.69/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f46,plain,(
% 11.69/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.69/1.99    inference(cnf_transformation,[],[f14])).
% 11.69/1.99  
% 11.69/1.99  fof(f68,plain,(
% 11.69/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X6,X7),k3_xboole_0(k1_enumset1(X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 11.69/1.99    inference(definition_unfolding,[],[f46,f57,f58,f49])).
% 11.69/1.99  
% 11.69/1.99  fof(f23,conjecture,(
% 11.69/1.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f24,negated_conjecture,(
% 11.69/1.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 11.69/1.99    inference(negated_conjecture,[],[f23])).
% 11.69/1.99  
% 11.69/1.99  fof(f28,plain,(
% 11.69/1.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 11.69/1.99    inference(ennf_transformation,[],[f24])).
% 11.69/1.99  
% 11.69/1.99  fof(f31,plain,(
% 11.69/1.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 11.69/1.99    introduced(choice_axiom,[])).
% 11.69/1.99  
% 11.69/1.99  fof(f32,plain,(
% 11.69/1.99    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 11.69/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f31])).
% 11.69/1.99  
% 11.69/1.99  fof(f55,plain,(
% 11.69/1.99    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  fof(f70,plain,(
% 11.69/1.99    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 11.69/1.99    inference(definition_unfolding,[],[f55,f61,f61,f61])).
% 11.69/1.99  
% 11.69/1.99  fof(f6,axiom,(
% 11.69/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.69/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/1.99  
% 11.69/1.99  fof(f38,plain,(
% 11.69/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.69/1.99    inference(cnf_transformation,[],[f6])).
% 11.69/1.99  
% 11.69/1.99  fof(f56,plain,(
% 11.69/1.99    sK1 != sK2),
% 11.69/1.99    inference(cnf_transformation,[],[f32])).
% 11.69/1.99  
% 11.69/1.99  cnf(c_57,plain,
% 11.69/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.69/1.99      theory(equality) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_56,plain,
% 11.69/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.69/1.99      theory(equality) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_50,plain,( X0_2 = X0_2 ),theory(equality) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5,plain,
% 11.69/1.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 11.69/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4,plain,
% 11.69/1.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 11.69/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3,plain,
% 11.69/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_0,plain,
% 11.69/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1234,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_26 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1344,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1234]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_10,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | X2 = X1
% 11.69/1.99      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 11.69/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1239,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | X0 = X1
% 11.69/1.99      | X2 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1339,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | X2 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1239]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1856,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X1
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1339]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1909,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_1856,c_1339]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1928,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1,plain,
% 11.69/1.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X1)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 11.69/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1235,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_27
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 11.69/1.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1343,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3330,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1928,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7,plain,
% 11.69/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.69/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4316,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_3330,c_7]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7425,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4316]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7455,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_7425,c_4316]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1613,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3328,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1928,c_1613]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23379,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_3328]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_24755,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_23379]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26475,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_24755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_32355,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_26475]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_32865,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_32355]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25271,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_23379]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_31069,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_25271]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_32587,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_31069]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23900,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3328]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_30807,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_23900]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_32412,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_30807]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11,plain,
% 11.69/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X6,X7),k3_xboole_0(k1_enumset1(X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 11.69/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1240,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_32
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 11.69/1.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1338,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1932,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1909,c_1338]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3664,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_1932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4057,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_3664,c_7]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5483,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4057]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5513,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_5483,c_4057]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3762,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27991,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_3762]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_31376,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_27991]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_31641,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_31376]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_31707,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_31641]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3761,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27602,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_3761]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_31132,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_27602]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1984,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18299,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_1984]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18728,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_18299]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23948,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_18728]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1982,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2002,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_1982,c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_29004,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_23948,c_2002]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_29245,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_29004,c_1338]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_29196,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_29004,c_23948]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_29001,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_23948]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3426,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27194,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_3426]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28575,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_27194]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18727,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_18299]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_21563,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_18727]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28233,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_21563,c_2002]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28326,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_28233,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28285,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_28233,c_3426]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28280,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_28233,c_21563]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_28230,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_21563]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_14,negated_conjecture,
% 11.69/1.99      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 11.69/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1241,negated_conjecture,
% 11.69/1.99      ( ~ iProver_ARSWP_33 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(arg_filter_abstr,[status(unp)],[c_14]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1337,plain,
% 11.69/1.99      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1931,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2265,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | arAF0_k1_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_1931,c_7]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2597,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_2265]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2622,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_2597,c_2265]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3327,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4754,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3327]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4784,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_4754,c_3327]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27600,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_4784,c_3761]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2009,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2002]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3461,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(global_propositional_subsumption,[status(thm)],[c_1239,c_2009]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_64,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_63,plain,( X0 = X0 ),theory(equality) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1524,plain,
% 11.69/1.99      ( X0 != X1 | X1 = X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_64,c_63]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6609,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | arAF0_k1_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_3461,c_1524]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6,plain,
% 11.69/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.69/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1522,plain,
% 11.69/1.99      ( X0 != X1 | k5_xboole_0(X1,k1_xboole_0) = X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_64,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1658,plain,
% 11.69/1.99      ( X0 != X1 | X2 != X0 | k5_xboole_0(X1,k1_xboole_0) = X2 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_1522,c_64]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_15352,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_6609,c_1658]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_15353,plain,
% 11.69/1.99      ( k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_15352]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1525,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_26
% 11.69/1.99      | X0 != arAF0_k1_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_64,c_1234]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7042,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | ~ iProver_ARSWP_26
% 11.69/1.99      | arAF0_k6_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_1525,c_3461]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16426,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | ~ iProver_ARSWP_26
% 11.69/1.99      | X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_7042,c_64]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16435,plain,
% 11.69/1.99      ( X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_16426]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6611,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | X0 != arAF0_k1_enumset1_0
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_3461,c_64]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1640,plain,
% 11.69/1.99      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_1524,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3504,plain,
% 11.69/1.99      ( X0 = X1 | X1 != k5_xboole_0(X0,k1_xboole_0) ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_1640,c_64]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19513,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_31
% 11.69/1.99      | X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 11.69/1.99      | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_6611,c_3504]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19514,plain,
% 11.69/1.99      ( X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 11.69/1.99      | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_19513]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27774,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(global_propositional_subsumption,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_27600,c_1984,c_15353,c_16435,c_19514]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27785,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_27774]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27193,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_3426]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3425,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27046,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_3425]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27045,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_3425]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18730,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_18299]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1983,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1909]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26623,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_18730,c_1983]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27003,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_26623]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_27002,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_26623]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26618,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_18730]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26871,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_26618,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26862,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_26618]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26861,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_26618]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8635,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_1338]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26622,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_18730,c_8635]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26473,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_24755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26503,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_26473,c_24755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_26474,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_24755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3424,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3449,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_3424,c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25689,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_3449]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25688,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_3449]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2648,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1344]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3324,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_1928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_15245,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3324]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_22842,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_15245]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25337,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_22842]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25269,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_23379]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25299,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_25269,c_23379]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_25270,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_23379]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23898,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3328]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23928,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_23898,c_3328]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_23899,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3328]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_22841,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_15245]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8741,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19329,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_8741]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_21540,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_19329]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_17761,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_8635]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_20954,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_17761]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_20929,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2002,c_8635]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18298,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1984]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_18720,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_18298]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19791,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_18720]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19827,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_19791]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_19792,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_18720]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16762,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1983]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16787,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_16762]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_17177,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_16787]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_16788,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_16762]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4756,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3327]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5535,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_4756]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_9255,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_5535]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11928,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_9255]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_14321,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_11928]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5534,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_4756]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_9019,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_5534]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11520,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_9019]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_14289,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_11520]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1614,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3666,plain,
% 11.69/1.99      ( X0 = X1
% 11.69/1.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1932,c_1614]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6932,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3666]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11145,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_6932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_13881,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_resolution,[status(thm)],[c_11145]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2647,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1338]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_12428,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_2647]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_13088,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_12428]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2646,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1343]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11971,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_2646]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6931,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3666]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_10825,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_6931]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_10836,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_10825,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2598,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | k1_xboole_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_2265]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7427,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4316]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11187,plain,
% 11.69/1.99      ( iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(global_propositional_subsumption,
% 11.69/1.99                [status(thm)],
% 11.69/1.99                [c_10836,c_2598,c_7427]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_11188,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(renaming,[status(thm)],[c_11187]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_10823,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
% 11.69/1.99      | arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_6931]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4813,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_4784]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1503,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_1338]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2125,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_1503]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3236,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_2125]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8294,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_4813,c_3236]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_9554,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_8294,c_3236]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8733,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_7455,c_1613]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8631,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_5513,c_1503]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4755,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3327]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5094,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_4755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8339,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_5094]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_8291,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_4813]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_7426,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | k1_xboole_0 = X0
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4316]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6930,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_3666]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6965,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_6930,c_3666]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3036,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1337,c_1613]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3801,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_3036]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6740,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_3801]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3240,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_1614]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6474,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_3240]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6445,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_3236]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4816,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_4784,c_3036]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6132,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_4816,c_1614]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_6124,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2648,c_4816]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5485,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4057]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5484,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | k1_xboole_0 = X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_4057]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5095,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) != X0
% 11.69/1.99      | arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_4755]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5109,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_5095,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3760,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_1932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_3785,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_32 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_3760,c_1932]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2873,plain,
% 11.69/1.99      ( arAF0_k6_enumset1_0 != X0
% 11.69/1.99      | k1_xboole_0 = X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_1344,c_2598]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2644,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_1614]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2677,plain,
% 11.69/1.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_27 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_2644,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_2599,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = X0
% 11.69/1.99      | k1_xboole_0 != X0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top ),
% 11.69/1.99      inference(equality_factoring,[status(thm)],[c_2265]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4814,plain,
% 11.69/1.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) = arAF0_k1_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(superposition,[status(thm)],[c_2622,c_4784]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_4844,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_33 != iProver_top
% 11.69/1.99      | iProver_ARSWP_31 != iProver_top
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(demodulation,[status(thm)],[c_4814,c_6]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1645,plain,
% 11.69/1.99      ( ~ iProver_ARSWP_26 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 11.69/1.99      inference(resolution,[status(thm)],[c_1524,c_1234]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_1646,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_5137,plain,
% 11.69/1.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 11.69/1.99      | iProver_ARSWP_26 != iProver_top ),
% 11.69/1.99      inference(global_propositional_subsumption,[status(thm)],[c_4844,c_1646]) ).
% 11.69/1.99  
% 11.69/1.99  cnf(c_13,negated_conjecture,
% 11.69/1.99      ( sK1 != sK2 ),
% 11.69/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.69/1.99  
% 11.69/1.99  
% 11.69/1.99  % SZS output end Saturation for theBenchmark.p
% 11.69/1.99  
% 11.69/1.99  ------                               Statistics
% 11.69/1.99  
% 11.69/1.99  ------ Selected
% 11.69/1.99  
% 11.69/1.99  total_time:                             1.148
% 11.69/1.99  
%------------------------------------------------------------------------------
