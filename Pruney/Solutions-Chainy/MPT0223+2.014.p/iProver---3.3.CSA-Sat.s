%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:46 EST 2020

% Result     : CounterSatisfiable 3.69s
% Output     : Saturation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  157 (5040 expanded)
%              Number of clauses        :  100 (1256 expanded)
%              Number of leaves         :   25 (1458 expanded)
%              Depth                    :   21
%              Number of atoms          :  406 (8372 expanded)
%              Number of equality atoms :  363 (8041 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f30])).

fof(f53,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f66,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f53,f56,f56,f56])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f44,f55,f56,f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f37,f56,f47])).

fof(f54,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f45,f55,f52,f56])).

cnf(c_56,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_49,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1396,negated_conjecture,
    ( ~ iProver_ARSWP_32
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1485,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1390,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1491,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1391,plain,
    ( ~ iProver_ARSWP_27
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1490,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_2063,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1490])).

cnf(c_6548,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_2063])).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1394,plain,
    ( ~ iProver_ARSWP_30
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1487,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1557,plain,
    ( ~ iProver_ARSWP_30
    | X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1558,plain,
    ( X0 = sK2
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_1560,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK1 = sK2
    | iProver_ARSWP_30 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_1879,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1487,c_12,c_1560])).

cnf(c_1885,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1879])).

cnf(c_4230,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1490])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4235,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4230,c_8])).

cnf(c_4271,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4235,c_1885])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1667,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_4346,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4271,c_1667])).

cnf(c_6543,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4346,c_2063])).

cnf(c_6495,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4346,c_1490])).

cnf(c_1886,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_1879])).

cnf(c_1897,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1886,c_8])).

cnf(c_1917,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1491])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1395,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1486,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_2095,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1486])).

cnf(c_2101,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2095,c_1667])).

cnf(c_1399,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_63,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1998,plain,
    ( X0 != X1
    | k5_xboole_0(X2,X3) != X1
    | k5_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_2031,plain,
    ( X0 != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_2966,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | arAF0_k6_enumset1_0 != arAF0_k1_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_3023,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2101,c_1399,c_1879,c_2966])).

cnf(c_3033,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_3023])).

cnf(c_4278,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4235,c_3033])).

cnf(c_4318,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4278,c_1667])).

cnf(c_5107,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4318,c_1879])).

cnf(c_5344,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5107,c_3])).

cnf(c_5100,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4318,c_1885])).

cnf(c_5143,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5100,c_8])).

cnf(c_3506,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_1490])).

cnf(c_4864,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3506,c_3])).

cnf(c_3037,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1486])).

cnf(c_3042,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3037,c_8])).

cnf(c_4221,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_1885])).

cnf(c_4258,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4221,c_1667])).

cnf(c_1773,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1486])).

cnf(c_4788,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4258,c_1773])).

cnf(c_4784,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_4258,c_1885])).

cnf(c_3082,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_1773])).

cnf(c_3134,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3082,c_1667])).

cnf(c_4223,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1885])).

cnf(c_4244,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4223,c_8])).

cnf(c_1916,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1486])).

cnf(c_1930,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1916,c_1667])).

cnf(c_2233,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1930])).

cnf(c_2259,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2233,c_1667])).

cnf(c_1697,plain,
    ( ~ iProver_ARSWP_32
    | X0 != arAF0_k1_enumset1_0
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(resolution,[status(thm)],[c_63,c_1396])).

cnf(c_1975,plain,
    ( ~ iProver_ARSWP_32
    | ~ iProver_ARSWP_26
    | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1697,c_1390])).

cnf(c_1976,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_2804,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_1976])).

cnf(c_2815,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_1879])).

cnf(c_3751,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_3])).

cnf(c_3504,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_3033])).

cnf(c_3253,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1486])).

cnf(c_3252,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1879])).

cnf(c_3247,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_3023])).

cnf(c_3034,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_3023])).

cnf(c_2864,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_1773])).

cnf(c_2816,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_1486])).

cnf(c_2062,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1490])).

cnf(c_2081,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2062,c_1667])).

cnf(c_2442,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_1490])).

cnf(c_2441,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_2081])).

cnf(c_2064,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_1490])).

cnf(c_1887,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1486])).

cnf(c_2478,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_2441])).

cnf(c_2498,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2478,c_1667])).

cnf(c_62,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1692,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_63,c_62])).

cnf(c_1796,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1692,c_1390])).

cnf(c_1797,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1796])).

cnf(c_2642,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_1797])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.69/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.98  
% 3.69/0.98  ------  iProver source info
% 3.69/0.98  
% 3.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.98  git: non_committed_changes: false
% 3.69/0.98  git: last_make_outside_of_git: false
% 3.69/0.98  
% 3.69/0.98  ------ 
% 3.69/0.98  ------ Parsing...
% 3.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  ------ Proving...
% 3.69/0.98  ------ Problem Properties 
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  clauses                                 11
% 3.69/0.98  conjectures                             2
% 3.69/0.98  EPR                                     1
% 3.69/0.98  Horn                                    10
% 3.69/0.98  unary                                   10
% 3.69/0.98  binary                                  0
% 3.69/0.98  lits                                    13
% 3.69/0.98  lits eq                                 13
% 3.69/0.98  fd_pure                                 0
% 3.69/0.98  fd_pseudo                               0
% 3.69/0.98  fd_cond                                 0
% 3.69/0.98  fd_pseudo_cond                          1
% 3.69/0.98  AC symbols                              0
% 3.69/0.98  
% 3.69/0.98  ------ Input Options Time Limit: Unbounded
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.69/0.98  Current options:
% 3.69/0.98  ------ 
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  % SZS output start Saturation for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  fof(f5,axiom,(
% 3.69/0.98    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f36,plain,(
% 3.69/0.98    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.69/0.98    inference(cnf_transformation,[],[f5])).
% 3.69/0.98  
% 3.69/0.98  fof(f4,axiom,(
% 3.69/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f24,plain,(
% 3.69/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.69/0.98    inference(rectify,[],[f4])).
% 3.69/0.98  
% 3.69/0.98  fof(f25,plain,(
% 3.69/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.69/0.98    inference(ennf_transformation,[],[f24])).
% 3.69/0.98  
% 3.69/0.98  fof(f28,plain,(
% 3.69/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.69/0.98    introduced(choice_axiom,[])).
% 3.69/0.98  
% 3.69/0.98  fof(f29,plain,(
% 3.69/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 3.69/0.98  
% 3.69/0.98  fof(f34,plain,(
% 3.69/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f29])).
% 3.69/0.98  
% 3.69/0.98  fof(f35,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.69/0.98    inference(cnf_transformation,[],[f29])).
% 3.69/0.98  
% 3.69/0.98  fof(f22,conjecture,(
% 3.69/0.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f23,negated_conjecture,(
% 3.69/0.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.69/0.98    inference(negated_conjecture,[],[f22])).
% 3.69/0.98  
% 3.69/0.98  fof(f27,plain,(
% 3.69/0.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.69/0.98    inference(ennf_transformation,[],[f23])).
% 3.69/0.98  
% 3.69/0.98  fof(f30,plain,(
% 3.69/0.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 3.69/0.98    introduced(choice_axiom,[])).
% 3.69/0.98  
% 3.69/0.98  fof(f31,plain,(
% 3.69/0.98    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f30])).
% 3.69/0.98  
% 3.69/0.98  fof(f53,plain,(
% 3.69/0.98    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 3.69/0.98    inference(cnf_transformation,[],[f31])).
% 3.69/0.98  
% 3.69/0.98  fof(f15,axiom,(
% 3.69/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f46,plain,(
% 3.69/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f15])).
% 3.69/0.98  
% 3.69/0.98  fof(f16,axiom,(
% 3.69/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f47,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f16])).
% 3.69/0.98  
% 3.69/0.98  fof(f56,plain,(
% 3.69/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f46,f47])).
% 3.69/0.98  
% 3.69/0.98  fof(f66,plain,(
% 3.69/0.98    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 3.69/0.98    inference(definition_unfolding,[],[f53,f56,f56,f56])).
% 3.69/0.98  
% 3.69/0.98  fof(f17,axiom,(
% 3.69/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f48,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f17])).
% 3.69/0.98  
% 3.69/0.98  fof(f18,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f49,plain,(
% 3.69/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f18])).
% 3.69/0.98  
% 3.69/0.98  fof(f19,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f50,plain,(
% 3.69/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f19])).
% 3.69/0.98  
% 3.69/0.98  fof(f20,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f51,plain,(
% 3.69/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f20])).
% 3.69/0.98  
% 3.69/0.98  fof(f21,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f52,plain,(
% 3.69/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f21])).
% 3.69/0.98  
% 3.69/0.98  fof(f57,plain,(
% 3.69/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f51,f52])).
% 3.69/0.98  
% 3.69/0.98  fof(f58,plain,(
% 3.69/0.98    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f50,f57])).
% 3.69/0.98  
% 3.69/0.98  fof(f59,plain,(
% 3.69/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f49,f58])).
% 3.69/0.98  
% 3.69/0.98  fof(f61,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f48,f59])).
% 3.69/0.98  
% 3.69/0.98  fof(f13,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f44,plain,(
% 3.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f13])).
% 3.69/0.98  
% 3.69/0.98  fof(f9,axiom,(
% 3.69/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f40,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f9])).
% 3.69/0.98  
% 3.69/0.98  fof(f6,axiom,(
% 3.69/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f37,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f6])).
% 3.69/0.98  
% 3.69/0.98  fof(f55,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f40,f37])).
% 3.69/0.98  
% 3.69/0.98  fof(f62,plain,(
% 3.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f44,f55,f56,f52])).
% 3.69/0.98  
% 3.69/0.98  fof(f12,axiom,(
% 3.69/0.98    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f26,plain,(
% 3.69/0.98    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 3.69/0.98    inference(ennf_transformation,[],[f12])).
% 3.69/0.98  
% 3.69/0.98  fof(f43,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 3.69/0.98    inference(cnf_transformation,[],[f26])).
% 3.69/0.98  
% 3.69/0.98  fof(f64,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 3.69/0.98    inference(definition_unfolding,[],[f43,f37,f56,f47])).
% 3.69/0.98  
% 3.69/0.98  fof(f54,plain,(
% 3.69/0.98    sK1 != sK2),
% 3.69/0.98    inference(cnf_transformation,[],[f31])).
% 3.69/0.98  
% 3.69/0.98  fof(f8,axiom,(
% 3.69/0.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f39,plain,(
% 3.69/0.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.69/0.98    inference(cnf_transformation,[],[f8])).
% 3.69/0.98  
% 3.69/0.98  fof(f7,axiom,(
% 3.69/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f38,plain,(
% 3.69/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.69/0.98    inference(cnf_transformation,[],[f7])).
% 3.69/0.98  
% 3.69/0.98  fof(f2,axiom,(
% 3.69/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f33,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f2])).
% 3.69/0.98  
% 3.69/0.98  fof(f14,axiom,(
% 3.69/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f45,plain,(
% 3.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f14])).
% 3.69/0.98  
% 3.69/0.98  fof(f65,plain,(
% 3.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f45,f55,f52,f56])).
% 3.69/0.98  
% 3.69/0.98  cnf(c_56,plain,
% 3.69/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/0.98      theory(equality) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_55,plain,
% 3.69/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/0.98      theory(equality) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_49,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_6,plain,
% 3.69/0.98      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.69/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_5,plain,
% 3.69/0.98      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.69/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_4,plain,
% 3.69/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.69/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_13,negated_conjecture,
% 3.69/0.98      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 3.69/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1396,negated_conjecture,
% 3.69/0.98      ( ~ iProver_ARSWP_32 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 3.69/0.98      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1485,plain,
% 3.69/0.98      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.69/0.98      | iProver_ARSWP_32 != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_0,plain,
% 3.69/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 3.69/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1390,plain,
% 3.69/0.98      ( ~ iProver_ARSWP_26 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 3.69/0.98      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1491,plain,
% 3.69/0.98      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.69/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1,plain,
% 3.69/0.98      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.69/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1391,plain,
% 3.69/0.98      ( ~ iProver_ARSWP_27
% 3.69/0.98      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.69/0.98      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1490,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.98      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2063,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.98      | iProver_ARSWP_27 != iProver_top
% 3.69/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1491,c_1490]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_6548,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.98      | iProver_ARSWP_32 != iProver_top
% 3.69/0.98      | iProver_ARSWP_27 != iProver_top
% 3.69/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1485,c_2063]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_10,plain,
% 3.69/0.98      ( X0 = X1
% 3.69/0.98      | X2 = X1
% 3.69/0.98      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 3.69/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1394,plain,
% 3.69/0.98      ( ~ iProver_ARSWP_30
% 3.69/0.98      | X0 = X1
% 3.69/0.98      | X2 = X1
% 3.69/0.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 3.69/0.98      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1487,plain,
% 3.69/0.98      ( X0 = X1
% 3.69/0.98      | X2 = X1
% 3.69/0.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12,negated_conjecture,
% 3.69/0.98      ( sK1 != sK2 ),
% 3.69/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1557,plain,
% 3.69/0.98      ( ~ iProver_ARSWP_30
% 3.69/0.98      | X0 = sK2
% 3.69/0.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | sK1 = sK2 ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_1394]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1558,plain,
% 3.69/0.98      ( X0 = sK2
% 3.69/0.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | sK1 = sK2
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1560,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | sK1 = sK2
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_1558]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1879,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.98      inference(global_propositional_subsumption,
% 3.69/0.98                [status(thm)],
% 3.69/0.98                [c_1487,c_12,c_1560]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1885,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top
% 3.69/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1491,c_1879]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_4230,plain,
% 3.69/0.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.98      | iProver_ARSWP_30 != iProver_top
% 3.69/0.98      | iProver_ARSWP_27 != iProver_top
% 3.69/0.98      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1885,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_8,plain,
% 3.69/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4235,plain,
% 3.69/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_4230,c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4271,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4235,c_1885]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7,plain,
% 3.69/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3,plain,
% 3.69/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1667,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4346,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_4271,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6543,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4346,c_2063]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6495,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4346,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1886,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1485,c_1879]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1897,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_1886,c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1917,plain,
% 3.69/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1897,c_1491]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_11,plain,
% 3.69/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.69/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1395,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_31
% 3.69/0.99      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 3.69/0.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1486,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2095,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1917,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2101,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_2095,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1399,plain,
% 3.69/0.99      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_63,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1998,plain,
% 3.69/0.99      ( X0 != X1 | k5_xboole_0(X2,X3) != X1 | k5_xboole_0(X2,X3) = X0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_63]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2031,plain,
% 3.69/0.99      ( X0 != arAF0_k1_enumset1_0
% 3.69/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 3.69/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1998]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2966,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
% 3.69/0.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | arAF0_k6_enumset1_0 != arAF0_k1_enumset1_0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3023,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2101,c_1399,c_1879,c_2966]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3033,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1491,c_3023]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4278,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4235,c_3033]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4318,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_4278,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5107,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4318,c_1879]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5344,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_5107,c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5100,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4318,c_1885]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5143,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_5100,c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3506,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3033,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4864,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3506,c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3037,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3023,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3042,plain,
% 3.69/0.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_3037,c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4221,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3042,c_1885]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4258,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_4221,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1773,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1491,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4788,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4258,c_1773]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4784,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4258,c_1885]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3082,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3042,c_1773]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3134,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_3082,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4223,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3134,c_1885]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4244,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_4223,c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1916,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1897,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1930,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_1916,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2233,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1917,c_1930]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2259,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_2233,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1697,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_32
% 3.69/0.99      | X0 != arAF0_k1_enumset1_0
% 3.69/0.99      | arAF0_k3_xboole_0_0 = X0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_63,c_1396]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1975,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_32
% 3.69/0.99      | ~ iProver_ARSWP_26
% 3.69/0.99      | arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_1697,c_1390]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1976,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2804,plain,
% 3.69/0.99      ( arAF0_k3_xboole_0_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2259,c_1976]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2815,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2804,c_1879]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3751,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2815,c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3504,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1485,c_3033]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3253,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3134,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3252,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3134,c_1879]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3247,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3134,c_3023]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3034,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2804,c_3023]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2864,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1485,c_1773]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2816,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2804,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2062,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1897,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2081,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_2062,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2442,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2081,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2441,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1485,c_2081]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2064,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1485,c_1490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1887,plain,
% 3.69/0.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_31 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1879,c_1486]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2478,plain,
% 3.69/0.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1917,c_2441]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2498,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_32 != iProver_top
% 3.69/0.99      | iProver_ARSWP_30 != iProver_top
% 3.69/0.99      | iProver_ARSWP_27 != iProver_top
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(demodulation,[status(thm)],[c_2478,c_1667]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_62,plain,( X0 = X0 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1692,plain,
% 3.69/0.99      ( X0 != X1 | X1 = X0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_63,c_62]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1796,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_26 | arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_1692,c_1390]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1797,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1796]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2642,plain,
% 3.69/0.99      ( arAF0_k1_enumset1_0 = arAF0_k6_enumset1_0
% 3.69/0.99      | iProver_ARSWP_26 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2498,c_1797]) ).
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS output end Saturation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  ------                               Statistics
% 3.69/0.99  
% 3.69/0.99  ------ Selected
% 3.69/0.99  
% 3.69/0.99  total_time:                             0.284
% 3.69/0.99  
%------------------------------------------------------------------------------
