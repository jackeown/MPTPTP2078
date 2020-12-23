%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:46 EST 2020

% Result     : CounterSatisfiable 19.33s
% Output     : Saturation 19.33s
% Verified   : 
% Statistics : Number of formulae       :  520 (98891 expanded)
%              Number of clauses        :  460 (27323 expanded)
%              Number of leaves         :   26 (28905 expanded)
%              Depth                    :   40
%              Number of atoms          : 2044 (166000 expanded)
%              Number of equality atoms : 1983 (162144 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
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
    inference(rectify,[],[f4])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f59])).

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

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f69,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f55,f61,f61,f61])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f47,f38,f61,f50])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k1_enumset1(X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f48,f57,f59])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f43,f57,f54])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f45,f57,f54,f60])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(definition_unfolding,[],[f44,f57,f58,f59,f60])).

cnf(c_59,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_58,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_52,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1404,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1516,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1411,negated_conjecture,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1509,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_13,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1410,plain,
    ( ~ iProver_ARSWP_32
    | X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1510,plain,
    ( X0 = X1
    | X2 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1410])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1929,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | k1_xboole_0 = X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_8])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_65,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_71,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_66,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_264,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_265,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1946,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = X0
    | sK1 != X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_14])).

cnf(c_2436,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = sK1
    | sK1 != sK1
    | iProver_ARSWP_32 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2534,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1929,c_14,c_71,c_265,c_2436])).

cnf(c_2541,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2534])).

cnf(c_2545,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2541,c_8])).

cnf(c_2565,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1516])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k1_enumset1(X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1405,plain,
    ( ~ iProver_ARSWP_27
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1515,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_2880,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_1515])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1663,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_3])).

cnf(c_2886,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2880,c_1663])).

cnf(c_1414,plain,
    ( arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_3044,plain,
    ( X0 != X1
    | k5_xboole_0(X2,X3) != X1
    | k5_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_4219,plain,
    ( X0 != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_3044])).

cnf(c_9812,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | arAF0_k5_enumset1_0 != arAF0_k1_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_4219])).

cnf(c_17756,plain,
    ( iProver_ARSWP_32 != iProver_top
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_1414,c_2534,c_9812])).

cnf(c_17757,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_17756])).

cnf(c_17774,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_17757])).

cnf(c_1765,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1515])).

cnf(c_19341,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_1765])).

cnf(c_19375,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_19341,c_8])).

cnf(c_2540,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2534])).

cnf(c_47237,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_2540])).

cnf(c_47365,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_47237,c_1663])).

cnf(c_1963,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1510])).

cnf(c_33888,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1963])).

cnf(c_72710,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_33888])).

cnf(c_1961,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1510])).

cnf(c_29958,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1961])).

cnf(c_71848,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_29958])).

cnf(c_19668,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_1765])).

cnf(c_19736,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_19668,c_1663])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1409,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1511,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_20355,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_1511])).

cnf(c_20368,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_20355,c_7,c_8])).

cnf(c_20604,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_20368])).

cnf(c_20729,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_20604,c_8])).

cnf(c_19345,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_1511])).

cnf(c_23675,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20729,c_19345])).

cnf(c_23747,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23675,c_1663])).

cnf(c_23664,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_19345])).

cnf(c_23774,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23664,c_8])).

cnf(c_27300,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23747,c_23774])).

cnf(c_27481,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_27300])).

cnf(c_27594,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_27481,c_1663])).

cnf(c_19682,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_1511])).

cnf(c_19694,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_19682,c_1663])).

cnf(c_37547,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_27594,c_19694])).

cnf(c_37609,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_37547,c_7])).

cnf(c_2024,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1511])).

cnf(c_38705,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37609,c_2024])).

cnf(c_62828,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_38705])).

cnf(c_62889,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_62828,c_1663])).

cnf(c_38707,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37609,c_19694])).

cnf(c_63335,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_62889,c_38707])).

cnf(c_9813,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
    | arAF0_k3_xboole_0_0 != arAF0_k1_enumset1_0 ),
    inference(instantiation,[status(thm)],[c_4219])).

cnf(c_65721,plain,
    ( iProver_ARSWP_32 != iProver_top
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63335,c_2534,c_9813,c_47365])).

cnf(c_65722,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_65721])).

cnf(c_65760,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_65722])).

cnf(c_65883,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_65760,c_3])).

cnf(c_65753,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_65722])).

cnf(c_62814,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_38705])).

cnf(c_29954,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20729,c_1961])).

cnf(c_30111,plain,
    ( arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_29954,c_1663])).

cnf(c_6696,plain,
    ( X0 != X1
    | arAF0_k1_enumset1_0 != X1
    | arAF0_k1_enumset1_0 = X0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_29943,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_1961])).

cnf(c_31561,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_29943])).

cnf(c_37027,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_31561])).

cnf(c_47148,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37027,c_8])).

cnf(c_48927,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47148,c_1961])).

cnf(c_49085,plain,
    ( arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_48927,c_1663])).

cnf(c_48922,plain,
    ( X0 = X1
    | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47148,c_1963])).

cnf(c_49110,plain,
    ( X0 = X1
    | arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_48922,c_1663])).

cnf(c_58062,plain,
    ( iProver_ARSWP_32 != iProver_top
    | arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30111,c_6696,c_49085,c_49110])).

cnf(c_58063,plain,
    ( arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_58062])).

cnf(c_58077,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_58063])).

cnf(c_1679,plain,
    ( X0 != X1
    | k5_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_66,c_7])).

cnf(c_1802,plain,
    ( X0 != X1
    | X2 != X0
    | k5_xboole_0(X1,k1_xboole_0) = X2 ),
    inference(resolution,[status(thm)],[c_1679,c_66])).

cnf(c_1682,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_66,c_65])).

cnf(c_1791,plain,
    ( ~ iProver_ARSWP_26
    | arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1682,c_1404])).

cnf(c_12074,plain,
    ( ~ iProver_ARSWP_26
    | k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
    | arAF0_k5_enumset1_0 != X0 ),
    inference(resolution,[status(thm)],[c_1802,c_1791])).

cnf(c_12075,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12074])).

cnf(c_2536,plain,
    ( ~ iProver_ARSWP_32
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2534])).

cnf(c_21258,plain,
    ( ~ iProver_ARSWP_32
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_2536])).

cnf(c_18450,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_66,c_65])).

cnf(c_24130,plain,
    ( ~ iProver_ARSWP_32
    | arAF0_k1_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
    inference(resolution,[status(thm)],[c_21258,c_18450])).

cnf(c_44445,plain,
    ( ~ iProver_ARSWP_32
    | X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | arAF0_k1_enumset1_0 = X0 ),
    inference(resolution,[status(thm)],[c_24130,c_66])).

cnf(c_44454,plain,
    ( X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44445])).

cnf(c_24132,plain,
    ( ~ iProver_ARSWP_32
    | X0 != arAF0_k1_enumset1_0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0 ),
    inference(resolution,[status(thm)],[c_21258,c_66])).

cnf(c_18666,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18450,c_7])).

cnf(c_21299,plain,
    ( X0 = X1
    | X1 != k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18666,c_66])).

cnf(c_57646,plain,
    ( ~ iProver_ARSWP_32
    | X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0 ),
    inference(resolution,[status(thm)],[c_24132,c_21299])).

cnf(c_57647,plain,
    ( X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57646])).

cnf(c_58934,plain,
    ( iProver_ARSWP_32 != iProver_top
    | arAF0_k5_enumset1_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58077,c_12075,c_44454,c_57647])).

cnf(c_58935,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_58934])).

cnf(c_1962,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k1_enumset1_0 != X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1510])).

cnf(c_31881,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20729,c_1962])).

cnf(c_48925,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47148,c_1962])).

cnf(c_50820,plain,
    ( iProver_ARSWP_32 != iProver_top
    | k1_xboole_0 != X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31881,c_48925])).

cnf(c_50821,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(renaming,[status(thm)],[c_50820])).

cnf(c_50830,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_50821])).

cnf(c_55034,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_50830,c_8])).

cnf(c_56549,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_55034])).

cnf(c_57397,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_56549])).

cnf(c_56543,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47148,c_55034])).

cnf(c_56622,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_56543,c_1663])).

cnf(c_56555,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_55034])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1408,plain,
    ( ~ iProver_ARSWP_30
    | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1512,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_2932,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1515])).

cnf(c_55147,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2932])).

cnf(c_55040,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_50830])).

cnf(c_2930,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1512])).

cnf(c_3123,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2930])).

cnf(c_3156,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3123,c_7,c_1663])).

cnf(c_3629,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_3156])).

cnf(c_4028,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_3629])).

cnf(c_4040,plain,
    ( arAF0_k5_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_7,c_8])).

cnf(c_4446,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_3629])).

cnf(c_4581,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4446,c_1663])).

cnf(c_4622,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_2534])).

cnf(c_4462,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_1512])).

cnf(c_4510,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4462,c_1663])).

cnf(c_16338,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_4510])).

cnf(c_2931,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1511])).

cnf(c_51308,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_16338,c_2931])).

cnf(c_52872,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_51308])).

cnf(c_52930,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_52872,c_1663])).

cnf(c_52868,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_51308])).

cnf(c_51328,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2931])).

cnf(c_51384,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_51328,c_7,c_8])).

cnf(c_52140,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_51384])).

cnf(c_51314,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2931])).

cnf(c_4453,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_3156])).

cnf(c_4552,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4453,c_1663])).

cnf(c_51327,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_2931])).

cnf(c_50325,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_1515])).

cnf(c_50317,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_1765])).

cnf(c_50238,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47365,c_2540])).

cnf(c_20353,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_1512])).

cnf(c_20387,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_20353,c_7,c_8])).

cnf(c_22347,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_20387])).

cnf(c_22417,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_22347,c_1663])).

cnf(c_47291,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1512])).

cnf(c_47312,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_47291,c_8])).

cnf(c_50168,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_47312])).

cnf(c_47292,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1511])).

cnf(c_47303,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_47292,c_8])).

cnf(c_49232,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_47303])).

cnf(c_19679,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_1512])).

cnf(c_19712,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_19679,c_1663])).

cnf(c_47251,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_19712])).

cnf(c_3752,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_1765])).

cnf(c_3768,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3752,c_1663])).

cnf(c_1687,plain,
    ( ~ iProver_ARSWP_33
    | X0 != arAF0_k1_enumset1_0
    | arAF0_k3_xboole_0_0 = X0 ),
    inference(resolution,[status(thm)],[c_66,c_1411])).

cnf(c_1706,plain,
    ( ~ iProver_ARSWP_33
    | ~ iProver_ARSWP_26
    | arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0 ),
    inference(resolution,[status(thm)],[c_1687,c_1404])).

cnf(c_1707,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_13376,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3768,c_1707])).

cnf(c_38061,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2024])).

cnf(c_39532,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_38061])).

cnf(c_47250,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_39532])).

cnf(c_47154,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_37027])).

cnf(c_22337,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_20387])).

cnf(c_22435,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_22337,c_8])).

cnf(c_22530,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22435,c_1512])).

cnf(c_22589,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_22530,c_1663])).

cnf(c_45377,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_22589])).

cnf(c_33894,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_1963])).

cnf(c_44299,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_33894])).

cnf(c_41998,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_39532])).

cnf(c_42087,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_41998,c_1663])).

cnf(c_2026,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1515])).

cnf(c_41183,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2026])).

cnf(c_41194,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_2026])).

cnf(c_29964,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_1961])).

cnf(c_40241,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_29964])).

cnf(c_33874,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = X1
    | arAF0_k5_enumset1_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_1963])).

cnf(c_40212,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_33874])).

cnf(c_39345,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_19712])).

cnf(c_39450,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_39345,c_1663])).

cnf(c_19344,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_1512])).

cnf(c_23557,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_19344])).

cnf(c_23611,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23557,c_1663])).

cnf(c_23547,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_19344])).

cnf(c_23634,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23547,c_8])).

cnf(c_26807,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23611,c_23634])).

cnf(c_39349,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_26807,c_19712])).

cnf(c_39432,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_39349,c_7,c_8])).

cnf(c_26803,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23611,c_3])).

cnf(c_26021,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_19344])).

cnf(c_28264,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_26803,c_26021])).

cnf(c_28841,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28264,c_23611])).

cnf(c_39330,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28841,c_19712])).

cnf(c_39350,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_19712])).

cnf(c_39360,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19712,c_19344])).

cnf(c_21726,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20729,c_1511])).

cnf(c_21745,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_21726,c_1663])).

cnf(c_38712,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37609,c_21745])).

cnf(c_38711,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37609,c_1961])).

cnf(c_38710,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_37609,c_1963])).

cnf(c_21725,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20729,c_2534])).

cnf(c_21756,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_21725,c_1663])).

cnf(c_38045,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_2024])).

cnf(c_38213,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_38045,c_8])).

cnf(c_38313,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_38213])).

cnf(c_38052,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2024])).

cnf(c_38060,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_2024])).

cnf(c_37532,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17757,c_19694])).

cnf(c_37643,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_37532,c_8])).

cnf(c_37551,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_19694])).

cnf(c_37546,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_19694])).

cnf(c_31884,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | k1_xboole_0 != X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1962])).

cnf(c_31968,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_31884])).

cnf(c_32972,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_31968,c_8])).

cnf(c_34431,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_32972])).

cnf(c_36052,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_34431])).

cnf(c_1964,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k1_enumset1_0 != X1
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1510])).

cnf(c_35710,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k5_enumset1_0 != X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_1964])).

cnf(c_35712,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k5_enumset1_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1964])).

cnf(c_33887,plain,
    ( X0 = X1
    | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1963])).

cnf(c_34013,plain,
    ( X0 = X1
    | arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(demodulation,[status(thm)],[c_33887,c_1663])).

cnf(c_29957,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1961])).

cnf(c_30086,plain,
    ( arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(demodulation,[status(thm)],[c_29957,c_1663])).

cnf(c_35095,plain,
    ( arAF0_k3_xboole_0_0 != X0
    | arAF0_k1_enumset1_0 = X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34013,c_6696,c_30086])).

cnf(c_35110,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_35095])).

cnf(c_35108,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_35095])).

cnf(c_33891,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_1963])).

cnf(c_33974,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_33891,c_8])).

cnf(c_29961,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_1961])).

cnf(c_30047,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_29961,c_8])).

cnf(c_34855,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33974,c_6696,c_30047])).

cnf(c_33892,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_1963])).

cnf(c_33959,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_33892,c_8])).

cnf(c_34843,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33959,c_6696,c_31561])).

cnf(c_33897,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1963])).

cnf(c_33904,plain,
    ( X0 = X1
    | arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(demodulation,[status(thm)],[c_33897,c_8])).

cnf(c_1801,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1679,c_1682])).

cnf(c_1803,plain,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = k5_xboole_0(X0,k1_xboole_0)
    | arAF0_k1_enumset1_0 != X0 ),
    inference(resolution,[status(thm)],[c_1679,c_1687])).

cnf(c_2776,plain,
    ( ~ iProver_ARSWP_33
    | X0 != k5_xboole_0(X1,k1_xboole_0)
    | arAF0_k3_xboole_0_0 = X0
    | arAF0_k1_enumset1_0 != X1 ),
    inference(resolution,[status(thm)],[c_1803,c_66])).

cnf(c_7257,plain,
    ( ~ iProver_ARSWP_33
    | X0 != X1
    | arAF0_k3_xboole_0_0 = X0
    | arAF0_k1_enumset1_0 != X1 ),
    inference(resolution,[status(thm)],[c_1801,c_2776])).

cnf(c_7258,plain,
    ( X0 != X1
    | arAF0_k3_xboole_0_0 = X0
    | arAF0_k1_enumset1_0 != X1
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7257])).

cnf(c_29967,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1961])).

cnf(c_29977,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(demodulation,[status(thm)],[c_29967,c_8])).

cnf(c_34521,plain,
    ( arAF0_k1_enumset1_0 = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33904,c_6696,c_7258,c_30086,c_29977,c_34013])).

cnf(c_34437,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_32972])).

cnf(c_33893,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_1963])).

cnf(c_33896,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_1963])).

cnf(c_33876,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_16338,c_1963])).

cnf(c_33886,plain,
    ( X0 = X1
    | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X1
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_1963])).

cnf(c_32978,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k1_xboole_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_31968])).

cnf(c_20617,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_20368])).

cnf(c_32247,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_20617])).

cnf(c_31883,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k5_enumset1_0 != X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_1962])).

cnf(c_31885,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
    | arAF0_k5_enumset1_0 != X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1962])).

cnf(c_29962,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_1961])).

cnf(c_30032,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | k1_xboole_0 != X0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_29962,c_8])).

cnf(c_29963,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_1961])).

cnf(c_16358,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_3156])).

cnf(c_29948,plain,
    ( arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | arAF0_k5_enumset1_0 != X0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_16358,c_1961])).

cnf(c_29966,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_1961])).

cnf(c_29945,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_16338,c_1961])).

cnf(c_29956,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X0
    | arAF0_k1_enumset1_0 = X0
    | arAF0_k1_enumset1_0 = X1
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_1961])).

cnf(c_23679,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_19345])).

cnf(c_24763,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_23679])).

cnf(c_24813,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_24763,c_1663])).

cnf(c_29298,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_24813,c_23747])).

cnf(c_28844,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28264,c_23634])).

cnf(c_28839,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_28264,c_3])).

cnf(c_27296,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23747,c_3])).

cnf(c_28347,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_27296])).

cnf(c_28420,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_28347,c_1663])).

cnf(c_28009,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_21745])).

cnf(c_28136,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_28009,c_1663])).

cnf(c_28030,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_21745])).

cnf(c_28034,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_21745])).

cnf(c_26076,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_1512])).

cnf(c_26023,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_22417,c_20387])).

cnf(c_25278,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_1511])).

cnf(c_23680,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_19345])).

cnf(c_25082,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_23680])).

cnf(c_24274,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23774,c_3])).

cnf(c_24059,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_23634,c_3])).

cnf(c_23658,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_19345])).

cnf(c_23791,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_23658,c_1663])).

cnf(c_19346,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_17774,c_1515])).

cnf(c_23221,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19346,c_3])).

cnf(c_16341,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_4510])).

cnf(c_16456,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_16341,c_1663])).

cnf(c_3640,plain,
    ( ~ iProver_ARSWP_32
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_2536])).

cnf(c_5402,plain,
    ( ~ iProver_ARSWP_33
    | ~ iProver_ARSWP_32
    | arAF0_k3_xboole_0_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
    inference(resolution,[status(thm)],[c_3640,c_1687])).

cnf(c_5429,plain,
    ( ~ iProver_ARSWP_33
    | ~ iProver_ARSWP_32
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_5402,c_1682])).

cnf(c_5430,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5429])).

cnf(c_16891,plain,
    ( iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_33 != iProver_top
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16456,c_5430])).

cnf(c_16892,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(renaming,[status(thm)],[c_16891])).

cnf(c_16906,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_16892])).

cnf(c_21140,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_16906])).

cnf(c_13414,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2534])).

cnf(c_20916,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13414,c_3])).

cnf(c_20618,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_20368])).

cnf(c_20613,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_20368])).

cnf(c_20354,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_19736,c_2534])).

cnf(c_19322,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_17774])).

cnf(c_4461,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_2930])).

cnf(c_4519,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4461,c_8,c_1663])).

cnf(c_4803,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_4519])).

cnf(c_4821,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4803,c_1663])).

cnf(c_1680,plain,
    ( X0 != k1_xboole_0
    | k5_xboole_0(X1,X1) = X0 ),
    inference(resolution,[status(thm)],[c_66,c_8])).

cnf(c_1814,plain,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = k5_xboole_0(X0,X0)
    | arAF0_k1_enumset1_0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1680,c_1687])).

cnf(c_2796,plain,
    ( ~ iProver_ARSWP_33
    | X0 != k5_xboole_0(X1,X1)
    | arAF0_k3_xboole_0_0 = X0
    | arAF0_k1_enumset1_0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1814,c_66])).

cnf(c_1786,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1682,c_7])).

cnf(c_4888,plain,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = k1_xboole_0
    | arAF0_k1_enumset1_0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2796,c_1786])).

cnf(c_4889,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | arAF0_k1_enumset1_0 != k1_xboole_0
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4888])).

cnf(c_6412,plain,
    ( iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_33 != iProver_top
    | arAF0_k3_xboole_0_0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4821,c_2545,c_4889])).

cnf(c_6413,plain,
    ( arAF0_k3_xboole_0_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(renaming,[status(thm)],[c_6412])).

cnf(c_2879,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_1511])).

cnf(c_2897,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2879,c_1663])).

cnf(c_18226,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_2897])).

cnf(c_18266,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_18226,c_7])).

cnf(c_2563,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1511])).

cnf(c_2587,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2563,c_1663])).

cnf(c_18557,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_18266,c_2587])).

cnf(c_18544,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_18266,c_2897])).

cnf(c_4465,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_1511])).

cnf(c_4483,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4465,c_1663])).

cnf(c_18374,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_4483])).

cnf(c_18225,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2897])).

cnf(c_18224,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2897])).

cnf(c_17775,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_17757])).

cnf(c_16907,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_16892])).

cnf(c_16346,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_4510])).

cnf(c_6435,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_1512])).

cnf(c_6458,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6435,c_7])).

cnf(c_16353,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_6458])).

cnf(c_2928,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1512])).

cnf(c_2966,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2928,c_1663])).

cnf(c_16350,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_2966])).

cnf(c_13415,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_1511])).

cnf(c_13430,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_13415,c_7,c_8])).

cnf(c_13920,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_13430])).

cnf(c_15350,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_13920])).

cnf(c_13413,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_1512])).

cnf(c_13447,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_13413,c_7,c_8])).

cnf(c_13988,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_13447])).

cnf(c_13921,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_13430])).

cnf(c_2025,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1511])).

cnf(c_2732,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2025])).

cnf(c_2746,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2732,c_7,c_8])).

cnf(c_13412,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2746])).

cnf(c_2877,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_2025])).

cnf(c_2914,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2877,c_8,c_1663])).

cnf(c_13407,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2914])).

cnf(c_2731,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2025])).

cnf(c_2755,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2731,c_7,c_1663])).

cnf(c_3375,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2755])).

cnf(c_5940,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_3375,c_2025])).

cnf(c_13401,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_5940])).

cnf(c_13393,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_13376,c_2587])).

cnf(c_3787,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2914])).

cnf(c_12917,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_3787])).

cnf(c_3785,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2914])).

cnf(c_11556,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_2025])).

cnf(c_11570,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11556,c_7])).

cnf(c_6847,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_6458])).

cnf(c_6916,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6847,c_1663])).

cnf(c_10911,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6916,c_3])).

cnf(c_6043,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_5940])).

cnf(c_6129,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6043,c_1663])).

cnf(c_9865,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_6129,c_3])).

cnf(c_10596,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_9865])).

cnf(c_10682,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_10596,c_1663])).

cnf(c_10226,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_2966])).

cnf(c_10307,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_10226,c_1663])).

cnf(c_10230,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2966])).

cnf(c_10223,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_2966])).

cnf(c_10238,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_3156])).

cnf(c_10236,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_4519])).

cnf(c_10233,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_6458])).

cnf(c_9934,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_2587])).

cnf(c_9999,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_9934,c_1663])).

cnf(c_9941,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_2587])).

cnf(c_9939,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2587])).

cnf(c_3195,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2746])).

cnf(c_9627,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_3195])).

cnf(c_5079,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_1512])).

cnf(c_5113,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5079,c_7,c_8])).

cnf(c_9128,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_5113])).

cnf(c_6855,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_3156])).

cnf(c_8716,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6855,c_3])).

cnf(c_6853,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6458,c_4519])).

cnf(c_8259,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_6853,c_3])).

cnf(c_6044,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_5940])).

cnf(c_7406,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_6044])).

cnf(c_7859,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_7406])).

cnf(c_7880,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_7859,c_1663])).

cnf(c_7910,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_7880,c_3])).

cnf(c_6851,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_6458])).

cnf(c_6038,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_5940])).

cnf(c_6154,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6038,c_1663])).

cnf(c_6039,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_5940])).

cnf(c_6143,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6039,c_1663])).

cnf(c_6045,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_5940])).

cnf(c_6050,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_5940,c_2755])).

cnf(c_6049,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_5940,c_2914])).

cnf(c_5939,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_3375,c_2930])).

cnf(c_2564,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1515])).

cnf(c_2578,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2564,c_1663])).

cnf(c_5681,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_1515])).

cnf(c_5673,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_2578])).

cnf(c_5081,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_1511])).

cnf(c_5095,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5081,c_7,c_8])).

cnf(c_5309,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_5095])).

cnf(c_5263,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_5113])).

cnf(c_5080,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_2534])).

cnf(c_5077,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_2755])).

cnf(c_4463,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_2025])).

cnf(c_4500,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4463,c_8,c_1663])).

cnf(c_5071,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_4500])).

cnf(c_4805,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_4519])).

cnf(c_3786,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2914])).

cnf(c_3817,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3786,c_1663])).

cnf(c_3754,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1765])).

cnf(c_3124,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_2930])).

cnf(c_3147,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3124,c_7,c_8])).

cnf(c_3421,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_3147])).

cnf(c_3376,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2755])).

cnf(c_3398,plain,
    ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3376,c_1663])).

cnf(c_4261,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_3754])).

cnf(c_4276,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4261,c_1663])).

cnf(c_1792,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_5539,plain,
    ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4276,c_1792])).

cnf(c_1766,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1515])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:25:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 19.33/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.33/2.98  
% 19.33/2.98  ------  iProver source info
% 19.33/2.98  
% 19.33/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.33/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.33/2.98  git: non_committed_changes: false
% 19.33/2.98  git: last_make_outside_of_git: false
% 19.33/2.98  
% 19.33/2.98  ------ 
% 19.33/2.98  ------ Parsing...
% 19.33/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  ------ Proving...
% 19.33/2.98  ------ Problem Properties 
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  clauses                                 13
% 19.33/2.98  conjectures                             2
% 19.33/2.98  EPR                                     1
% 19.33/2.98  Horn                                    12
% 19.33/2.98  unary                                   12
% 19.33/2.98  binary                                  0
% 19.33/2.98  lits                                    15
% 19.33/2.98  lits eq                                 15
% 19.33/2.98  fd_pure                                 0
% 19.33/2.98  fd_pseudo                               0
% 19.33/2.98  fd_cond                                 0
% 19.33/2.98  fd_pseudo_cond                          1
% 19.33/2.98  AC symbols                              0
% 19.33/2.98  
% 19.33/2.98  ------ Input Options Time Limit: Unbounded
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.33/2.98  Current options:
% 19.33/2.98  ------ 
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  % SZS status CounterSatisfiable for theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  % SZS output start Saturation for theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  fof(f5,axiom,(
% 19.33/2.98    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f37,plain,(
% 19.33/2.98    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f5])).
% 19.33/2.98  
% 19.33/2.98  fof(f4,axiom,(
% 19.33/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f25,plain,(
% 19.33/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.33/2.98    inference(rectify,[],[f4])).
% 19.33/2.98  
% 19.33/2.98  fof(f26,plain,(
% 19.33/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.33/2.98    inference(ennf_transformation,[],[f25])).
% 19.33/2.98  
% 19.33/2.98  fof(f29,plain,(
% 19.33/2.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 19.33/2.98    introduced(choice_axiom,[])).
% 19.33/2.98  
% 19.33/2.98  fof(f30,plain,(
% 19.33/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.33/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).
% 19.33/2.98  
% 19.33/2.98  fof(f35,plain,(
% 19.33/2.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f30])).
% 19.33/2.98  
% 19.33/2.98  fof(f36,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f30])).
% 19.33/2.98  
% 19.33/2.98  fof(f19,axiom,(
% 19.33/2.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f51,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f19])).
% 19.33/2.98  
% 19.33/2.98  fof(f20,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f52,plain,(
% 19.33/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f20])).
% 19.33/2.98  
% 19.33/2.98  fof(f21,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f53,plain,(
% 19.33/2.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f21])).
% 19.33/2.98  
% 19.33/2.98  fof(f22,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f54,plain,(
% 19.33/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f22])).
% 19.33/2.98  
% 19.33/2.98  fof(f58,plain,(
% 19.33/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f53,f54])).
% 19.33/2.98  
% 19.33/2.98  fof(f59,plain,(
% 19.33/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f52,f58])).
% 19.33/2.98  
% 19.33/2.98  fof(f62,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f51,f59])).
% 19.33/2.98  
% 19.33/2.98  fof(f23,conjecture,(
% 19.33/2.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f24,negated_conjecture,(
% 19.33/2.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 19.33/2.98    inference(negated_conjecture,[],[f23])).
% 19.33/2.98  
% 19.33/2.98  fof(f28,plain,(
% 19.33/2.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 19.33/2.98    inference(ennf_transformation,[],[f24])).
% 19.33/2.98  
% 19.33/2.98  fof(f31,plain,(
% 19.33/2.98    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 19.33/2.98    introduced(choice_axiom,[])).
% 19.33/2.98  
% 19.33/2.98  fof(f32,plain,(
% 19.33/2.98    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 19.33/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f31])).
% 19.33/2.98  
% 19.33/2.98  fof(f55,plain,(
% 19.33/2.98    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 19.33/2.98    inference(cnf_transformation,[],[f32])).
% 19.33/2.98  
% 19.33/2.98  fof(f17,axiom,(
% 19.33/2.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f49,plain,(
% 19.33/2.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f17])).
% 19.33/2.98  
% 19.33/2.98  fof(f18,axiom,(
% 19.33/2.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f50,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f18])).
% 19.33/2.98  
% 19.33/2.98  fof(f61,plain,(
% 19.33/2.98    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f49,f50])).
% 19.33/2.98  
% 19.33/2.98  fof(f69,plain,(
% 19.33/2.98    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 19.33/2.98    inference(definition_unfolding,[],[f55,f61,f61,f61])).
% 19.33/2.98  
% 19.33/2.98  fof(f15,axiom,(
% 19.33/2.98    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f27,plain,(
% 19.33/2.98    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 19.33/2.98    inference(ennf_transformation,[],[f15])).
% 19.33/2.98  
% 19.33/2.98  fof(f47,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 19.33/2.98    inference(cnf_transformation,[],[f27])).
% 19.33/2.98  
% 19.33/2.98  fof(f6,axiom,(
% 19.33/2.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f38,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f6])).
% 19.33/2.98  
% 19.33/2.98  fof(f68,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 19.33/2.98    inference(definition_unfolding,[],[f47,f38,f61,f50])).
% 19.33/2.98  
% 19.33/2.98  fof(f8,axiom,(
% 19.33/2.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f40,plain,(
% 19.33/2.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.33/2.98    inference(cnf_transformation,[],[f8])).
% 19.33/2.98  
% 19.33/2.98  fof(f56,plain,(
% 19.33/2.98    sK1 != sK2),
% 19.33/2.98    inference(cnf_transformation,[],[f32])).
% 19.33/2.98  
% 19.33/2.98  fof(f16,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f48,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f16])).
% 19.33/2.98  
% 19.33/2.98  fof(f9,axiom,(
% 19.33/2.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f41,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f9])).
% 19.33/2.98  
% 19.33/2.98  fof(f57,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f41,f38])).
% 19.33/2.98  
% 19.33/2.98  fof(f63,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k1_enumset1(X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f48,f57,f59])).
% 19.33/2.98  
% 19.33/2.98  fof(f7,axiom,(
% 19.33/2.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f39,plain,(
% 19.33/2.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.33/2.98    inference(cnf_transformation,[],[f7])).
% 19.33/2.98  
% 19.33/2.98  fof(f2,axiom,(
% 19.33/2.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f34,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f2])).
% 19.33/2.98  
% 19.33/2.98  fof(f13,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f45,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f13])).
% 19.33/2.98  
% 19.33/2.98  fof(f11,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f43,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f11])).
% 19.33/2.98  
% 19.33/2.98  fof(f60,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f43,f57,f54])).
% 19.33/2.98  
% 19.33/2.98  fof(f66,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))))) )),
% 19.33/2.98    inference(definition_unfolding,[],[f45,f57,f54,f60])).
% 19.33/2.98  
% 19.33/2.98  fof(f12,axiom,(
% 19.33/2.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f44,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f12])).
% 19.33/2.98  
% 19.33/2.98  fof(f65,plain,(
% 19.33/2.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))))) )),
% 19.33/2.98    inference(definition_unfolding,[],[f44,f57,f58,f59,f60])).
% 19.33/2.98  
% 19.33/2.98  cnf(c_59,plain,
% 19.33/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.33/2.98      theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58,plain,
% 19.33/2.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.33/2.98      theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_52,plain,( X0_2 = X0_2 ),theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6,plain,
% 19.33/2.98      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 19.33/2.98      inference(cnf_transformation,[],[f37]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5,plain,
% 19.33/2.98      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 19.33/2.98      inference(cnf_transformation,[],[f35]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4,plain,
% 19.33/2.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 19.33/2.98      inference(cnf_transformation,[],[f36]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_0,plain,
% 19.33/2.98      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 19.33/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1404,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_26 | arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1516,plain,
% 19.33/2.98      ( arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_15,negated_conjecture,
% 19.33/2.98      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 19.33/2.98      inference(cnf_transformation,[],[f69]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1411,negated_conjecture,
% 19.33/2.98      ( ~ iProver_ARSWP_33 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1509,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | X2 = X1
% 19.33/2.98      | k5_xboole_0(k1_enumset1(X1,X0,X2),k3_xboole_0(k1_enumset1(X1,X0,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X0,X0,X2) ),
% 19.33/2.98      inference(cnf_transformation,[],[f68]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1410,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | X0 = X1
% 19.33/2.98      | X2 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1510,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | X2 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1410]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_8,plain,
% 19.33/2.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.33/2.98      inference(cnf_transformation,[],[f40]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1929,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | k1_xboole_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1510,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_14,negated_conjecture,
% 19.33/2.98      ( sK1 != sK2 ),
% 19.33/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65,plain,( X0 = X0 ),theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_71,plain,( sK1 = sK1 ),inference(instantiation,[status(thm)],[c_65]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_66,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_264,plain,
% 19.33/2.98      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_265,plain,
% 19.33/2.98      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_264]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1946,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | sK2 = X0
% 19.33/2.98      | sK1 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1510,c_14]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2436,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | sK2 = sK1
% 19.33/2.98      | sK1 != sK1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_1946]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2534,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_1929,c_14,c_71,c_265,c_2436]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2541,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2545,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2541,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2565,plain,
% 19.33/2.98      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1516]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1,plain,
% 19.33/2.98      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k1_enumset1(X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 19.33/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1405,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_27
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0 ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1515,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2880,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7,plain,
% 19.33/2.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.33/2.98      inference(cnf_transformation,[],[f39]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3,plain,
% 19.33/2.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.33/2.98      inference(cnf_transformation,[],[f34]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1663,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_7,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2886,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2880,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1414,plain,
% 19.33/2.98      ( arAF0_k5_enumset1_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3044,plain,
% 19.33/2.98      ( X0 != X1 | k5_xboole_0(X2,X3) != X1 | k5_xboole_0(X2,X3) = X0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4219,plain,
% 19.33/2.98      ( X0 != arAF0_k1_enumset1_0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_3044]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9812,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | arAF0_k5_enumset1_0 != arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_4219]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_17756,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_2886,c_1414,c_2534,c_9812]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_17757,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_17756]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_17774,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_17757]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1765,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19341,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_1765]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19375,plain,
% 19.33/2.98      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_19341,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2540,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47237,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_2540]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47365,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_47237,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1963,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_1510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33888,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_72710,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_33888]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1961,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_1510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29958,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_71848,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_29958]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19668,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_1765]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19736,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_19668,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_11,plain,
% 19.33/2.98      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k1_enumset1(X6,X7,X8),k3_xboole_0(k1_enumset1(X6,X7,X8),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) ),
% 19.33/2.98      inference(cnf_transformation,[],[f66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1409,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_31
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1511,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20355,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20368,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_20355,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20604,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_20368]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20729,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_20604,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19345,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23675,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_20729,c_19345]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23747,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_23675,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23664,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_19345]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23774,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_23664,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_27300,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23747,c_23774]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_27481,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_27300]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_27594,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_27481,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19682,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19694,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_19682,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37547,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_27594,c_19694]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37609,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_37547,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2024,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38705,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37609,c_2024]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62828,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_38705]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62889,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_62828,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38707,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37609,c_19694]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_63335,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_62889,c_38707]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9813,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) != arAF0_k1_enumset1_0
% 19.33/2.98      | arAF0_k3_xboole_0_0 != arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_4219]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65721,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_63335,c_2534,c_9813,c_47365]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65722,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_65721]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65760,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_65722]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65883,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_65760,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_65753,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_65722]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62814,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2540,c_38705]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29954,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_20729,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_30111,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_29954,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6696,plain,
% 19.33/2.98      ( X0 != X1 | arAF0_k1_enumset1_0 != X1 | arAF0_k1_enumset1_0 = X0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29943,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31561,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_29943]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37027,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(equality_resolution,[status(thm)],[c_31561]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47148,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37027,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_48927,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47148,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_49085,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_48927,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_48922,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47148,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_49110,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_48922,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58062,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_30111,c_6696,c_49085,c_49110]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58063,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_58062]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58077,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_58063]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1679,plain,
% 19.33/2.98      ( X0 != X1 | k5_xboole_0(X1,k1_xboole_0) = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_66,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1802,plain,
% 19.33/2.98      ( X0 != X1 | X2 != X0 | k5_xboole_0(X1,k1_xboole_0) = X2 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1679,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1682,plain,
% 19.33/2.98      ( X0 != X1 | X1 = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_66,c_65]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1791,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_26 | arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1682,c_1404]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_12074,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_26
% 19.33/2.98      | k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1802,c_1791]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_12075,plain,
% 19.33/2.98      ( k5_xboole_0(X0,k1_xboole_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_12074]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2536,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21258,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(global_propositional_subsumption,[status(thm)],[c_1410,c_2536]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18450,plain,
% 19.33/2.98      ( X0 != X1 | X1 = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_66,c_65]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24130,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | arAF0_k1_enumset1_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_21258,c_18450]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_44445,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_24130,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_44454,plain,
% 19.33/2.98      ( X0 != k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_44445]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24132,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | X0 != arAF0_k1_enumset1_0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_21258,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18666,plain,
% 19.33/2.98      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_18450,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21299,plain,
% 19.33/2.98      ( X0 = X1 | X1 != k5_xboole_0(X0,k1_xboole_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_18666,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_57646,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_24132,c_21299]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_57647,plain,
% 19.33/2.98      ( X0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | k5_xboole_0(X0,k1_xboole_0) != arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_57646]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58934,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_58077,c_12075,c_44454,c_57647]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_58935,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_58934]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1962,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_1510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31881,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | k1_xboole_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_20729,c_1962]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_48925,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | k1_xboole_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47148,c_1962]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50820,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | k1_xboole_0 != X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_31881,c_48925]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50821,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_50820]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50830,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(equality_resolution,[status(thm)],[c_50821]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_55034,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_50830,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_56549,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_55034]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_57397,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_56549]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_56543,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47148,c_55034]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_56622,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_56543,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_56555,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_55034]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10,plain,
% 19.33/2.98      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k3_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) ),
% 19.33/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1408,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_30
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 19.33/2.98      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1512,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2932,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1512,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_55147,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_2932]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_55040,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_50830]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2930,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3123,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_2930]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3156,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_3123,c_7,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3629,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_3156]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4028,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_3629]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4040,plain,
% 19.33/2.98      ( arAF0_k5_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4028,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4446,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_3629]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4581,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4446,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4622,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4581,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4462,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4510,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4462,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16338,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4622,c_4510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2931,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1512,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_51308,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_16338,c_2931]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_52872,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_51308]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_52930,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_52872,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_52868,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4622,c_51308]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_51328,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_2931]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_51384,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_51328,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_52140,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_51384]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_51314,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_2931]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4453,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_3156]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4552,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4453,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_51327,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_2931]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50325,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50317,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_1765]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50238,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_47365,c_2540]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20353,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20387,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_20353,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22347,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_20387]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22417,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_22347,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47291,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2540,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47312,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_47291,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_50168,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_47312]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47292,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2540,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47303,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_47292,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_49232,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_47303]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19679,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19712,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_19679,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47251,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2540,c_19712]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3752,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_1765]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3768,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_3752,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1687,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | X0 != arAF0_k1_enumset1_0
% 19.33/2.98      | arAF0_k3_xboole_0_0 = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_66,c_1411]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1706,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | ~ iProver_ARSWP_26
% 19.33/2.98      | arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1687,c_1404]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1707,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_1706]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13376,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,[status(thm)],[c_3768,c_1707]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38061,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2024]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39532,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3,c_38061]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47250,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2540,c_39532]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_47154,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_37027]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22337,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_20387]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22435,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_22337,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22530,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22435,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_22589,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_22530,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_45377,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_22589]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33894,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_44299,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3,c_33894]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_41998,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_39532]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_42087,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_41998,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2026,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1511,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_41183,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_2026]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_41194,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_2026]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29964,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_40241,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3,c_29964]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33874,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_40212,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | k1_xboole_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_33874]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39345,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_19712]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39450,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_39345,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19344,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23557,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_19344]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23611,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_23557,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23547,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_19344]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23634,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_23547,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26807,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23611,c_23634]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39349,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_26807,c_19712]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39432,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_39349,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26803,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23611,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26021,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_19344]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28264,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_26803,c_26021]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28841,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_28264,c_23611]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39330,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_28841,c_19712]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39350,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_19712]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_39360,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19712,c_19344]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21726,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_20729,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21745,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_21726,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38712,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37609,c_21745]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38711,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37609,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38710,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_37609,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21725,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_20729,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21756,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_21725,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38045,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_2024]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38213,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_38045,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38313,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_21756,c_38213]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38052,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_2024]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_38060,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_2024]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37532,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17757,c_19694]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37643,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_37532,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37551,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_19694]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_37546,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_19694]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31884,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | k1_xboole_0 != X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1962]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31968,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_resolution,[status(thm)],[c_31884]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_32972,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_31968,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34431,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_32972]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_36052,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_34431]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1964,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_1510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_35710,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4581,c_1964]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_35712,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1964]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33887,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34013,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_33887,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29957,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_30086,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_29957,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_35095,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_34013,c_6696,c_30086]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_35110,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_35095]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_35108,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_35095]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33891,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33974,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_33891,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29961,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_30047,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_29961,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34855,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_33974,c_6696,c_30047]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33892,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_21756,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33959,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_33892,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34843,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_33959,c_6696,c_31561]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33897,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33904,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_33897,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1801,plain,
% 19.33/2.98      ( X0 != X1 | X0 = k5_xboole_0(X1,k1_xboole_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1679,c_1682]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1803,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | arAF0_k3_xboole_0_0 = k5_xboole_0(X0,k1_xboole_0)
% 19.33/2.98      | arAF0_k1_enumset1_0 != X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1679,c_1687]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2776,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | X0 != k5_xboole_0(X1,k1_xboole_0)
% 19.33/2.98      | arAF0_k3_xboole_0_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 != X1 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1803,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7257,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | X0 != X1
% 19.33/2.98      | arAF0_k3_xboole_0_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 != X1 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1801,c_2776]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7258,plain,
% 19.33/2.98      ( X0 != X1
% 19.33/2.98      | arAF0_k3_xboole_0_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_7257]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29967,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29977,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_29967,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34521,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_33904,c_6696,c_7258,c_30086,c_29977,c_34013]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_34437,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_32972]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33893,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33896,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33876,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_16338,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_33886,plain,
% 19.33/2.98      ( X0 = X1
% 19.33/2.98      | k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X1
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4581,c_1963]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_32978,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(equality_factoring,[status(thm)],[c_31968]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20617,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_20368]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_32247,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_21756,c_20617]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31883,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4581,c_1962]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_31885,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X0
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_1962]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29962,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_21756,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_30032,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | k1_xboole_0 != X0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_29962,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29963,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16358,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4510,c_3156]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29948,plain,
% 19.33/2.98      ( arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | arAF0_k5_enumset1_0 != X0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_16358,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29966,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29945,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_16338,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29956,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) != X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 = X1
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4581,c_1961]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23679,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_19345]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24763,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_23679]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24813,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_24763,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_29298,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_24813,c_23747]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28844,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_28264,c_23634]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28839,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_28264,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_27296,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23747,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28347,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_27296]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28420,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_28347,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28009,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_21745]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28136,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_28009,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28030,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_21745]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_28034,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_21745]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26076,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26023,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_22417,c_20387]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_25278,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_21756,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23680,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_19345]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_25082,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3,c_23680]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24274,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23774,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_24059,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_23634,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23658,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19375,c_19345]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23791,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_23658,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19346,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_17774,c_1515]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_23221,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19346,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16341,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_4510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16456,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_16341,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3640,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_32
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 19.33/2.98      inference(global_propositional_subsumption,[status(thm)],[c_1410,c_2536]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5402,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | ~ iProver_ARSWP_32
% 19.33/2.98      | arAF0_k3_xboole_0_0 = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_3640,c_1687]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5429,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | ~ iProver_ARSWP_32
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_5402,c_1682]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5430,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_5429]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16891,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0 ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_16456,c_5430]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16892,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_16891]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16906,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_16892]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_21140,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_16906]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13414,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20916,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13414,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20618,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_20368]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20613,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_20368]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20354,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_27 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_19736,c_2534]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_19322,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_17774]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4461,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_2930]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4519,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4461,c_8,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4803,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_4519]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4821,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4803,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1680,plain,
% 19.33/2.98      ( X0 != k1_xboole_0 | k5_xboole_0(X1,X1) = X0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_66,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1814,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | arAF0_k3_xboole_0_0 = k5_xboole_0(X0,X0)
% 19.33/2.98      | arAF0_k1_enumset1_0 != k1_xboole_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1680,c_1687]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2796,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | X0 != k5_xboole_0(X1,X1)
% 19.33/2.98      | arAF0_k3_xboole_0_0 = X0
% 19.33/2.98      | arAF0_k1_enumset1_0 != k1_xboole_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1814,c_66]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1786,plain,
% 19.33/2.98      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_1682,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4888,plain,
% 19.33/2.98      ( ~ iProver_ARSWP_33
% 19.33/2.98      | arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | arAF0_k1_enumset1_0 != k1_xboole_0 ),
% 19.33/2.98      inference(resolution,[status(thm)],[c_2796,c_1786]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4889,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | arAF0_k1_enumset1_0 != k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_4888]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6412,plain,
% 19.33/2.98      ( iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | arAF0_k3_xboole_0_0 = k1_xboole_0 ),
% 19.33/2.98      inference(global_propositional_subsumption,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_4821,c_2545,c_4889]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6413,plain,
% 19.33/2.98      ( arAF0_k3_xboole_0_0 = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top ),
% 19.33/2.98      inference(renaming,[status(thm)],[c_6412]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2879,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2897,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2879,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18226,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6413,c_2897]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18266,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_18226,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2563,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2587,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2563,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18557,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_18266,c_2587]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18544,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_18266,c_2897]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4465,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4483,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_4465,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18374,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_4483]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18225,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2897]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_18224,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2897]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_17775,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_17757]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16907,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_16892]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16346,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_4510]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6435,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6413,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6458,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_6435,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16353,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4510,c_6458]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2928,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2966,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2928,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_16350,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4510,c_2966]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13415,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13430,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_13415,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13920,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_13430]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_15350,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_13920]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13413,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13447,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_13413,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13988,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_13447]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13921,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_13430]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2025,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_1511]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2732,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2025]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2746,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2732,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13412,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2746]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2877,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_2025]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2914,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2877,c_8,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13407,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2914]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2731,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_2025]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2755,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_2731,c_7,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3375,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_2755]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5940,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3375,c_2025]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13401,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_5940]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_13393,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_13376,c_2587]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3787,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2914]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_12917,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_3787]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3785,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2534,c_2914]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_11556,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_3785,c_2025]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_11570,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_11556,c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6847,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_6458]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6916,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_6847,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10911,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6916,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6043,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2545,c_5940]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6129,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_6043,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9865,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6129,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10596,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_9865]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10682,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_10596,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10226,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_2966]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10307,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k3_xboole_0_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_10226,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10230,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_2966]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10223,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4622,c_2966]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10238,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2966,c_3156]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10236,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2966,c_4519]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10233,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2966,c_6458]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9934,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_2587]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9999,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_9934,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9941,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_2587]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9939,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2587]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3195,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_2746]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9627,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_3195]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5079,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4552,c_1512]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5113,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_5079,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_9128,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4622,c_5113]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6855,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6458,c_3156]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_8716,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6855,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6853,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6458,c_4519]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_8259,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_6853,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6044,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1516,c_5940]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7406,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_6044]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7859,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_2565,c_7406]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7880,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_7859,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7910,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_7880,c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6851,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1509,c_6458]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6038,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_4040,c_5940]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6154,plain,
% 19.33/2.98      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.98      | iProver_ARSWP_33 != iProver_top
% 19.33/2.98      | iProver_ARSWP_32 != iProver_top
% 19.33/2.98      | iProver_ARSWP_31 != iProver_top
% 19.33/2.98      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.98      inference(demodulation,[status(thm)],[c_6038,c_1663]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6039,plain,
% 19.33/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2565,c_5940]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_6143,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_6039,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_6045,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_5940]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_6050,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_5940,c_2755]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_6049,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_5940,c_2914]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5939,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_3375,c_2930]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_2564,plain,
% 19.33/2.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2545,c_1515]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_2578,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_2564,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5681,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2578,c_1515]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5673,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_2578]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5081,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_1511]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5095,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_5081,c_7,c_8]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5309,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_5095]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5263,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_5113]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5080,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0) = arAF0_k1_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_2534]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5077,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_2755]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_4463,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4040,c_2025]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_4500,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_4463,c_8,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5071,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k5_enumset1_0)) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_4552,c_4500]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_4805,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_4519]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3786,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2545,c_2914]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3817,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = k1_xboole_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_3786,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3754,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_1765]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3124,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k5_enumset1_0)) = k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0))
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1516,c_2930]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3147,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_3124,c_7,c_8]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3421,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_30 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_3147]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3376,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2545,c_2755]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_3398,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_31 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_3376,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_4261,plain,
% 19.33/2.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_2565,c_3754]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_4276,plain,
% 19.33/2.99      ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_32 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(demodulation,[status(thm)],[c_4261,c_1663]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_1792,plain,
% 19.33/2.99      ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_5539,plain,
% 19.33/2.99      ( arAF0_k1_enumset1_0 = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_26 != iProver_top ),
% 19.33/2.99      inference(global_propositional_subsumption,[status(thm)],[c_4276,c_1792]) ).
% 19.33/2.99  
% 19.33/2.99  cnf(c_1766,plain,
% 19.33/2.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k5_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k5_enumset1_0
% 19.33/2.99      | iProver_ARSWP_33 != iProver_top
% 19.33/2.99      | iProver_ARSWP_27 != iProver_top ),
% 19.33/2.99      inference(superposition,[status(thm)],[c_1509,c_1515]) ).
% 19.33/2.99  
% 19.33/2.99  
% 19.33/2.99  % SZS output end Saturation for theBenchmark.p
% 19.33/2.99  
% 19.33/2.99  ------                               Statistics
% 19.33/2.99  
% 19.33/2.99  ------ Selected
% 19.33/2.99  
% 19.33/2.99  total_time:                             2.113
% 19.33/2.99  
%------------------------------------------------------------------------------
