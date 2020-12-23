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
% DateTime   : Thu Dec  3 11:29:59 EST 2020

% Result     : CounterSatisfiable 27.54s
% Output     : Saturation 27.54s
% Verified   : 
% Statistics : Number of formulae       :  448 (64984 expanded)
%              Number of clauses        :  384 (15864 expanded)
%              Number of leaves         :   27 (19638 expanded)
%              Depth                    :   21
%              Number of atoms          : 1814 (107413 expanded)
%              Number of equality atoms : 1773 (104263 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    6 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f45,f37,f60,f51])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f29,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f32])).

fof(f58,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f73,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X1,X1,X0),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f59,f51,f51])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f43,f59,f60])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k1_enumset1(X8,X8,X8),k3_xboole_0(k1_enumset1(X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f44,f59,f60,f64])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f47,f59,f60,f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f49,f59,f56,f60])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f57,f60,f60,f60])).

cnf(c_58,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_51,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( X0 = X1
    | X2 = X0
    | k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1210,plain,
    ( ~ iProver_ARSWP_30
    | X0 = X1
    | X2 = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1316,plain,
    ( X0 = X1
    | X2 = X0
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_64,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_72,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_65,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_273,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_274,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_1396,plain,
    ( ~ iProver_ARSWP_30
    | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1397,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = X0
    | sK1 = sK2
    | iProver_ARSWP_30 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1399,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | sK2 = sK1
    | sK1 = sK2
    | iProver_ARSWP_30 != iProver_top ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1757,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_14,c_72,c_274,c_1399])).

cnf(c_13,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1212,plain,
    ( ~ iProver_ARSWP_32
    | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_1314,plain,
    ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X1)))) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1206,plain,
    ( ~ iProver_ARSWP_26
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1320,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_26 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_1920,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1320])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1938,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1920,c_6])).

cnf(c_9,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k1_enumset1(X8,X8,X8),k3_xboole_0(k1_enumset1(X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1209,plain,
    ( ~ iProver_ARSWP_29
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_1317,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_29 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_2887,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1317])).

cnf(c_20219,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_2887])).

cnf(c_40127,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_20219])).

cnf(c_66221,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_40127])).

cnf(c_86212,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_66221])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1207,plain,
    ( ~ iProver_ARSWP_27
    | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1319,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_27 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1610,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1319])).

cnf(c_6487,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1610])).

cnf(c_6507,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_6487,c_6])).

cnf(c_6901,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_1314])).

cnf(c_6892,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_1317])).

cnf(c_37970,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_6892])).

cnf(c_65716,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_37970])).

cnf(c_85299,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_65716])).

cnf(c_12,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1211,plain,
    ( ~ iProver_ARSWP_31
    | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_12])).

cnf(c_1315,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_1491,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1315])).

cnf(c_4498,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1491])).

cnf(c_4522,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_4498,c_6])).

cnf(c_4548,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_1314])).

cnf(c_4539,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_1317])).

cnf(c_34571,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_4539])).

cnf(c_63704,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_34571])).

cnf(c_84463,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_63704])).

cnf(c_20218,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_2887])).

cnf(c_78994,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_20218])).

cnf(c_79066,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_78994,c_6])).

cnf(c_20223,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_2887])).

cnf(c_79002,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_20218,c_20223])).

cnf(c_6955,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_1317])).

cnf(c_62996,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_6955])).

cnf(c_76899,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_62996,c_2887])).

cnf(c_20217,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_2887])).

cnf(c_76077,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_20217])).

cnf(c_76153,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_76077,c_6])).

cnf(c_76078,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_20217])).

cnf(c_20221,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_2887])).

cnf(c_76088,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_20217,c_20221])).

cnf(c_4818,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_1757])).

cnf(c_2888,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1317])).

cnf(c_21104,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_2888])).

cnf(c_32680,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_21104])).

cnf(c_74095,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_32680])).

cnf(c_6963,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_1757])).

cnf(c_21102,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_2888])).

cnf(c_29974,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_21102])).

cnf(c_72948,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_29974])).

cnf(c_40124,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_20219])).

cnf(c_40194,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_40124,c_6])).

cnf(c_21100,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_2888])).

cnf(c_40942,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_40194,c_21100])).

cnf(c_47714,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_40942])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_47853,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_47714,c_5])).

cnf(c_48846,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_1317])).

cnf(c_71964,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_48846])).

cnf(c_71962,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_48846])).

cnf(c_71978,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_48846,c_2887])).

cnf(c_2889,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1317])).

cnf(c_48811,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_2889])).

cnf(c_71354,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_48811,c_2887])).

cnf(c_48808,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_2887])).

cnf(c_69781,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_48808])).

cnf(c_69854,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_69781,c_6])).

cnf(c_69784,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_48808])).

cnf(c_69804,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_48808,c_1320])).

cnf(c_69790,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_48808,c_20219])).

cnf(c_2066,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1757])).

cnf(c_48803,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_21100])).

cnf(c_52823,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_48803])).

cnf(c_67351,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_52823])).

cnf(c_67388,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(demodulation,[status(thm)],[c_67351,c_5])).

cnf(c_40142,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_20219,c_1320])).

cnf(c_67278,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_40142])).

cnf(c_4810,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_1317])).

cnf(c_43674,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_4810])).

cnf(c_66270,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_43674])).

cnf(c_66287,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_43674,c_2887])).

cnf(c_53455,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_20221])).

cnf(c_53551,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_53455,c_6])).

cnf(c_65727,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_37970,c_53551])).

cnf(c_21109,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_2887])).

cnf(c_64436,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_21109])).

cnf(c_64471,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_64436,c_6])).

cnf(c_58087,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_20223])).

cnf(c_58180,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_58087,c_6])).

cnf(c_63713,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_34571,c_58180])).

cnf(c_63001,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_6955])).

cnf(c_6966,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_1319])).

cnf(c_61237,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_6966])).

cnf(c_6936,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_1610])).

cnf(c_60248,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_6936])).

cnf(c_58213,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_58180])).

cnf(c_58089,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_20223])).

cnf(c_54083,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_53551,c_21102])).

cnf(c_54161,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_54083])).

cnf(c_54065,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_53551])).

cnf(c_53456,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_20221])).

cnf(c_4822,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_1315])).

cnf(c_52909,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_4822])).

cnf(c_2064,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1320])).

cnf(c_52835,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_48803,c_2064])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1213,negated_conjecture,
    ( ~ iProver_ARSWP_33
    | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_15])).

cnf(c_1313,plain,
    ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1213])).

cnf(c_2891,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1317])).

cnf(c_2902,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2891,c_5,c_6])).

cnf(c_21114,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_2902])).

cnf(c_21108,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2888])).

cnf(c_21875,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21114,c_21108])).

cnf(c_1763,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1757])).

cnf(c_1774,plain,
    ( arAF0_k1_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1763,c_6])).

cnf(c_20226,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2887])).

cnf(c_22392,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_20226])).

cnf(c_25591,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_22392])).

cnf(c_20220,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2887])).

cnf(c_31258,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_25591,c_20220])).

cnf(c_50510,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_31258])).

cnf(c_50577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_50510])).

cnf(c_48805,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_2888])).

cnf(c_48741,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_40194])).

cnf(c_48732,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_47853,c_40942])).

cnf(c_47060,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_21104])).

cnf(c_47124,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_47060,c_6])).

cnf(c_47607,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_47124])).

cnf(c_2945,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2902])).

cnf(c_4268,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2945])).

cnf(c_5170,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_4268])).

cnf(c_5179,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_5170,c_5,c_6])).

cnf(c_2890,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1317])).

cnf(c_7623,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2890])).

cnf(c_8004,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_7623])).

cnf(c_8506,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_8004])).

cnf(c_19854,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8506])).

cnf(c_8504,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8004])).

cnf(c_19959,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_19854,c_8504])).

cnf(c_46246,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_19959])).

cnf(c_46994,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_46246])).

cnf(c_21886,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_21108])).

cnf(c_21908,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_21886,c_5])).

cnf(c_7620,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2890])).

cnf(c_42967,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_7620])).

cnf(c_43027,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_42967])).

cnf(c_23137,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_20226])).

cnf(c_31255,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_25591,c_23137])).

cnf(c_44939,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_43027,c_31255])).

cnf(c_43677,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_4810])).

cnf(c_43037,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_42967])).

cnf(c_43095,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_43037,c_5,c_6])).

cnf(c_43041,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_42967])).

cnf(c_43057,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_43041,c_5])).

cnf(c_43030,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21114,c_42967])).

cnf(c_43028,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_42967])).

cnf(c_42965,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_7620])).

cnf(c_7616,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_2890])).

cnf(c_39587,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_7616])).

cnf(c_41032,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_39587])).

cnf(c_40934,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_40194])).

cnf(c_39582,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_7616])).

cnf(c_39593,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_7616,c_2887])).

cnf(c_5773,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_1317])).

cnf(c_35422,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_5773])).

cnf(c_35521,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_35422])).

cnf(c_36162,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_35521,c_31255])).

cnf(c_21882,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_21108])).

cnf(c_21950,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_21882,c_5,c_6])).

cnf(c_35415,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_5773])).

cnf(c_36761,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_35415])).

cnf(c_36821,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21950,c_36761])).

cnf(c_38585,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_36162,c_36821])).

cnf(c_37966,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_6892])).

cnf(c_37979,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6892,c_2887])).

cnf(c_37978,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6892,c_2888])).

cnf(c_36823,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_36761])).

cnf(c_27641,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_23137])).

cnf(c_36164,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_35521,c_27641])).

cnf(c_35522,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_35422])).

cnf(c_35417,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_5773])).

cnf(c_35428,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5773,c_8004])).

cnf(c_35425,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5773,c_2887])).

cnf(c_34566,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_4539])).

cnf(c_34578,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4539,c_2887])).

cnf(c_34577,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4539,c_2888])).

cnf(c_2947,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2902])).

cnf(c_3524,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2947])).

cnf(c_3529,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_3524,c_5])).

cnf(c_4234,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_3529])).

cnf(c_19723,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_8504])).

cnf(c_33978,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_19723])).

cnf(c_34035,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_33978])).

cnf(c_33977,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_19723])).

cnf(c_8000,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_7623])).

cnf(c_8115,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_8000])).

cnf(c_8402,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8115])).

cnf(c_8410,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8402,c_5])).

cnf(c_8398,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_8115])).

cnf(c_8448,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8398,c_5,c_6])).

cnf(c_10263,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_8410,c_8448])).

cnf(c_31253,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_25591])).

cnf(c_33294,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_10263,c_31253])).

cnf(c_8511,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_8004])).

cnf(c_8809,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8511])).

cnf(c_8818,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8809,c_5])).

cnf(c_19733,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_8504,c_8818])).

cnf(c_29617,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_19733])).

cnf(c_30557,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_29617])).

cnf(c_29616,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_19733])).

cnf(c_20482,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_20226])).

cnf(c_20494,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_20482,c_5])).

cnf(c_27646,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_23137,c_20494])).

cnf(c_29263,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_27646])).

cnf(c_21309,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21114,c_20226])).

cnf(c_27644,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_23137,c_21309])).

cnf(c_29182,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_27644])).

cnf(c_20478,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_20226])).

cnf(c_20531,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_20478,c_5,c_6])).

cnf(c_27647,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_23137,c_20531])).

cnf(c_27645,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_23137,c_20220])).

cnf(c_8805,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_8511])).

cnf(c_8856,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8805,c_5,c_6])).

cnf(c_19735,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_8504,c_8856])).

cnf(c_27005,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_19735])).

cnf(c_27049,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_27005])).

cnf(c_27048,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_27005])).

cnf(c_27004,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_19735])).

cnf(c_22398,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_8511])).

cnf(c_25954,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_22398])).

cnf(c_8108,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8000])).

cnf(c_14715,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_8108])).

cnf(c_23501,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21950,c_14715])).

cnf(c_23146,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_2947])).

cnf(c_23144,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_8115])).

cnf(c_23143,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_8511])).

cnf(c_23140,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_14715])).

cnf(c_15173,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_7623])).

cnf(c_15205,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_15173,c_6])).

cnf(c_16063,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_15205])).

cnf(c_23139,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_16063])).

cnf(c_16056,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_15205])).

cnf(c_16426,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_16056])).

cnf(c_23138,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_16426])).

cnf(c_23134,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_21108])).

cnf(c_23132,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21908,c_21875])).

cnf(c_2892,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1315])).

cnf(c_23056,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_2892])).

cnf(c_23055,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_2892])).

cnf(c_21101,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2888])).

cnf(c_21591,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_21101])).

cnf(c_22388,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_21591])).

cnf(c_22845,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_22388])).

cnf(c_22847,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_22388])).

cnf(c_22884,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_22847,c_5])).

cnf(c_22400,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_4268])).

cnf(c_22595,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_22400])).

cnf(c_22401,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_2947])).

cnf(c_22399,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_8115])).

cnf(c_22395,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_14715])).

cnf(c_22394,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_16063])).

cnf(c_22393,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_16426])).

cnf(c_22389,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21875,c_21108])).

cnf(c_21590,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_21101])).

cnf(c_21586,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_21101])).

cnf(c_21479,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_21100])).

cnf(c_21317,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21114,c_2947])).

cnf(c_21314,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_21114,c_8511])).

cnf(c_21103,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_2888])).

cnf(c_21099,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_2888])).

cnf(c_21098,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6901,c_2888])).

cnf(c_21115,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_1319])).

cnf(c_21113,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_8000])).

cnf(c_21112,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_8004])).

cnf(c_21110,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_15205])).

cnf(c_1764,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1315])).

cnf(c_20472,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_20226])).

cnf(c_20222,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_2887])).

cnf(c_19950,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_19854])).

cnf(c_19963,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_19854,c_8856])).

cnf(c_19961,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_19854,c_8818])).

cnf(c_18885,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2889])).

cnf(c_1784,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1757])).

cnf(c_2113,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1784])).

cnf(c_8394,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_8115])).

cnf(c_15172,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_8394])).

cnf(c_16945,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_15172])).

cnf(c_16064,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_15205,c_8004])).

cnf(c_16877,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_16064])).

cnf(c_16425,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_16056])).

cnf(c_16421,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_16056])).

cnf(c_16062,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_15205])).

cnf(c_16058,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_15205])).

cnf(c_5771,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_2947])).

cnf(c_15174,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_5771])).

cnf(c_15170,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_8856])).

cnf(c_15167,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_8818])).

cnf(c_14714,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_8108])).

cnf(c_14710,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_8108])).

cnf(c_1788,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1315])).

cnf(c_2479,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1788])).

cnf(c_2671,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2479])).

cnf(c_2707,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2671])).

cnf(c_2713,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2707,c_5])).

cnf(c_3244,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_2479])).

cnf(c_3850,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_3244])).

cnf(c_8005,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_7623])).

cnf(c_8043,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8005,c_6])).

cnf(c_12408,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_8043])).

cnf(c_1611,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1319])).

cnf(c_1785,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1611])).

cnf(c_1809,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_1785,c_5])).

cnf(c_1914,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1809])).

cnf(c_1787,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1319])).

cnf(c_2288,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1787])).

cnf(c_2457,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2288])).

cnf(c_2465,plain,
    ( arAF0_k6_enumset1_0 = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(demodulation,[status(thm)],[c_2457,c_5,c_6])).

cnf(c_3150,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_1611])).

cnf(c_11986,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_3150])).

cnf(c_4778,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_2064])).

cnf(c_11984,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_4778])).

cnf(c_9194,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_8511])).

cnf(c_11214,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_9194])).

cnf(c_11226,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_11214,c_5])).

cnf(c_10257,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_8410])).

cnf(c_8883,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_8394])).

cnf(c_8892,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(demodulation,[status(thm)],[c_8883,c_5])).

cnf(c_10262,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_8410,c_8892])).

cnf(c_9719,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_8892])).

cnf(c_9678,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_8856])).

cnf(c_9199,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_1611])).

cnf(c_9197,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_2947])).

cnf(c_8510,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_8004])).

cnf(c_8114,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_8000])).

cnf(c_8110,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_8000])).

cnf(c_4547,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_1315])).

cnf(c_7290,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_4547])).

cnf(c_6899,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_6507,c_1319])).

cnf(c_5772,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_2902])).

cnf(c_5767,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_4268])).

cnf(c_2946,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2902])).

cnf(c_5734,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_2946])).

cnf(c_5424,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_4778])).

cnf(c_4800,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_1491])).

cnf(c_4776,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_2064])).

cnf(c_4267,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_29 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_2945])).

cnf(c_3876,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_2671])).

cnf(c_3873,plain,
    ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_3244])).

cnf(c_3147,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_2288])).

cnf(c_2477,plain,
    ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1788])).

cnf(c_2287,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1787])).

cnf(c_2070,plain,
    ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_31 != iProver_top
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1315])).

cnf(c_2069,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
    | iProver_ARSWP_30 != iProver_top
    | iProver_ARSWP_27 != iProver_top
    | iProver_ARSWP_26 != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1319])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:43:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 27.54/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.54/3.99  
% 27.54/3.99  ------  iProver source info
% 27.54/3.99  
% 27.54/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.54/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.54/3.99  git: non_committed_changes: false
% 27.54/3.99  git: last_make_outside_of_git: false
% 27.54/3.99  
% 27.54/3.99  ------ 
% 27.54/3.99  ------ Parsing...
% 27.54/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  ------ Proving...
% 27.54/3.99  ------ Problem Properties 
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  clauses                                 13
% 27.54/3.99  conjectures                             2
% 27.54/3.99  EPR                                     1
% 27.54/3.99  Horn                                    12
% 27.54/3.99  unary                                   12
% 27.54/3.99  binary                                  0
% 27.54/3.99  lits                                    15
% 27.54/3.99  lits eq                                 15
% 27.54/3.99  fd_pure                                 0
% 27.54/3.99  fd_pseudo                               0
% 27.54/3.99  fd_cond                                 0
% 27.54/3.99  fd_pseudo_cond                          1
% 27.54/3.99  AC symbols                              0
% 27.54/3.99  
% 27.54/3.99  ------ Input Options Time Limit: Unbounded
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 27.54/3.99  Current options:
% 27.54/3.99  ------ 
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  % SZS status CounterSatisfiable for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  % SZS output start Saturation for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  fof(f3,axiom,(
% 27.54/3.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f36,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f3])).
% 27.54/3.99  
% 27.54/3.99  fof(f2,axiom,(
% 27.54/3.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f26,plain,(
% 27.54/3.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(rectify,[],[f2])).
% 27.54/3.99  
% 27.54/3.99  fof(f27,plain,(
% 27.54/3.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(ennf_transformation,[],[f26])).
% 27.54/3.99  
% 27.54/3.99  fof(f30,plain,(
% 27.54/3.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 27.54/3.99    introduced(choice_axiom,[])).
% 27.54/3.99  
% 27.54/3.99  fof(f31,plain,(
% 27.54/3.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f30])).
% 27.54/3.99  
% 27.54/3.99  fof(f34,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f31])).
% 27.54/3.99  
% 27.54/3.99  fof(f35,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f31])).
% 27.54/3.99  
% 27.54/3.99  fof(f12,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f28,plain,(
% 27.54/3.99    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 27.54/3.99    inference(ennf_transformation,[],[f12])).
% 27.54/3.99  
% 27.54/3.99  fof(f45,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1) )),
% 27.54/3.99    inference(cnf_transformation,[],[f28])).
% 27.54/3.99  
% 27.54/3.99  fof(f4,axiom,(
% 27.54/3.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f37,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f4])).
% 27.54/3.99  
% 27.54/3.99  fof(f17,axiom,(
% 27.54/3.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f50,plain,(
% 27.54/3.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f17])).
% 27.54/3.99  
% 27.54/3.99  fof(f60,plain,(
% 27.54/3.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f50,f51])).
% 27.54/3.99  
% 27.54/3.99  fof(f18,axiom,(
% 27.54/3.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f51,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f18])).
% 27.54/3.99  
% 27.54/3.99  fof(f70,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 27.54/3.99    inference(definition_unfolding,[],[f45,f37,f60,f51])).
% 27.54/3.99  
% 27.54/3.99  fof(f24,conjecture,(
% 27.54/3.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f25,negated_conjecture,(
% 27.54/3.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 27.54/3.99    inference(negated_conjecture,[],[f24])).
% 27.54/3.99  
% 27.54/3.99  fof(f29,plain,(
% 27.54/3.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 27.54/3.99    inference(ennf_transformation,[],[f25])).
% 27.54/3.99  
% 27.54/3.99  fof(f32,plain,(
% 27.54/3.99    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 27.54/3.99    introduced(choice_axiom,[])).
% 27.54/3.99  
% 27.54/3.99  fof(f33,plain,(
% 27.54/3.99    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 27.54/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f32])).
% 27.54/3.99  
% 27.54/3.99  fof(f58,plain,(
% 27.54/3.99    sK1 != sK2),
% 27.54/3.99    inference(cnf_transformation,[],[f33])).
% 27.54/3.99  
% 27.54/3.99  fof(f19,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f52,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f19])).
% 27.54/3.99  
% 27.54/3.99  fof(f20,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f53,plain,(
% 27.54/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f20])).
% 27.54/3.99  
% 27.54/3.99  fof(f21,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f54,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f21])).
% 27.54/3.99  
% 27.54/3.99  fof(f22,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f55,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f22])).
% 27.54/3.99  
% 27.54/3.99  fof(f23,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f56,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f23])).
% 27.54/3.99  
% 27.54/3.99  fof(f61,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f55,f56])).
% 27.54/3.99  
% 27.54/3.99  fof(f62,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f54,f61])).
% 27.54/3.99  
% 27.54/3.99  fof(f63,plain,(
% 27.54/3.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f53,f62])).
% 27.54/3.99  
% 27.54/3.99  fof(f73,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f52,f63])).
% 27.54/3.99  
% 27.54/3.99  fof(f13,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f46,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f13])).
% 27.54/3.99  
% 27.54/3.99  fof(f7,axiom,(
% 27.54/3.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f40,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f7])).
% 27.54/3.99  
% 27.54/3.99  fof(f59,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f40,f37])).
% 27.54/3.99  
% 27.54/3.99  fof(f65,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X1,X1,X0),k5_xboole_0(k1_enumset1(X2,X2,X0),k3_xboole_0(k1_enumset1(X2,X2,X0),k1_enumset1(X1,X1,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f46,f59,f51,f51])).
% 27.54/3.99  
% 27.54/3.99  fof(f6,axiom,(
% 27.54/3.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f39,plain,(
% 27.54/3.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.54/3.99    inference(cnf_transformation,[],[f6])).
% 27.54/3.99  
% 27.54/3.99  fof(f11,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f44,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f11])).
% 27.54/3.99  
% 27.54/3.99  fof(f10,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f43,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f10])).
% 27.54/3.99  
% 27.54/3.99  fof(f64,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f43,f59,f60])).
% 27.54/3.99  
% 27.54/3.99  fof(f69,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k1_enumset1(X8,X8,X8),k3_xboole_0(k1_enumset1(X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))))) )),
% 27.54/3.99    inference(definition_unfolding,[],[f44,f59,f60,f64])).
% 27.54/3.99  
% 27.54/3.99  fof(f14,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f47,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f14])).
% 27.54/3.99  
% 27.54/3.99  fof(f66,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f47,f59,f60,f56])).
% 27.54/3.99  
% 27.54/3.99  fof(f16,axiom,(
% 27.54/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f49,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f16])).
% 27.54/3.99  
% 27.54/3.99  fof(f72,plain,(
% 27.54/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f49,f59,f56,f60])).
% 27.54/3.99  
% 27.54/3.99  fof(f5,axiom,(
% 27.54/3.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f38,plain,(
% 27.54/3.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.54/3.99    inference(cnf_transformation,[],[f5])).
% 27.54/3.99  
% 27.54/3.99  fof(f57,plain,(
% 27.54/3.99    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 27.54/3.99    inference(cnf_transformation,[],[f33])).
% 27.54/3.99  
% 27.54/3.99  fof(f74,plain,(
% 27.54/3.99    k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1)),
% 27.54/3.99    inference(definition_unfolding,[],[f57,f60,f60,f60])).
% 27.54/3.99  
% 27.54/3.99  cnf(c_58,plain,
% 27.54/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.54/3.99      theory(equality) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_57,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.54/3.99      theory(equality) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_51,plain,( X0_2 = X0_2 ),theory(equality) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4,plain,
% 27.54/3.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 27.54/3.99      inference(cnf_transformation,[],[f36]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3,plain,
% 27.54/3.99      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 27.54/3.99      inference(cnf_transformation,[],[f34]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2,plain,
% 27.54/3.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 27.54/3.99      inference(cnf_transformation,[],[f35]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_10,plain,
% 27.54/3.99      ( X0 = X1
% 27.54/3.99      | X2 = X0
% 27.54/3.99      | k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))) = k1_enumset1(X1,X1,X2) ),
% 27.54/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1210,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_30
% 27.54/3.99      | X0 = X1
% 27.54/3.99      | X2 = X0
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1316,plain,
% 27.54/3.99      ( X0 = X1
% 27.54/3.99      | X2 = X0
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_14,negated_conjecture,
% 27.54/3.99      ( sK1 != sK2 ),
% 27.54/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_64,plain,( X0 = X0 ),theory(equality) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_72,plain,( sK1 = sK1 ),inference(instantiation,[status(thm)],[c_64]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_65,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_273,plain,
% 27.54/3.99      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_65]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_274,plain,
% 27.54/3.99      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_273]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1396,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_30
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | sK2 = X0
% 27.54/3.99      | sK1 = sK2 ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_1210]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1397,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | sK2 = X0
% 27.54/3.99      | sK1 = sK2
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1399,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | sK2 = sK1
% 27.54/3.99      | sK1 = sK2
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_1397]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1757,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(global_propositional_subsumption,
% 27.54/3.99                [status(thm)],
% 27.54/3.99                [c_1316,c_14,c_72,c_274,c_1399]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_13,plain,
% 27.54/3.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 27.54/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1212,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_32 | arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1314,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_0,plain,
% 27.54/3.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X1),k3_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X1)))) = k1_enumset1(X1,X0,X2) ),
% 27.54/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1206,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_26
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1320,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1920,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_1320]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6,plain,
% 27.54/3.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.54/3.99      inference(cnf_transformation,[],[f39]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1938,plain,
% 27.54/3.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_1920,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9,plain,
% 27.54/3.99      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k1_enumset1(X8,X8,X8),k3_xboole_0(k1_enumset1(X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
% 27.54/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1209,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_29
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1317,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2887,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20219,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40127,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_20219]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_66221,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_40127]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_86212,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_66221]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1,plain,
% 27.54/3.99      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_enumset1(X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 27.54/3.99      inference(cnf_transformation,[],[f66]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1207,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_27
% 27.54/3.99      | k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1319,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1610,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6487,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_1610]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6507,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_6487,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6901,plain,
% 27.54/3.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_1314]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6892,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_37970,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_6892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_65716,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_37970]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_85299,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_65716]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_12,plain,
% 27.54/3.99      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 27.54/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1211,plain,
% 27.54/3.99      ( ~ iProver_ARSWP_31
% 27.54/3.99      | k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_12]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1315,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1491,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4498,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_1491]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4522,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_4498,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4548,plain,
% 27.54/3.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_1314]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4539,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_34571,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_4539]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_63704,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_34571]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_84463,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_63704]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20218,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_78994,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_20218]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_79066,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_78994,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20223,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_79002,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_20218,c_20223]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6955,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_62996,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_6955]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_76899,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_62996,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20217,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_76077,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_20217]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_76153,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_76077,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_76078,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_20217]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20221,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_76088,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_20217,c_20221]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4818,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_1757]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2888,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21104,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_32680,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_21104]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_74095,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4818,c_32680]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6963,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_1757]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21102,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29974,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_21102]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_72948,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6963,c_29974]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40124,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_20219]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40194,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_40124,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21100,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40942,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_40194,c_21100]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_47714,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_40942]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5,plain,
% 27.54/3.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.54/3.99      inference(cnf_transformation,[],[f38]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_47853,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_47714,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48846,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_71964,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_48846]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_71962,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_48846]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_71978,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_48846,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2889,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48811,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_2889]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_71354,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_48811,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48808,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69781,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_48808]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69854,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_69781,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69784,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_48808]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69804,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_48808,c_1320]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69790,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_48808,c_20219]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2066,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_1757]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48803,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_21100]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_52823,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2066,c_48803]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_67351,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_52823]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_67388,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_67351,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40142,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_20219,c_1320]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_67278,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_40142]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4810,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43674,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_4810]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_66270,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_43674]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_66287,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_43674,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_53455,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_20221]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_53551,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_53455,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_65727,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_37970,c_53551]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21109,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_64436,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_21109]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_64471,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_64436,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_58087,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_20223]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_58180,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_58087,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_63713,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_34571,c_58180]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_63001,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_6955]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6966,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_61237,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_6966]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6936,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_1610]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_60248,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6963,c_6936]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_58213,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_58180]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_58089,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_20223]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_54083,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_53551,c_21102]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_54161,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_54083]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_54065,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_53551]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_53456,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_20221]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4822,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_52909,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_4822]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2064,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_1320]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_52835,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_48803,c_2064]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15,negated_conjecture,
% 27.54/3.99      ( k3_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(sK1,sK1,sK1) ),
% 27.54/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1213,negated_conjecture,
% 27.54/3.99      ( ~ iProver_ARSWP_33 | arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0 ),
% 27.54/3.99      inference(arg_filter_abstr,[status(unp)],[c_15]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1313,plain,
% 27.54/3.99      ( arAF0_k3_xboole_0_0 = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1213]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2891,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2902,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_2891,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21114,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_2902]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21108,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21875,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21114,c_21108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1763,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1757]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1774,plain,
% 27.54/3.99      ( arAF0_k1_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_1763,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20226,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22392,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_25591,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_22392]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20220,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_31258,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_25591,c_20220]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_50510,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_31258]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_50577,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_50510]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48805,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48741,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_40194]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_48732,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_47853,c_40942]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_47060,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4818,c_21104]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_47124,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_47060,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_47607,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_47124]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2945,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2902]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4268,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2945]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5170,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_4268]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5179,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_5170,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2890,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_7623,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2890]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8004,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_7623]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8506,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19854,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8506]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8504,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19959,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_19854,c_8504]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_46246,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_19959]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_46994,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_46246]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21886,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_21108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21908,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_21886,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_7620,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2890]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_42967,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_7620]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43027,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_42967]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23137,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_31255,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_25591,c_23137]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_44939,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_43027,c_31255]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43677,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_4810]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43037,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_42967]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43095,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_43037,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43041,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_42967]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43057,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_43041,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43030,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21114,c_42967]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_43028,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_42967]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_42965,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_7620]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_7616,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_2890]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_39587,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_7616]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_41032,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_39587]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_40934,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_40194]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_39582,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_7616]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_39593,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_7616,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5773,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_1317]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35422,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_5773]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35521,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_35422]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_36162,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_35521,c_31255]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21882,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_21108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21950,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_21882,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35415,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_5773]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_36761,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_35415]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_36821,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21950,c_36761]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_38585,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_36162,c_36821]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_37966,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_6892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_37979,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6892,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_37978,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6892,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_36823,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_36761]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27641,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_23137]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_36164,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_35521,c_27641]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35522,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_35422]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35417,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_5773]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35428,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5773,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35425,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5773,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_34566,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_4539]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_34578,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4539,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_34577,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4539,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2947,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2902]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3524,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3529,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_3524,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4234,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_3529]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19723,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_8504]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_33978,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_19723]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_34035,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_33978]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_33977,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_19723]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8000,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_7623]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8115,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_8000]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8402,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8115]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8410,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8402,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8398,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_8115]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8448,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8398,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_10263,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_8410,c_8448]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_31253,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_25591]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_33294,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_10263,c_31253]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8511,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8809,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8818,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8809,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19733,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_8504,c_8818]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29617,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_19733]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_30557,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_29617]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29616,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_19733]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20482,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20494,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_20482,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27646,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_23137,c_20494]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29263,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_27646]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21309,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21114,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27644,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_23137,c_21309]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29182,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_27644]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20478,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20531,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_20478,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27647,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_23137,c_20531]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27645,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_23137,c_20220]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8805,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8856,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8805,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19735,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_8504,c_8856]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27005,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_19735]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27049,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_27005]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27048,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_27005]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_27004,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_19735]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22398,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_25954,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_22398]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8108,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8000]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_14715,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_8108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23501,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21950,c_14715]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23146,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23144,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_8115]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23143,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23140,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_14715]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15173,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_7623]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15205,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_15173,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16063,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_15205]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23139,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_16063]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16056,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_15205]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16426,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_16056]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23138,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_16426]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23134,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_21108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23132,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21908,c_21875]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2892,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1317,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23056,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_2892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_23055,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_2892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21101,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21591,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_21101]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22388,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_21591]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22845,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_22388]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22847,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,k1_xboole_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_22388]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22884,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_22847,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22400,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_4268]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22595,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_22400]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22401,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22399,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_8115]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22395,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_14715]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22394,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_16063]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22393,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_16426]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22389,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21875,c_21108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21590,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_21101]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21586,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_21101]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21479,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_21100]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21317,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21114,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21314,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_21114,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21103,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21099,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21098,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6901,c_2888]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21115,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21113,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_8000]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21112,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21110,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2888,c_15205]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1764,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20472,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1764,c_20226]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20222,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_2887]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19950,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_19854]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19963,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_19854,c_8856]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19961,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_19854,c_8818]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_18885,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2889]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1784,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_1757]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2113,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1784]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8394,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_8115]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15172,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_8394]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16945,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2113,c_15172]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16064,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_15205,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16877,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_16064]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16425,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_16056]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16421,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_16056]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16062,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_15205]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16058,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_15205]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5771,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15174,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_5771]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15170,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_8856]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_15167,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4234,c_8818]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_14714,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_8108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_14710,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_8108]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1788,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2479,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1788]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2671,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2479]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2707,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2671]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2713,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_2707,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3244,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2713,c_2479]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3850,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2113,c_3244]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8005,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_3850,c_7623]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8043,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8005,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_12408,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_8043]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1611,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1785,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,k1_xboole_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_1611]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1809,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_1785,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1914,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1809]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1787,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2288,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_1787]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2457,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2288]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2465,plain,
% 27.54/3.99      ( arAF0_k6_enumset1_0 = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_2457,c_5,c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3150,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2465,c_1611]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_11986,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1914,c_3150]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4778,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1313,c_2064]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_11984,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1914,c_4778]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9194,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1764,c_8511]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_11214,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_9194]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_11226,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_11214,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_10257,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0)
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2113,c_8410]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8883,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_8394]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8892,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(demodulation,[status(thm)],[c_8883,c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_10262,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_8410,c_8892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9719,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = k1_xboole_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2113,c_8892]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9678,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_3850,c_8856]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9199,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1764,c_1611]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9197,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1764,c_2947]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8510,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_8004]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8114,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_8000]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8110,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0))
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_8000]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4547,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4522,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_7290,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1757,c_4547]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6899,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_6507,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5772,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_2902]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5767,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_5179,c_4268]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2946,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2902]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5734,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1774,c_2946]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5424,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_3850,c_4778]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4800,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_4548,c_1491]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4776,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0) = arAF0_k1_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2066,c_2064]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4267,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_29 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_2945]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3876,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_3850,c_2671]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3873,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,arAF0_k6_enumset1_0) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_3850,c_3244]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3147,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,arAF0_k1_enumset1_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_2465,c_2288]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2477,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k1_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1788]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2287,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k1_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_33 != iProver_top
% 27.54/3.99      | iProver_ARSWP_32 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1314,c_1787]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2070,plain,
% 27.54/3.99      ( k5_xboole_0(arAF0_k6_enumset1_0,k5_xboole_0(k1_xboole_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_31 != iProver_top
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_1315]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_2069,plain,
% 27.54/3.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(arAF0_k6_enumset1_0,arAF0_k3_xboole_0_0)) = arAF0_k6_enumset1_0
% 27.54/3.99      | iProver_ARSWP_30 != iProver_top
% 27.54/3.99      | iProver_ARSWP_27 != iProver_top
% 27.54/3.99      | iProver_ARSWP_26 != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_1938,c_1319]) ).
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  % SZS output end Saturation for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  ------                               Statistics
% 27.54/3.99  
% 27.54/3.99  ------ Selected
% 27.54/3.99  
% 27.54/3.99  total_time:                             3.063
% 27.54/3.99  
%------------------------------------------------------------------------------
