%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:33 EST 2020

% Result     : Theorem 31.47s
% Output     : CNFRefutation 31.47s
% Verified   : 
% Statistics : Number of formulae       :  145 (1385 expanded)
%              Number of clauses        :   62 ( 192 expanded)
%              Number of leaves         :   25 ( 403 expanded)
%              Depth                    :   25
%              Number of atoms          :  273 (2169 expanded)
%              Number of equality atoms :  174 (1710 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f37])).

fof(f67,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f91,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f67,f76,f78])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f77])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f77])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f68,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_820,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_822,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9828,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_822])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_826,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_59744,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9828,c_826])).

cnf(c_59935,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_59744])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_47,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_821,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_823,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12126,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9828,c_823])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_467,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_862,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_890,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_885,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_950,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_1022,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_14966,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12126,c_20,c_890,c_950,c_1022])).

cnf(c_14972,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_14966])).

cnf(c_14974,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14972])).

cnf(c_59939,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59935,c_47,c_14974])).

cnf(c_59947,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_59939,c_22])).

cnf(c_59957,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59939,c_821])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_818,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_59960,plain,
    ( r2_hidden(sK0,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59939,c_818])).

cnf(c_69938,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59957,c_59960])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_824,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_70442,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_69938,c_824])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_463,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_10,c_0])).

cnf(c_827,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_83423,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_70442,c_827])).

cnf(c_108177,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_59947,c_83423])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1164,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_1162,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_462,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_10,c_0])).

cnf(c_13,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_829,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_462,c_11,c_13])).

cnf(c_1095,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_829,c_0])).

cnf(c_1168,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1162,c_1095])).

cnf(c_1342,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1164,c_1168])).

cnf(c_1351,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1342,c_829])).

cnf(c_108848,plain,
    ( sK1 = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_108177,c_1351,c_59947])).

cnf(c_21,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_108975,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_108848,c_21])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_108980,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_108975,c_19])).

cnf(c_108981,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_108980])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.47/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.47/4.50  
% 31.47/4.50  ------  iProver source info
% 31.47/4.50  
% 31.47/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.47/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.47/4.50  git: non_committed_changes: false
% 31.47/4.50  git: last_make_outside_of_git: false
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options
% 31.47/4.50  
% 31.47/4.50  --out_options                           all
% 31.47/4.50  --tptp_safe_out                         true
% 31.47/4.50  --problem_path                          ""
% 31.47/4.50  --include_path                          ""
% 31.47/4.50  --clausifier                            res/vclausify_rel
% 31.47/4.50  --clausifier_options                    ""
% 31.47/4.50  --stdin                                 false
% 31.47/4.50  --stats_out                             all
% 31.47/4.50  
% 31.47/4.50  ------ General Options
% 31.47/4.50  
% 31.47/4.50  --fof                                   false
% 31.47/4.50  --time_out_real                         305.
% 31.47/4.50  --time_out_virtual                      -1.
% 31.47/4.50  --symbol_type_check                     false
% 31.47/4.50  --clausify_out                          false
% 31.47/4.50  --sig_cnt_out                           false
% 31.47/4.50  --trig_cnt_out                          false
% 31.47/4.50  --trig_cnt_out_tolerance                1.
% 31.47/4.50  --trig_cnt_out_sk_spl                   false
% 31.47/4.50  --abstr_cl_out                          false
% 31.47/4.50  
% 31.47/4.50  ------ Global Options
% 31.47/4.50  
% 31.47/4.50  --schedule                              default
% 31.47/4.50  --add_important_lit                     false
% 31.47/4.50  --prop_solver_per_cl                    1000
% 31.47/4.50  --min_unsat_core                        false
% 31.47/4.50  --soft_assumptions                      false
% 31.47/4.50  --soft_lemma_size                       3
% 31.47/4.50  --prop_impl_unit_size                   0
% 31.47/4.50  --prop_impl_unit                        []
% 31.47/4.50  --share_sel_clauses                     true
% 31.47/4.50  --reset_solvers                         false
% 31.47/4.50  --bc_imp_inh                            [conj_cone]
% 31.47/4.50  --conj_cone_tolerance                   3.
% 31.47/4.50  --extra_neg_conj                        none
% 31.47/4.50  --large_theory_mode                     true
% 31.47/4.50  --prolific_symb_bound                   200
% 31.47/4.50  --lt_threshold                          2000
% 31.47/4.50  --clause_weak_htbl                      true
% 31.47/4.50  --gc_record_bc_elim                     false
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing Options
% 31.47/4.50  
% 31.47/4.50  --preprocessing_flag                    true
% 31.47/4.50  --time_out_prep_mult                    0.1
% 31.47/4.50  --splitting_mode                        input
% 31.47/4.50  --splitting_grd                         true
% 31.47/4.50  --splitting_cvd                         false
% 31.47/4.50  --splitting_cvd_svl                     false
% 31.47/4.50  --splitting_nvd                         32
% 31.47/4.50  --sub_typing                            true
% 31.47/4.50  --prep_gs_sim                           true
% 31.47/4.50  --prep_unflatten                        true
% 31.47/4.50  --prep_res_sim                          true
% 31.47/4.50  --prep_upred                            true
% 31.47/4.50  --prep_sem_filter                       exhaustive
% 31.47/4.50  --prep_sem_filter_out                   false
% 31.47/4.50  --pred_elim                             true
% 31.47/4.50  --res_sim_input                         true
% 31.47/4.50  --eq_ax_congr_red                       true
% 31.47/4.50  --pure_diseq_elim                       true
% 31.47/4.50  --brand_transform                       false
% 31.47/4.50  --non_eq_to_eq                          false
% 31.47/4.50  --prep_def_merge                        true
% 31.47/4.50  --prep_def_merge_prop_impl              false
% 31.47/4.50  --prep_def_merge_mbd                    true
% 31.47/4.50  --prep_def_merge_tr_red                 false
% 31.47/4.50  --prep_def_merge_tr_cl                  false
% 31.47/4.50  --smt_preprocessing                     true
% 31.47/4.50  --smt_ac_axioms                         fast
% 31.47/4.50  --preprocessed_out                      false
% 31.47/4.50  --preprocessed_stats                    false
% 31.47/4.50  
% 31.47/4.50  ------ Abstraction refinement Options
% 31.47/4.50  
% 31.47/4.50  --abstr_ref                             []
% 31.47/4.50  --abstr_ref_prep                        false
% 31.47/4.50  --abstr_ref_until_sat                   false
% 31.47/4.50  --abstr_ref_sig_restrict                funpre
% 31.47/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.47/4.50  --abstr_ref_under                       []
% 31.47/4.50  
% 31.47/4.50  ------ SAT Options
% 31.47/4.50  
% 31.47/4.50  --sat_mode                              false
% 31.47/4.50  --sat_fm_restart_options                ""
% 31.47/4.50  --sat_gr_def                            false
% 31.47/4.50  --sat_epr_types                         true
% 31.47/4.50  --sat_non_cyclic_types                  false
% 31.47/4.50  --sat_finite_models                     false
% 31.47/4.50  --sat_fm_lemmas                         false
% 31.47/4.50  --sat_fm_prep                           false
% 31.47/4.50  --sat_fm_uc_incr                        true
% 31.47/4.50  --sat_out_model                         small
% 31.47/4.50  --sat_out_clauses                       false
% 31.47/4.50  
% 31.47/4.50  ------ QBF Options
% 31.47/4.50  
% 31.47/4.50  --qbf_mode                              false
% 31.47/4.50  --qbf_elim_univ                         false
% 31.47/4.50  --qbf_dom_inst                          none
% 31.47/4.50  --qbf_dom_pre_inst                      false
% 31.47/4.50  --qbf_sk_in                             false
% 31.47/4.50  --qbf_pred_elim                         true
% 31.47/4.50  --qbf_split                             512
% 31.47/4.50  
% 31.47/4.50  ------ BMC1 Options
% 31.47/4.50  
% 31.47/4.50  --bmc1_incremental                      false
% 31.47/4.50  --bmc1_axioms                           reachable_all
% 31.47/4.50  --bmc1_min_bound                        0
% 31.47/4.50  --bmc1_max_bound                        -1
% 31.47/4.50  --bmc1_max_bound_default                -1
% 31.47/4.50  --bmc1_symbol_reachability              true
% 31.47/4.50  --bmc1_property_lemmas                  false
% 31.47/4.50  --bmc1_k_induction                      false
% 31.47/4.50  --bmc1_non_equiv_states                 false
% 31.47/4.50  --bmc1_deadlock                         false
% 31.47/4.50  --bmc1_ucm                              false
% 31.47/4.50  --bmc1_add_unsat_core                   none
% 31.47/4.50  --bmc1_unsat_core_children              false
% 31.47/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.47/4.50  --bmc1_out_stat                         full
% 31.47/4.50  --bmc1_ground_init                      false
% 31.47/4.50  --bmc1_pre_inst_next_state              false
% 31.47/4.50  --bmc1_pre_inst_state                   false
% 31.47/4.50  --bmc1_pre_inst_reach_state             false
% 31.47/4.50  --bmc1_out_unsat_core                   false
% 31.47/4.50  --bmc1_aig_witness_out                  false
% 31.47/4.50  --bmc1_verbose                          false
% 31.47/4.50  --bmc1_dump_clauses_tptp                false
% 31.47/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.47/4.50  --bmc1_dump_file                        -
% 31.47/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.47/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.47/4.50  --bmc1_ucm_extend_mode                  1
% 31.47/4.50  --bmc1_ucm_init_mode                    2
% 31.47/4.50  --bmc1_ucm_cone_mode                    none
% 31.47/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.47/4.50  --bmc1_ucm_relax_model                  4
% 31.47/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.47/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.47/4.50  --bmc1_ucm_layered_model                none
% 31.47/4.50  --bmc1_ucm_max_lemma_size               10
% 31.47/4.50  
% 31.47/4.50  ------ AIG Options
% 31.47/4.50  
% 31.47/4.50  --aig_mode                              false
% 31.47/4.50  
% 31.47/4.50  ------ Instantiation Options
% 31.47/4.50  
% 31.47/4.50  --instantiation_flag                    true
% 31.47/4.50  --inst_sos_flag                         true
% 31.47/4.50  --inst_sos_phase                        true
% 31.47/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel_side                     num_symb
% 31.47/4.50  --inst_solver_per_active                1400
% 31.47/4.50  --inst_solver_calls_frac                1.
% 31.47/4.50  --inst_passive_queue_type               priority_queues
% 31.47/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.47/4.50  --inst_passive_queues_freq              [25;2]
% 31.47/4.50  --inst_dismatching                      true
% 31.47/4.50  --inst_eager_unprocessed_to_passive     true
% 31.47/4.50  --inst_prop_sim_given                   true
% 31.47/4.50  --inst_prop_sim_new                     false
% 31.47/4.50  --inst_subs_new                         false
% 31.47/4.50  --inst_eq_res_simp                      false
% 31.47/4.50  --inst_subs_given                       false
% 31.47/4.50  --inst_orphan_elimination               true
% 31.47/4.50  --inst_learning_loop_flag               true
% 31.47/4.50  --inst_learning_start                   3000
% 31.47/4.50  --inst_learning_factor                  2
% 31.47/4.50  --inst_start_prop_sim_after_learn       3
% 31.47/4.50  --inst_sel_renew                        solver
% 31.47/4.50  --inst_lit_activity_flag                true
% 31.47/4.50  --inst_restr_to_given                   false
% 31.47/4.50  --inst_activity_threshold               500
% 31.47/4.50  --inst_out_proof                        true
% 31.47/4.50  
% 31.47/4.50  ------ Resolution Options
% 31.47/4.50  
% 31.47/4.50  --resolution_flag                       true
% 31.47/4.50  --res_lit_sel                           adaptive
% 31.47/4.50  --res_lit_sel_side                      none
% 31.47/4.50  --res_ordering                          kbo
% 31.47/4.50  --res_to_prop_solver                    active
% 31.47/4.50  --res_prop_simpl_new                    false
% 31.47/4.50  --res_prop_simpl_given                  true
% 31.47/4.50  --res_passive_queue_type                priority_queues
% 31.47/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.47/4.50  --res_passive_queues_freq               [15;5]
% 31.47/4.50  --res_forward_subs                      full
% 31.47/4.50  --res_backward_subs                     full
% 31.47/4.50  --res_forward_subs_resolution           true
% 31.47/4.50  --res_backward_subs_resolution          true
% 31.47/4.50  --res_orphan_elimination                true
% 31.47/4.50  --res_time_limit                        2.
% 31.47/4.50  --res_out_proof                         true
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Options
% 31.47/4.50  
% 31.47/4.50  --superposition_flag                    true
% 31.47/4.50  --sup_passive_queue_type                priority_queues
% 31.47/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.47/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.47/4.50  --demod_completeness_check              fast
% 31.47/4.50  --demod_use_ground                      true
% 31.47/4.50  --sup_to_prop_solver                    passive
% 31.47/4.50  --sup_prop_simpl_new                    true
% 31.47/4.50  --sup_prop_simpl_given                  true
% 31.47/4.50  --sup_fun_splitting                     true
% 31.47/4.50  --sup_smt_interval                      50000
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Simplification Setup
% 31.47/4.50  
% 31.47/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.47/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.47/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_immed_triv                        [TrivRules]
% 31.47/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_bw_main                     []
% 31.47/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.47/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_input_bw                          []
% 31.47/4.50  
% 31.47/4.50  ------ Combination Options
% 31.47/4.50  
% 31.47/4.50  --comb_res_mult                         3
% 31.47/4.50  --comb_sup_mult                         2
% 31.47/4.50  --comb_inst_mult                        10
% 31.47/4.50  
% 31.47/4.50  ------ Debug Options
% 31.47/4.50  
% 31.47/4.50  --dbg_backtrace                         false
% 31.47/4.50  --dbg_dump_prop_clauses                 false
% 31.47/4.50  --dbg_dump_prop_clauses_file            -
% 31.47/4.50  --dbg_out_stat                          false
% 31.47/4.50  ------ Parsing...
% 31.47/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.47/4.50  ------ Proving...
% 31.47/4.50  ------ Problem Properties 
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  clauses                                 22
% 31.47/4.50  conjectures                             4
% 31.47/4.50  EPR                                     6
% 31.47/4.50  Horn                                    21
% 31.47/4.50  unary                                   11
% 31.47/4.50  binary                                  8
% 31.47/4.50  lits                                    37
% 31.47/4.50  lits eq                                 14
% 31.47/4.50  fd_pure                                 0
% 31.47/4.50  fd_pseudo                               0
% 31.47/4.50  fd_cond                                 1
% 31.47/4.50  fd_pseudo_cond                          1
% 31.47/4.50  AC symbols                              1
% 31.47/4.50  
% 31.47/4.50  ------ Schedule dynamic 5 is on 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  Current options:
% 31.47/4.50  ------ 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options
% 31.47/4.50  
% 31.47/4.50  --out_options                           all
% 31.47/4.50  --tptp_safe_out                         true
% 31.47/4.50  --problem_path                          ""
% 31.47/4.50  --include_path                          ""
% 31.47/4.50  --clausifier                            res/vclausify_rel
% 31.47/4.50  --clausifier_options                    ""
% 31.47/4.50  --stdin                                 false
% 31.47/4.50  --stats_out                             all
% 31.47/4.50  
% 31.47/4.50  ------ General Options
% 31.47/4.50  
% 31.47/4.50  --fof                                   false
% 31.47/4.50  --time_out_real                         305.
% 31.47/4.50  --time_out_virtual                      -1.
% 31.47/4.50  --symbol_type_check                     false
% 31.47/4.50  --clausify_out                          false
% 31.47/4.50  --sig_cnt_out                           false
% 31.47/4.50  --trig_cnt_out                          false
% 31.47/4.50  --trig_cnt_out_tolerance                1.
% 31.47/4.50  --trig_cnt_out_sk_spl                   false
% 31.47/4.50  --abstr_cl_out                          false
% 31.47/4.50  
% 31.47/4.50  ------ Global Options
% 31.47/4.50  
% 31.47/4.50  --schedule                              default
% 31.47/4.50  --add_important_lit                     false
% 31.47/4.50  --prop_solver_per_cl                    1000
% 31.47/4.50  --min_unsat_core                        false
% 31.47/4.50  --soft_assumptions                      false
% 31.47/4.50  --soft_lemma_size                       3
% 31.47/4.50  --prop_impl_unit_size                   0
% 31.47/4.50  --prop_impl_unit                        []
% 31.47/4.50  --share_sel_clauses                     true
% 31.47/4.50  --reset_solvers                         false
% 31.47/4.50  --bc_imp_inh                            [conj_cone]
% 31.47/4.50  --conj_cone_tolerance                   3.
% 31.47/4.50  --extra_neg_conj                        none
% 31.47/4.50  --large_theory_mode                     true
% 31.47/4.50  --prolific_symb_bound                   200
% 31.47/4.50  --lt_threshold                          2000
% 31.47/4.50  --clause_weak_htbl                      true
% 31.47/4.50  --gc_record_bc_elim                     false
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing Options
% 31.47/4.50  
% 31.47/4.50  --preprocessing_flag                    true
% 31.47/4.50  --time_out_prep_mult                    0.1
% 31.47/4.50  --splitting_mode                        input
% 31.47/4.50  --splitting_grd                         true
% 31.47/4.50  --splitting_cvd                         false
% 31.47/4.50  --splitting_cvd_svl                     false
% 31.47/4.50  --splitting_nvd                         32
% 31.47/4.50  --sub_typing                            true
% 31.47/4.50  --prep_gs_sim                           true
% 31.47/4.50  --prep_unflatten                        true
% 31.47/4.50  --prep_res_sim                          true
% 31.47/4.50  --prep_upred                            true
% 31.47/4.50  --prep_sem_filter                       exhaustive
% 31.47/4.50  --prep_sem_filter_out                   false
% 31.47/4.50  --pred_elim                             true
% 31.47/4.50  --res_sim_input                         true
% 31.47/4.50  --eq_ax_congr_red                       true
% 31.47/4.50  --pure_diseq_elim                       true
% 31.47/4.50  --brand_transform                       false
% 31.47/4.50  --non_eq_to_eq                          false
% 31.47/4.50  --prep_def_merge                        true
% 31.47/4.50  --prep_def_merge_prop_impl              false
% 31.47/4.50  --prep_def_merge_mbd                    true
% 31.47/4.50  --prep_def_merge_tr_red                 false
% 31.47/4.50  --prep_def_merge_tr_cl                  false
% 31.47/4.50  --smt_preprocessing                     true
% 31.47/4.50  --smt_ac_axioms                         fast
% 31.47/4.50  --preprocessed_out                      false
% 31.47/4.50  --preprocessed_stats                    false
% 31.47/4.50  
% 31.47/4.50  ------ Abstraction refinement Options
% 31.47/4.50  
% 31.47/4.50  --abstr_ref                             []
% 31.47/4.50  --abstr_ref_prep                        false
% 31.47/4.50  --abstr_ref_until_sat                   false
% 31.47/4.50  --abstr_ref_sig_restrict                funpre
% 31.47/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.47/4.50  --abstr_ref_under                       []
% 31.47/4.50  
% 31.47/4.50  ------ SAT Options
% 31.47/4.50  
% 31.47/4.50  --sat_mode                              false
% 31.47/4.50  --sat_fm_restart_options                ""
% 31.47/4.50  --sat_gr_def                            false
% 31.47/4.50  --sat_epr_types                         true
% 31.47/4.50  --sat_non_cyclic_types                  false
% 31.47/4.50  --sat_finite_models                     false
% 31.47/4.50  --sat_fm_lemmas                         false
% 31.47/4.50  --sat_fm_prep                           false
% 31.47/4.50  --sat_fm_uc_incr                        true
% 31.47/4.50  --sat_out_model                         small
% 31.47/4.50  --sat_out_clauses                       false
% 31.47/4.50  
% 31.47/4.50  ------ QBF Options
% 31.47/4.50  
% 31.47/4.50  --qbf_mode                              false
% 31.47/4.50  --qbf_elim_univ                         false
% 31.47/4.50  --qbf_dom_inst                          none
% 31.47/4.50  --qbf_dom_pre_inst                      false
% 31.47/4.50  --qbf_sk_in                             false
% 31.47/4.50  --qbf_pred_elim                         true
% 31.47/4.50  --qbf_split                             512
% 31.47/4.50  
% 31.47/4.50  ------ BMC1 Options
% 31.47/4.50  
% 31.47/4.50  --bmc1_incremental                      false
% 31.47/4.50  --bmc1_axioms                           reachable_all
% 31.47/4.50  --bmc1_min_bound                        0
% 31.47/4.50  --bmc1_max_bound                        -1
% 31.47/4.50  --bmc1_max_bound_default                -1
% 31.47/4.50  --bmc1_symbol_reachability              true
% 31.47/4.50  --bmc1_property_lemmas                  false
% 31.47/4.50  --bmc1_k_induction                      false
% 31.47/4.50  --bmc1_non_equiv_states                 false
% 31.47/4.50  --bmc1_deadlock                         false
% 31.47/4.50  --bmc1_ucm                              false
% 31.47/4.50  --bmc1_add_unsat_core                   none
% 31.47/4.50  --bmc1_unsat_core_children              false
% 31.47/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.47/4.50  --bmc1_out_stat                         full
% 31.47/4.50  --bmc1_ground_init                      false
% 31.47/4.50  --bmc1_pre_inst_next_state              false
% 31.47/4.50  --bmc1_pre_inst_state                   false
% 31.47/4.50  --bmc1_pre_inst_reach_state             false
% 31.47/4.50  --bmc1_out_unsat_core                   false
% 31.47/4.50  --bmc1_aig_witness_out                  false
% 31.47/4.50  --bmc1_verbose                          false
% 31.47/4.50  --bmc1_dump_clauses_tptp                false
% 31.47/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.47/4.50  --bmc1_dump_file                        -
% 31.47/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.47/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.47/4.50  --bmc1_ucm_extend_mode                  1
% 31.47/4.50  --bmc1_ucm_init_mode                    2
% 31.47/4.50  --bmc1_ucm_cone_mode                    none
% 31.47/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.47/4.50  --bmc1_ucm_relax_model                  4
% 31.47/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.47/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.47/4.50  --bmc1_ucm_layered_model                none
% 31.47/4.50  --bmc1_ucm_max_lemma_size               10
% 31.47/4.50  
% 31.47/4.50  ------ AIG Options
% 31.47/4.50  
% 31.47/4.50  --aig_mode                              false
% 31.47/4.50  
% 31.47/4.50  ------ Instantiation Options
% 31.47/4.50  
% 31.47/4.50  --instantiation_flag                    true
% 31.47/4.50  --inst_sos_flag                         true
% 31.47/4.50  --inst_sos_phase                        true
% 31.47/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel_side                     none
% 31.47/4.50  --inst_solver_per_active                1400
% 31.47/4.50  --inst_solver_calls_frac                1.
% 31.47/4.50  --inst_passive_queue_type               priority_queues
% 31.47/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.47/4.50  --inst_passive_queues_freq              [25;2]
% 31.47/4.50  --inst_dismatching                      true
% 31.47/4.50  --inst_eager_unprocessed_to_passive     true
% 31.47/4.50  --inst_prop_sim_given                   true
% 31.47/4.50  --inst_prop_sim_new                     false
% 31.47/4.50  --inst_subs_new                         false
% 31.47/4.50  --inst_eq_res_simp                      false
% 31.47/4.50  --inst_subs_given                       false
% 31.47/4.50  --inst_orphan_elimination               true
% 31.47/4.50  --inst_learning_loop_flag               true
% 31.47/4.50  --inst_learning_start                   3000
% 31.47/4.50  --inst_learning_factor                  2
% 31.47/4.50  --inst_start_prop_sim_after_learn       3
% 31.47/4.50  --inst_sel_renew                        solver
% 31.47/4.50  --inst_lit_activity_flag                true
% 31.47/4.50  --inst_restr_to_given                   false
% 31.47/4.50  --inst_activity_threshold               500
% 31.47/4.50  --inst_out_proof                        true
% 31.47/4.50  
% 31.47/4.50  ------ Resolution Options
% 31.47/4.50  
% 31.47/4.50  --resolution_flag                       false
% 31.47/4.50  --res_lit_sel                           adaptive
% 31.47/4.50  --res_lit_sel_side                      none
% 31.47/4.50  --res_ordering                          kbo
% 31.47/4.50  --res_to_prop_solver                    active
% 31.47/4.50  --res_prop_simpl_new                    false
% 31.47/4.50  --res_prop_simpl_given                  true
% 31.47/4.50  --res_passive_queue_type                priority_queues
% 31.47/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.47/4.50  --res_passive_queues_freq               [15;5]
% 31.47/4.50  --res_forward_subs                      full
% 31.47/4.50  --res_backward_subs                     full
% 31.47/4.50  --res_forward_subs_resolution           true
% 31.47/4.50  --res_backward_subs_resolution          true
% 31.47/4.50  --res_orphan_elimination                true
% 31.47/4.50  --res_time_limit                        2.
% 31.47/4.50  --res_out_proof                         true
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Options
% 31.47/4.50  
% 31.47/4.50  --superposition_flag                    true
% 31.47/4.50  --sup_passive_queue_type                priority_queues
% 31.47/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.47/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.47/4.50  --demod_completeness_check              fast
% 31.47/4.50  --demod_use_ground                      true
% 31.47/4.50  --sup_to_prop_solver                    passive
% 31.47/4.50  --sup_prop_simpl_new                    true
% 31.47/4.50  --sup_prop_simpl_given                  true
% 31.47/4.50  --sup_fun_splitting                     true
% 31.47/4.50  --sup_smt_interval                      50000
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Simplification Setup
% 31.47/4.50  
% 31.47/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.47/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.47/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_immed_triv                        [TrivRules]
% 31.47/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_bw_main                     []
% 31.47/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.47/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_input_bw                          []
% 31.47/4.50  
% 31.47/4.50  ------ Combination Options
% 31.47/4.50  
% 31.47/4.50  --comb_res_mult                         3
% 31.47/4.50  --comb_sup_mult                         2
% 31.47/4.50  --comb_inst_mult                        10
% 31.47/4.50  
% 31.47/4.50  ------ Debug Options
% 31.47/4.50  
% 31.47/4.50  --dbg_backtrace                         false
% 31.47/4.50  --dbg_dump_prop_clauses                 false
% 31.47/4.50  --dbg_dump_prop_clauses_file            -
% 31.47/4.50  --dbg_out_stat                          false
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ Proving...
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  % SZS status Theorem for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50   Resolution empty clause
% 31.47/4.50  
% 31.47/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  fof(f21,axiom,(
% 31.47/4.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f34,plain,(
% 31.47/4.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 31.47/4.50    inference(nnf_transformation,[],[f21])).
% 31.47/4.50  
% 31.47/4.50  fof(f63,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f34])).
% 31.47/4.50  
% 31.47/4.50  fof(f11,axiom,(
% 31.47/4.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f52,plain,(
% 31.47/4.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f11])).
% 31.47/4.50  
% 31.47/4.50  fof(f12,axiom,(
% 31.47/4.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f53,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f12])).
% 31.47/4.50  
% 31.47/4.50  fof(f13,axiom,(
% 31.47/4.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f54,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f13])).
% 31.47/4.50  
% 31.47/4.50  fof(f14,axiom,(
% 31.47/4.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f55,plain,(
% 31.47/4.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f14])).
% 31.47/4.50  
% 31.47/4.50  fof(f15,axiom,(
% 31.47/4.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f56,plain,(
% 31.47/4.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f15])).
% 31.47/4.50  
% 31.47/4.50  fof(f16,axiom,(
% 31.47/4.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f57,plain,(
% 31.47/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f16])).
% 31.47/4.50  
% 31.47/4.50  fof(f17,axiom,(
% 31.47/4.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f58,plain,(
% 31.47/4.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f17])).
% 31.47/4.50  
% 31.47/4.50  fof(f71,plain,(
% 31.47/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f57,f58])).
% 31.47/4.50  
% 31.47/4.50  fof(f72,plain,(
% 31.47/4.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f56,f71])).
% 31.47/4.50  
% 31.47/4.50  fof(f73,plain,(
% 31.47/4.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f55,f72])).
% 31.47/4.50  
% 31.47/4.50  fof(f74,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f54,f73])).
% 31.47/4.50  
% 31.47/4.50  fof(f75,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f53,f74])).
% 31.47/4.50  
% 31.47/4.50  fof(f78,plain,(
% 31.47/4.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f52,f75])).
% 31.47/4.50  
% 31.47/4.50  fof(f86,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f63,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f23,conjecture,(
% 31.47/4.50    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f24,negated_conjecture,(
% 31.47/4.50    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.47/4.50    inference(negated_conjecture,[],[f23])).
% 31.47/4.50  
% 31.47/4.50  fof(f30,plain,(
% 31.47/4.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 31.47/4.50    inference(ennf_transformation,[],[f24])).
% 31.47/4.50  
% 31.47/4.50  fof(f37,plain,(
% 31.47/4.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f38,plain,(
% 31.47/4.50    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f37])).
% 31.47/4.50  
% 31.47/4.50  fof(f67,plain,(
% 31.47/4.50    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  fof(f19,axiom,(
% 31.47/4.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f60,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f19])).
% 31.47/4.50  
% 31.47/4.50  fof(f76,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f60,f75])).
% 31.47/4.50  
% 31.47/4.50  fof(f91,plain,(
% 31.47/4.50    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 31.47/4.50    inference(definition_unfolding,[],[f67,f76,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f7,axiom,(
% 31.47/4.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f48,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f7])).
% 31.47/4.50  
% 31.47/4.50  fof(f83,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f48,f76])).
% 31.47/4.50  
% 31.47/4.50  fof(f4,axiom,(
% 31.47/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f32,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(nnf_transformation,[],[f4])).
% 31.47/4.50  
% 31.47/4.50  fof(f33,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(flattening,[],[f32])).
% 31.47/4.50  
% 31.47/4.50  fof(f45,plain,(
% 31.47/4.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f33])).
% 31.47/4.50  
% 31.47/4.50  fof(f43,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.47/4.50    inference(cnf_transformation,[],[f33])).
% 31.47/4.50  
% 31.47/4.50  fof(f93,plain,(
% 31.47/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.47/4.50    inference(equality_resolution,[],[f43])).
% 31.47/4.50  
% 31.47/4.50  fof(f18,axiom,(
% 31.47/4.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f29,plain,(
% 31.47/4.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 31.47/4.50    inference(ennf_transformation,[],[f18])).
% 31.47/4.50  
% 31.47/4.50  fof(f59,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f29])).
% 31.47/4.50  
% 31.47/4.50  fof(f84,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f59,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f6,axiom,(
% 31.47/4.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f27,plain,(
% 31.47/4.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 31.47/4.50    inference(ennf_transformation,[],[f6])).
% 31.47/4.50  
% 31.47/4.50  fof(f28,plain,(
% 31.47/4.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 31.47/4.50    inference(flattening,[],[f27])).
% 31.47/4.50  
% 31.47/4.50  fof(f47,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f28])).
% 31.47/4.50  
% 31.47/4.50  fof(f69,plain,(
% 31.47/4.50    k1_xboole_0 != sK1),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  fof(f22,axiom,(
% 31.47/4.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f35,plain,(
% 31.47/4.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 31.47/4.50    inference(nnf_transformation,[],[f22])).
% 31.47/4.50  
% 31.47/4.50  fof(f36,plain,(
% 31.47/4.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 31.47/4.50    inference(flattening,[],[f35])).
% 31.47/4.50  
% 31.47/4.50  fof(f66,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f36])).
% 31.47/4.50  
% 31.47/4.50  fof(f88,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f66,f75])).
% 31.47/4.50  
% 31.47/4.50  fof(f5,axiom,(
% 31.47/4.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f26,plain,(
% 31.47/4.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.47/4.50    inference(ennf_transformation,[],[f5])).
% 31.47/4.50  
% 31.47/4.50  fof(f46,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f26])).
% 31.47/4.50  
% 31.47/4.50  fof(f82,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f46,f76])).
% 31.47/4.50  
% 31.47/4.50  fof(f2,axiom,(
% 31.47/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f31,plain,(
% 31.47/4.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.47/4.50    inference(nnf_transformation,[],[f2])).
% 31.47/4.50  
% 31.47/4.50  fof(f40,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f31])).
% 31.47/4.50  
% 31.47/4.50  fof(f10,axiom,(
% 31.47/4.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f51,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f10])).
% 31.47/4.50  
% 31.47/4.50  fof(f77,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f51,f76])).
% 31.47/4.50  
% 31.47/4.50  fof(f80,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f40,f77])).
% 31.47/4.50  
% 31.47/4.50  fof(f8,axiom,(
% 31.47/4.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f49,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f8])).
% 31.47/4.50  
% 31.47/4.50  fof(f1,axiom,(
% 31.47/4.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f39,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f1])).
% 31.47/4.50  
% 31.47/4.50  fof(f9,axiom,(
% 31.47/4.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f50,plain,(
% 31.47/4.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f9])).
% 31.47/4.50  
% 31.47/4.50  fof(f3,axiom,(
% 31.47/4.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f25,plain,(
% 31.47/4.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.47/4.50    inference(rectify,[],[f3])).
% 31.47/4.50  
% 31.47/4.50  fof(f42,plain,(
% 31.47/4.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f25])).
% 31.47/4.50  
% 31.47/4.50  fof(f81,plain,(
% 31.47/4.50    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 31.47/4.50    inference(definition_unfolding,[],[f42,f77])).
% 31.47/4.50  
% 31.47/4.50  fof(f20,axiom,(
% 31.47/4.50    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f61,plain,(
% 31.47/4.50    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f20])).
% 31.47/4.50  
% 31.47/4.50  fof(f85,plain,(
% 31.47/4.50    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 31.47/4.50    inference(definition_unfolding,[],[f61,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f68,plain,(
% 31.47/4.50    sK1 != sK2),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  fof(f70,plain,(
% 31.47/4.50    k1_xboole_0 != sK2),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  cnf(c_14,plain,
% 31.47/4.50      ( ~ r2_hidden(X0,X1)
% 31.47/4.50      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_820,plain,
% 31.47/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.47/4.50      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_22,negated_conjecture,
% 31.47/4.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f91]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_9,plain,
% 31.47/4.50      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 31.47/4.50      inference(cnf_transformation,[],[f83]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_822,plain,
% 31.47/4.50      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_9828,plain,
% 31.47/4.50      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_22,c_822]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.47/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_826,plain,
% 31.47/4.50      ( X0 = X1
% 31.47/4.50      | r1_tarski(X0,X1) != iProver_top
% 31.47/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59744,plain,
% 31.47/4.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 31.47/4.50      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_9828,c_826]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59935,plain,
% 31.47/4.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 31.47/4.50      | r2_hidden(sK0,sK1) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_820,c_59744]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f93]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_45,plain,
% 31.47/4.50      ( r1_tarski(X0,X0) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_47,plain,
% 31.47/4.50      ( r1_tarski(sK1,sK1) = iProver_top ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_45]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_12,plain,
% 31.47/4.50      ( r2_hidden(X0,X1)
% 31.47/4.50      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f84]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_821,plain,
% 31.47/4.50      ( r2_hidden(X0,X1) = iProver_top
% 31.47/4.50      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_8,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1)
% 31.47/4.50      | ~ r1_tarski(X0,X2)
% 31.47/4.50      | ~ r1_xboole_0(X1,X2)
% 31.47/4.50      | k1_xboole_0 = X0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_823,plain,
% 31.47/4.50      ( k1_xboole_0 = X0
% 31.47/4.50      | r1_tarski(X0,X1) != iProver_top
% 31.47/4.50      | r1_tarski(X0,X2) != iProver_top
% 31.47/4.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_12126,plain,
% 31.47/4.50      ( sK1 = k1_xboole_0
% 31.47/4.50      | r1_tarski(sK1,X0) != iProver_top
% 31.47/4.50      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_9828,c_823]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_20,negated_conjecture,
% 31.47/4.50      ( k1_xboole_0 != sK1 ),
% 31.47/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_467,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_862,plain,
% 31.47/4.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_467]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_890,plain,
% 31.47/4.50      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_862]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_885,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,k1_xboole_0)
% 31.47/4.50      | ~ r1_tarski(k1_xboole_0,X0)
% 31.47/4.50      | k1_xboole_0 = X0 ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_4]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_950,plain,
% 31.47/4.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_885]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1022,plain,
% 31.47/4.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_14966,plain,
% 31.47/4.50      ( r1_tarski(sK1,X0) != iProver_top
% 31.47/4.50      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_12126,c_20,c_890,c_950,c_1022]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_14972,plain,
% 31.47/4.50      ( r2_hidden(sK0,X0) = iProver_top | r1_tarski(sK1,X0) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_821,c_14966]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_14974,plain,
% 31.47/4.50      ( r2_hidden(sK0,sK1) = iProver_top | r1_tarski(sK1,sK1) != iProver_top ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_14972]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59939,plain,
% 31.47/4.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_59935,c_47,c_14974]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59947,plain,
% 31.47/4.50      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
% 31.47/4.50      inference(demodulation,[status(thm)],[c_59939,c_22]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59957,plain,
% 31.47/4.50      ( r2_hidden(sK0,X0) = iProver_top | r1_xboole_0(sK1,X0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_59939,c_821]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_16,plain,
% 31.47/4.50      ( ~ r2_hidden(X0,X1)
% 31.47/4.50      | ~ r2_hidden(X2,X1)
% 31.47/4.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f88]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_818,plain,
% 31.47/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.47/4.50      | r2_hidden(X2,X1) != iProver_top
% 31.47/4.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_59960,plain,
% 31.47/4.50      ( r2_hidden(sK0,X0) != iProver_top | r1_tarski(sK1,X0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_59939,c_818]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_69938,plain,
% 31.47/4.50      ( r1_tarski(sK1,X0) = iProver_top | r1_xboole_0(sK1,X0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_59957,c_59960]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_7,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1)
% 31.47/4.50      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 31.47/4.50      inference(cnf_transformation,[],[f82]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_824,plain,
% 31.47/4.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 31.47/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_70442,plain,
% 31.47/4.50      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
% 31.47/4.50      | r1_xboole_0(sK1,X0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_69938,c_824]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2,plain,
% 31.47/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.47/4.50      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_10,plain,
% 31.47/4.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_0,plain,
% 31.47/4.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f39]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_463,plain,
% 31.47/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.47/4.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 31.47/4.50      inference(theory_normalisation,[status(thm)],[c_2,c_10,c_0]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_827,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
% 31.47/4.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_83423,plain,
% 31.47/4.50      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
% 31.47/4.51      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_70442,c_827]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_108177,plain,
% 31.47/4.51      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
% 31.47/4.51      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_59947,c_83423]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_11,plain,
% 31.47/4.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.47/4.51      inference(cnf_transformation,[],[f50]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1164,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1162,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_3,plain,
% 31.47/4.51      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 31.47/4.51      inference(cnf_transformation,[],[f81]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_462,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 31.47/4.51      inference(theory_normalisation,[status(thm)],[c_3,c_10,c_0]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_13,plain,
% 31.47/4.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 31.47/4.51      inference(cnf_transformation,[],[f85]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_829,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.47/4.51      inference(light_normalisation,[status(thm)],[c_462,c_11,c_13]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1095,plain,
% 31.47/4.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_829,c_0]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1168,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_1162,c_1095]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1342,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_1164,c_1168]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1351,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_1342,c_829]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_108848,plain,
% 31.47/4.51      ( sK1 = sK2 | sK2 = k1_xboole_0 ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_108177,c_1351,c_59947]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21,negated_conjecture,
% 31.47/4.51      ( sK1 != sK2 ),
% 31.47/4.51      inference(cnf_transformation,[],[f68]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_108975,plain,
% 31.47/4.51      ( sK2 = k1_xboole_0 ),
% 31.47/4.51      inference(global_propositional_subsumption,[status(thm)],[c_108848,c_21]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_19,negated_conjecture,
% 31.47/4.51      ( k1_xboole_0 != sK2 ),
% 31.47/4.51      inference(cnf_transformation,[],[f70]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_108980,plain,
% 31.47/4.51      ( k1_xboole_0 != k1_xboole_0 ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_108975,c_19]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_108981,plain,
% 31.47/4.51      ( $false ),
% 31.47/4.51      inference(equality_resolution_simp,[status(thm)],[c_108980]) ).
% 31.47/4.51  
% 31.47/4.51  
% 31.47/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.47/4.51  
% 31.47/4.51  ------                               Statistics
% 31.47/4.51  
% 31.47/4.51  ------ General
% 31.47/4.51  
% 31.47/4.51  abstr_ref_over_cycles:                  0
% 31.47/4.51  abstr_ref_under_cycles:                 0
% 31.47/4.51  gc_basic_clause_elim:                   0
% 31.47/4.51  forced_gc_time:                         0
% 31.47/4.51  parsing_time:                           0.01
% 31.47/4.51  unif_index_cands_time:                  0.
% 31.47/4.51  unif_index_add_time:                    0.
% 31.47/4.51  orderings_time:                         0.
% 31.47/4.51  out_proof_time:                         0.012
% 31.47/4.51  total_time:                             3.535
% 31.47/4.51  num_of_symbols:                         41
% 31.47/4.51  num_of_terms:                           325904
% 31.47/4.51  
% 31.47/4.51  ------ Preprocessing
% 31.47/4.51  
% 31.47/4.51  num_of_splits:                          0
% 31.47/4.51  num_of_split_atoms:                     0
% 31.47/4.51  num_of_reused_defs:                     0
% 31.47/4.51  num_eq_ax_congr_red:                    9
% 31.47/4.51  num_of_sem_filtered_clauses:            1
% 31.47/4.51  num_of_subtypes:                        0
% 31.47/4.51  monotx_restored_types:                  0
% 31.47/4.51  sat_num_of_epr_types:                   0
% 31.47/4.51  sat_num_of_non_cyclic_types:            0
% 31.47/4.51  sat_guarded_non_collapsed_types:        0
% 31.47/4.51  num_pure_diseq_elim:                    0
% 31.47/4.51  simp_replaced_by:                       0
% 31.47/4.51  res_preprocessed:                       103
% 31.47/4.51  prep_upred:                             0
% 31.47/4.51  prep_unflattend:                        12
% 31.47/4.51  smt_new_axioms:                         0
% 31.47/4.51  pred_elim_cands:                        3
% 31.47/4.51  pred_elim:                              0
% 31.47/4.51  pred_elim_cl:                           0
% 31.47/4.51  pred_elim_cycles:                       2
% 31.47/4.51  merged_defs:                            16
% 31.47/4.51  merged_defs_ncl:                        0
% 31.47/4.51  bin_hyper_res:                          16
% 31.47/4.51  prep_cycles:                            4
% 31.47/4.51  pred_elim_time:                         0.002
% 31.47/4.51  splitting_time:                         0.
% 31.47/4.51  sem_filter_time:                        0.
% 31.47/4.51  monotx_time:                            0.
% 31.47/4.51  subtype_inf_time:                       0.
% 31.47/4.51  
% 31.47/4.51  ------ Problem properties
% 31.47/4.51  
% 31.47/4.51  clauses:                                22
% 31.47/4.51  conjectures:                            4
% 31.47/4.51  epr:                                    6
% 31.47/4.51  horn:                                   21
% 31.47/4.51  ground:                                 4
% 31.47/4.51  unary:                                  11
% 31.47/4.51  binary:                                 8
% 31.47/4.51  lits:                                   37
% 31.47/4.51  lits_eq:                                14
% 31.47/4.51  fd_pure:                                0
% 31.47/4.51  fd_pseudo:                              0
% 31.47/4.51  fd_cond:                                1
% 31.47/4.51  fd_pseudo_cond:                         1
% 31.47/4.51  ac_symbols:                             1
% 31.47/4.51  
% 31.47/4.51  ------ Propositional Solver
% 31.47/4.51  
% 31.47/4.51  prop_solver_calls:                      33
% 31.47/4.51  prop_fast_solver_calls:                 694
% 31.47/4.51  smt_solver_calls:                       0
% 31.47/4.51  smt_fast_solver_calls:                  0
% 31.47/4.51  prop_num_of_clauses:                    10010
% 31.47/4.51  prop_preprocess_simplified:             18681
% 31.47/4.51  prop_fo_subsumed:                       9
% 31.47/4.51  prop_solver_time:                       0.
% 31.47/4.51  smt_solver_time:                        0.
% 31.47/4.51  smt_fast_solver_time:                   0.
% 31.47/4.51  prop_fast_solver_time:                  0.
% 31.47/4.51  prop_unsat_core_time:                   0.
% 31.47/4.51  
% 31.47/4.51  ------ QBF
% 31.47/4.51  
% 31.47/4.51  qbf_q_res:                              0
% 31.47/4.51  qbf_num_tautologies:                    0
% 31.47/4.51  qbf_prep_cycles:                        0
% 31.47/4.51  
% 31.47/4.51  ------ BMC1
% 31.47/4.51  
% 31.47/4.51  bmc1_current_bound:                     -1
% 31.47/4.51  bmc1_last_solved_bound:                 -1
% 31.47/4.51  bmc1_unsat_core_size:                   -1
% 31.47/4.51  bmc1_unsat_core_parents_size:           -1
% 31.47/4.51  bmc1_merge_next_fun:                    0
% 31.47/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.47/4.51  
% 31.47/4.51  ------ Instantiation
% 31.47/4.51  
% 31.47/4.51  inst_num_of_clauses:                    2380
% 31.47/4.51  inst_num_in_passive:                    860
% 31.47/4.51  inst_num_in_active:                     844
% 31.47/4.51  inst_num_in_unprocessed:                676
% 31.47/4.51  inst_num_of_loops:                      940
% 31.47/4.51  inst_num_of_learning_restarts:          0
% 31.47/4.51  inst_num_moves_active_passive:          91
% 31.47/4.51  inst_lit_activity:                      0
% 31.47/4.51  inst_lit_activity_moves:                0
% 31.47/4.51  inst_num_tautologies:                   0
% 31.47/4.51  inst_num_prop_implied:                  0
% 31.47/4.51  inst_num_existing_simplified:           0
% 31.47/4.51  inst_num_eq_res_simplified:             0
% 31.47/4.51  inst_num_child_elim:                    0
% 31.47/4.51  inst_num_of_dismatching_blockings:      2161
% 31.47/4.51  inst_num_of_non_proper_insts:           3184
% 31.47/4.51  inst_num_of_duplicates:                 0
% 31.47/4.51  inst_inst_num_from_inst_to_res:         0
% 31.47/4.51  inst_dismatching_checking_time:         0.
% 31.47/4.51  
% 31.47/4.51  ------ Resolution
% 31.47/4.51  
% 31.47/4.51  res_num_of_clauses:                     0
% 31.47/4.51  res_num_in_passive:                     0
% 31.47/4.51  res_num_in_active:                      0
% 31.47/4.51  res_num_of_loops:                       107
% 31.47/4.51  res_forward_subset_subsumed:            470
% 31.47/4.51  res_backward_subset_subsumed:           2
% 31.47/4.51  res_forward_subsumed:                   0
% 31.47/4.51  res_backward_subsumed:                  0
% 31.47/4.51  res_forward_subsumption_resolution:     0
% 31.47/4.51  res_backward_subsumption_resolution:    0
% 31.47/4.51  res_clause_to_clause_subsumption:       464520
% 31.47/4.51  res_orphan_elimination:                 0
% 31.47/4.51  res_tautology_del:                      321
% 31.47/4.51  res_num_eq_res_simplified:              0
% 31.47/4.51  res_num_sel_changes:                    0
% 31.47/4.51  res_moves_from_active_to_pass:          0
% 31.47/4.51  
% 31.47/4.51  ------ Superposition
% 31.47/4.51  
% 31.47/4.51  sup_time_total:                         0.
% 31.47/4.51  sup_time_generating:                    0.
% 31.47/4.51  sup_time_sim_full:                      0.
% 31.47/4.51  sup_time_sim_immed:                     0.
% 31.47/4.51  
% 31.47/4.51  sup_num_of_clauses:                     4167
% 31.47/4.51  sup_num_in_active:                      172
% 31.47/4.51  sup_num_in_passive:                     3995
% 31.47/4.51  sup_num_of_loops:                       186
% 31.47/4.51  sup_fw_superposition:                   28908
% 31.47/4.51  sup_bw_superposition:                   19268
% 31.47/4.51  sup_immediate_simplified:               34861
% 31.47/4.51  sup_given_eliminated:                   0
% 31.47/4.51  comparisons_done:                       0
% 31.47/4.51  comparisons_avoided:                    3
% 31.47/4.51  
% 31.47/4.51  ------ Simplifications
% 31.47/4.51  
% 31.47/4.51  
% 31.47/4.51  sim_fw_subset_subsumed:                 18
% 31.47/4.51  sim_bw_subset_subsumed:                 1
% 31.47/4.51  sim_fw_subsumed:                        533
% 31.47/4.51  sim_bw_subsumed:                        1
% 31.47/4.51  sim_fw_subsumption_res:                 0
% 31.47/4.51  sim_bw_subsumption_res:                 0
% 31.47/4.51  sim_tautology_del:                      4
% 31.47/4.51  sim_eq_tautology_del:                   5642
% 31.47/4.51  sim_eq_res_simp:                        0
% 31.47/4.51  sim_fw_demodulated:                     36488
% 31.47/4.51  sim_bw_demodulated:                     27
% 31.47/4.51  sim_light_normalised:                   7599
% 31.47/4.51  sim_joinable_taut:                      1286
% 31.47/4.51  sim_joinable_simp:                      0
% 31.47/4.51  sim_ac_normalised:                      0
% 31.47/4.51  sim_smt_subsumption:                    0
% 31.47/4.51  
%------------------------------------------------------------------------------
