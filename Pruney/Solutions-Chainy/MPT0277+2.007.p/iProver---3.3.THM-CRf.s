%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:29 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  153 (3427 expanded)
%              Number of clauses        :   69 ( 213 expanded)
%              Number of leaves         :   24 (1114 expanded)
%              Depth                    :   27
%              Number of atoms          :  364 (5252 expanded)
%              Number of equality atoms :  312 (5098 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f76,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f39,f68,f68,f68,f68])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f69])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f36,f70])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f67,f71,f71,f67])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) )
   => ( ( ( k2_tarski(sK1,sK2) != sK0
          & k1_tarski(sK2) != sK0
          & k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 )
      & ( k2_tarski(sK1,sK2) = sK0
        | k1_tarski(sK2) = sK0
        | k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ( k2_tarski(sK1,sK2) != sK0
        & k1_tarski(sK2) != sK0
        & k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 )
    & ( k2_tarski(sK1,sK2) = sK0
      | k1_tarski(sK2) = sK0
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).

fof(f58,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k1_xboole_0 = sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f58,f67,f71,f71,f70,f67])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f70])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,
    ( k1_tarski(sK2) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f61,f71,f70,f67])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,
    ( k1_xboole_0 != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f59,f70,f67])).

fof(f60,plain,
    ( k1_tarski(sK1) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f60,f71,f70,f67])).

fof(f62,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f62,f67,f70,f67])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f54,f67,f71])).

fof(f89,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) ),
    inference(definition_unfolding,[],[f38,f70,f70,f68])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f53,f67,f71])).

fof(f90,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f79])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f91,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

cnf(c_14,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_932,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_14,c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_80,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_197,plain,
    ( X0 != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) != X4
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0
    | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X4),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X4)))) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_80,c_13])).

cnf(c_198,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) = k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_266,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_198,c_19])).

cnf(c_933,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k3_tarski(k6_enumset1(k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),X0))
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_266,c_5])).

cnf(c_943,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k3_tarski(k6_enumset1(k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),X0)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_932,c_933])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_7,c_0])).

cnf(c_561,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_287,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_555,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_576,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_286,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_643,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_16,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_280,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_16,c_7,c_0])).

cnf(c_18,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_278,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_18,c_7,c_0])).

cnf(c_17,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_279,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_17,c_7,c_0])).

cnf(c_15,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_281,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0
    | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_15,c_7,c_0])).

cnf(c_645,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_266,c_278,c_279,c_281,c_576,c_643])).

cnf(c_577,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_597,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_710,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
    | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_732,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_10,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_854,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_569,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_777,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X0
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1157,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_1159,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1272,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_266,c_278,c_279,c_280,c_281,c_561,c_576,c_643,c_710,c_732,c_854,c_1159])).

cnf(c_1273,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1272])).

cnf(c_4,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_282,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_7,c_0])).

cnf(c_539,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_282,c_5])).

cnf(c_540,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(light_normalisation,[status(thm)],[c_539,c_14])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_541,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_540,c_6,c_8])).

cnf(c_647,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_645,c_541])).

cnf(c_1282,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1273,c_647])).

cnf(c_1284,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1282,c_8,c_14])).

cnf(c_1285,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1284])).

cnf(c_11,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_533,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2227,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_533])).

cnf(c_537,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_9968,plain,
    ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_537,c_541])).

cnf(c_9980,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2227,c_9968])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2646,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_766,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1901,plain,
    ( r1_tarski(sK0,X0)
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_5489,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_10247,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9980,c_266,c_278,c_279,c_280,c_281,c_561,c_576,c_643,c_732,c_2646,c_5489])).

cnf(c_10250,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10247,c_647])).

cnf(c_10251,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10250])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.63/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/1.01  
% 3.63/1.01  ------  iProver source info
% 3.63/1.01  
% 3.63/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.63/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/1.01  git: non_committed_changes: false
% 3.63/1.01  git: last_make_outside_of_git: false
% 3.63/1.01  
% 3.63/1.01  ------ 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options
% 3.63/1.01  
% 3.63/1.01  --out_options                           all
% 3.63/1.01  --tptp_safe_out                         true
% 3.63/1.01  --problem_path                          ""
% 3.63/1.01  --include_path                          ""
% 3.63/1.01  --clausifier                            res/vclausify_rel
% 3.63/1.01  --clausifier_options                    ""
% 3.63/1.01  --stdin                                 false
% 3.63/1.01  --stats_out                             all
% 3.63/1.01  
% 3.63/1.01  ------ General Options
% 3.63/1.01  
% 3.63/1.01  --fof                                   false
% 3.63/1.01  --time_out_real                         305.
% 3.63/1.01  --time_out_virtual                      -1.
% 3.63/1.01  --symbol_type_check                     false
% 3.63/1.01  --clausify_out                          false
% 3.63/1.01  --sig_cnt_out                           false
% 3.63/1.01  --trig_cnt_out                          false
% 3.63/1.01  --trig_cnt_out_tolerance                1.
% 3.63/1.01  --trig_cnt_out_sk_spl                   false
% 3.63/1.01  --abstr_cl_out                          false
% 3.63/1.01  
% 3.63/1.01  ------ Global Options
% 3.63/1.01  
% 3.63/1.01  --schedule                              default
% 3.63/1.01  --add_important_lit                     false
% 3.63/1.01  --prop_solver_per_cl                    1000
% 3.63/1.01  --min_unsat_core                        false
% 3.63/1.01  --soft_assumptions                      false
% 3.63/1.01  --soft_lemma_size                       3
% 3.63/1.01  --prop_impl_unit_size                   0
% 3.63/1.01  --prop_impl_unit                        []
% 3.63/1.01  --share_sel_clauses                     true
% 3.63/1.01  --reset_solvers                         false
% 3.63/1.01  --bc_imp_inh                            [conj_cone]
% 3.63/1.01  --conj_cone_tolerance                   3.
% 3.63/1.01  --extra_neg_conj                        none
% 3.63/1.01  --large_theory_mode                     true
% 3.63/1.01  --prolific_symb_bound                   200
% 3.63/1.01  --lt_threshold                          2000
% 3.63/1.01  --clause_weak_htbl                      true
% 3.63/1.01  --gc_record_bc_elim                     false
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing Options
% 3.63/1.01  
% 3.63/1.01  --preprocessing_flag                    true
% 3.63/1.01  --time_out_prep_mult                    0.1
% 3.63/1.01  --splitting_mode                        input
% 3.63/1.01  --splitting_grd                         true
% 3.63/1.01  --splitting_cvd                         false
% 3.63/1.01  --splitting_cvd_svl                     false
% 3.63/1.01  --splitting_nvd                         32
% 3.63/1.01  --sub_typing                            true
% 3.63/1.01  --prep_gs_sim                           true
% 3.63/1.01  --prep_unflatten                        true
% 3.63/1.01  --prep_res_sim                          true
% 3.63/1.01  --prep_upred                            true
% 3.63/1.01  --prep_sem_filter                       exhaustive
% 3.63/1.01  --prep_sem_filter_out                   false
% 3.63/1.01  --pred_elim                             true
% 3.63/1.01  --res_sim_input                         true
% 3.63/1.01  --eq_ax_congr_red                       true
% 3.63/1.01  --pure_diseq_elim                       true
% 3.63/1.01  --brand_transform                       false
% 3.63/1.01  --non_eq_to_eq                          false
% 3.63/1.01  --prep_def_merge                        true
% 3.63/1.01  --prep_def_merge_prop_impl              false
% 3.63/1.01  --prep_def_merge_mbd                    true
% 3.63/1.01  --prep_def_merge_tr_red                 false
% 3.63/1.01  --prep_def_merge_tr_cl                  false
% 3.63/1.01  --smt_preprocessing                     true
% 3.63/1.01  --smt_ac_axioms                         fast
% 3.63/1.01  --preprocessed_out                      false
% 3.63/1.01  --preprocessed_stats                    false
% 3.63/1.01  
% 3.63/1.01  ------ Abstraction refinement Options
% 3.63/1.01  
% 3.63/1.01  --abstr_ref                             []
% 3.63/1.01  --abstr_ref_prep                        false
% 3.63/1.01  --abstr_ref_until_sat                   false
% 3.63/1.01  --abstr_ref_sig_restrict                funpre
% 3.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.01  --abstr_ref_under                       []
% 3.63/1.01  
% 3.63/1.01  ------ SAT Options
% 3.63/1.01  
% 3.63/1.01  --sat_mode                              false
% 3.63/1.01  --sat_fm_restart_options                ""
% 3.63/1.01  --sat_gr_def                            false
% 3.63/1.01  --sat_epr_types                         true
% 3.63/1.01  --sat_non_cyclic_types                  false
% 3.63/1.01  --sat_finite_models                     false
% 3.63/1.01  --sat_fm_lemmas                         false
% 3.63/1.01  --sat_fm_prep                           false
% 3.63/1.01  --sat_fm_uc_incr                        true
% 3.63/1.01  --sat_out_model                         small
% 3.63/1.01  --sat_out_clauses                       false
% 3.63/1.01  
% 3.63/1.01  ------ QBF Options
% 3.63/1.01  
% 3.63/1.01  --qbf_mode                              false
% 3.63/1.01  --qbf_elim_univ                         false
% 3.63/1.01  --qbf_dom_inst                          none
% 3.63/1.01  --qbf_dom_pre_inst                      false
% 3.63/1.01  --qbf_sk_in                             false
% 3.63/1.01  --qbf_pred_elim                         true
% 3.63/1.01  --qbf_split                             512
% 3.63/1.01  
% 3.63/1.01  ------ BMC1 Options
% 3.63/1.01  
% 3.63/1.01  --bmc1_incremental                      false
% 3.63/1.01  --bmc1_axioms                           reachable_all
% 3.63/1.01  --bmc1_min_bound                        0
% 3.63/1.01  --bmc1_max_bound                        -1
% 3.63/1.01  --bmc1_max_bound_default                -1
% 3.63/1.01  --bmc1_symbol_reachability              true
% 3.63/1.01  --bmc1_property_lemmas                  false
% 3.63/1.01  --bmc1_k_induction                      false
% 3.63/1.01  --bmc1_non_equiv_states                 false
% 3.63/1.01  --bmc1_deadlock                         false
% 3.63/1.01  --bmc1_ucm                              false
% 3.63/1.01  --bmc1_add_unsat_core                   none
% 3.63/1.01  --bmc1_unsat_core_children              false
% 3.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.01  --bmc1_out_stat                         full
% 3.63/1.01  --bmc1_ground_init                      false
% 3.63/1.01  --bmc1_pre_inst_next_state              false
% 3.63/1.01  --bmc1_pre_inst_state                   false
% 3.63/1.01  --bmc1_pre_inst_reach_state             false
% 3.63/1.01  --bmc1_out_unsat_core                   false
% 3.63/1.01  --bmc1_aig_witness_out                  false
% 3.63/1.01  --bmc1_verbose                          false
% 3.63/1.01  --bmc1_dump_clauses_tptp                false
% 3.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.01  --bmc1_dump_file                        -
% 3.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.01  --bmc1_ucm_extend_mode                  1
% 3.63/1.01  --bmc1_ucm_init_mode                    2
% 3.63/1.01  --bmc1_ucm_cone_mode                    none
% 3.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.01  --bmc1_ucm_relax_model                  4
% 3.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.01  --bmc1_ucm_layered_model                none
% 3.63/1.01  --bmc1_ucm_max_lemma_size               10
% 3.63/1.01  
% 3.63/1.01  ------ AIG Options
% 3.63/1.01  
% 3.63/1.01  --aig_mode                              false
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation Options
% 3.63/1.01  
% 3.63/1.01  --instantiation_flag                    true
% 3.63/1.01  --inst_sos_flag                         true
% 3.63/1.01  --inst_sos_phase                        true
% 3.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel_side                     num_symb
% 3.63/1.01  --inst_solver_per_active                1400
% 3.63/1.01  --inst_solver_calls_frac                1.
% 3.63/1.01  --inst_passive_queue_type               priority_queues
% 3.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.01  --inst_passive_queues_freq              [25;2]
% 3.63/1.01  --inst_dismatching                      true
% 3.63/1.01  --inst_eager_unprocessed_to_passive     true
% 3.63/1.01  --inst_prop_sim_given                   true
% 3.63/1.01  --inst_prop_sim_new                     false
% 3.63/1.01  --inst_subs_new                         false
% 3.63/1.01  --inst_eq_res_simp                      false
% 3.63/1.01  --inst_subs_given                       false
% 3.63/1.01  --inst_orphan_elimination               true
% 3.63/1.01  --inst_learning_loop_flag               true
% 3.63/1.01  --inst_learning_start                   3000
% 3.63/1.01  --inst_learning_factor                  2
% 3.63/1.01  --inst_start_prop_sim_after_learn       3
% 3.63/1.01  --inst_sel_renew                        solver
% 3.63/1.01  --inst_lit_activity_flag                true
% 3.63/1.01  --inst_restr_to_given                   false
% 3.63/1.01  --inst_activity_threshold               500
% 3.63/1.01  --inst_out_proof                        true
% 3.63/1.01  
% 3.63/1.01  ------ Resolution Options
% 3.63/1.01  
% 3.63/1.01  --resolution_flag                       true
% 3.63/1.01  --res_lit_sel                           adaptive
% 3.63/1.01  --res_lit_sel_side                      none
% 3.63/1.01  --res_ordering                          kbo
% 3.63/1.01  --res_to_prop_solver                    active
% 3.63/1.01  --res_prop_simpl_new                    false
% 3.63/1.01  --res_prop_simpl_given                  true
% 3.63/1.01  --res_passive_queue_type                priority_queues
% 3.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.01  --res_passive_queues_freq               [15;5]
% 3.63/1.01  --res_forward_subs                      full
% 3.63/1.01  --res_backward_subs                     full
% 3.63/1.01  --res_forward_subs_resolution           true
% 3.63/1.01  --res_backward_subs_resolution          true
% 3.63/1.01  --res_orphan_elimination                true
% 3.63/1.01  --res_time_limit                        2.
% 3.63/1.01  --res_out_proof                         true
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Options
% 3.63/1.01  
% 3.63/1.01  --superposition_flag                    true
% 3.63/1.01  --sup_passive_queue_type                priority_queues
% 3.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.01  --demod_completeness_check              fast
% 3.63/1.01  --demod_use_ground                      true
% 3.63/1.01  --sup_to_prop_solver                    passive
% 3.63/1.01  --sup_prop_simpl_new                    true
% 3.63/1.01  --sup_prop_simpl_given                  true
% 3.63/1.01  --sup_fun_splitting                     true
% 3.63/1.01  --sup_smt_interval                      50000
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Simplification Setup
% 3.63/1.01  
% 3.63/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_immed_triv                        [TrivRules]
% 3.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_bw_main                     []
% 3.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_input_bw                          []
% 3.63/1.01  
% 3.63/1.01  ------ Combination Options
% 3.63/1.01  
% 3.63/1.01  --comb_res_mult                         3
% 3.63/1.01  --comb_sup_mult                         2
% 3.63/1.01  --comb_inst_mult                        10
% 3.63/1.01  
% 3.63/1.01  ------ Debug Options
% 3.63/1.01  
% 3.63/1.01  --dbg_backtrace                         false
% 3.63/1.01  --dbg_dump_prop_clauses                 false
% 3.63/1.01  --dbg_dump_prop_clauses_file            -
% 3.63/1.01  --dbg_out_stat                          false
% 3.63/1.01  ------ Parsing...
% 3.63/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.01  ------ Proving...
% 3.63/1.01  ------ Problem Properties 
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  clauses                                 20
% 3.63/1.01  conjectures                             4
% 3.63/1.01  EPR                                     0
% 3.63/1.01  Horn                                    18
% 3.63/1.01  unary                                   11
% 3.63/1.01  binary                                  7
% 3.63/1.01  lits                                    34
% 3.63/1.01  lits eq                                 26
% 3.63/1.01  fd_pure                                 0
% 3.63/1.01  fd_pseudo                               0
% 3.63/1.01  fd_cond                                 0
% 3.63/1.01  fd_pseudo_cond                          1
% 3.63/1.01  AC symbols                              1
% 3.63/1.01  
% 3.63/1.01  ------ Schedule dynamic 5 is on 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  ------ 
% 3.63/1.01  Current options:
% 3.63/1.01  ------ 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options
% 3.63/1.01  
% 3.63/1.01  --out_options                           all
% 3.63/1.01  --tptp_safe_out                         true
% 3.63/1.01  --problem_path                          ""
% 3.63/1.01  --include_path                          ""
% 3.63/1.01  --clausifier                            res/vclausify_rel
% 3.63/1.01  --clausifier_options                    ""
% 3.63/1.01  --stdin                                 false
% 3.63/1.01  --stats_out                             all
% 3.63/1.01  
% 3.63/1.01  ------ General Options
% 3.63/1.01  
% 3.63/1.01  --fof                                   false
% 3.63/1.01  --time_out_real                         305.
% 3.63/1.01  --time_out_virtual                      -1.
% 3.63/1.01  --symbol_type_check                     false
% 3.63/1.01  --clausify_out                          false
% 3.63/1.01  --sig_cnt_out                           false
% 3.63/1.01  --trig_cnt_out                          false
% 3.63/1.01  --trig_cnt_out_tolerance                1.
% 3.63/1.01  --trig_cnt_out_sk_spl                   false
% 3.63/1.01  --abstr_cl_out                          false
% 3.63/1.01  
% 3.63/1.01  ------ Global Options
% 3.63/1.01  
% 3.63/1.01  --schedule                              default
% 3.63/1.01  --add_important_lit                     false
% 3.63/1.01  --prop_solver_per_cl                    1000
% 3.63/1.01  --min_unsat_core                        false
% 3.63/1.01  --soft_assumptions                      false
% 3.63/1.01  --soft_lemma_size                       3
% 3.63/1.01  --prop_impl_unit_size                   0
% 3.63/1.01  --prop_impl_unit                        []
% 3.63/1.01  --share_sel_clauses                     true
% 3.63/1.01  --reset_solvers                         false
% 3.63/1.01  --bc_imp_inh                            [conj_cone]
% 3.63/1.01  --conj_cone_tolerance                   3.
% 3.63/1.01  --extra_neg_conj                        none
% 3.63/1.01  --large_theory_mode                     true
% 3.63/1.01  --prolific_symb_bound                   200
% 3.63/1.01  --lt_threshold                          2000
% 3.63/1.01  --clause_weak_htbl                      true
% 3.63/1.01  --gc_record_bc_elim                     false
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing Options
% 3.63/1.01  
% 3.63/1.01  --preprocessing_flag                    true
% 3.63/1.01  --time_out_prep_mult                    0.1
% 3.63/1.01  --splitting_mode                        input
% 3.63/1.01  --splitting_grd                         true
% 3.63/1.01  --splitting_cvd                         false
% 3.63/1.01  --splitting_cvd_svl                     false
% 3.63/1.01  --splitting_nvd                         32
% 3.63/1.01  --sub_typing                            true
% 3.63/1.01  --prep_gs_sim                           true
% 3.63/1.01  --prep_unflatten                        true
% 3.63/1.01  --prep_res_sim                          true
% 3.63/1.01  --prep_upred                            true
% 3.63/1.01  --prep_sem_filter                       exhaustive
% 3.63/1.01  --prep_sem_filter_out                   false
% 3.63/1.01  --pred_elim                             true
% 3.63/1.01  --res_sim_input                         true
% 3.63/1.01  --eq_ax_congr_red                       true
% 3.63/1.01  --pure_diseq_elim                       true
% 3.63/1.01  --brand_transform                       false
% 3.63/1.01  --non_eq_to_eq                          false
% 3.63/1.01  --prep_def_merge                        true
% 3.63/1.01  --prep_def_merge_prop_impl              false
% 3.63/1.01  --prep_def_merge_mbd                    true
% 3.63/1.01  --prep_def_merge_tr_red                 false
% 3.63/1.01  --prep_def_merge_tr_cl                  false
% 3.63/1.01  --smt_preprocessing                     true
% 3.63/1.01  --smt_ac_axioms                         fast
% 3.63/1.01  --preprocessed_out                      false
% 3.63/1.01  --preprocessed_stats                    false
% 3.63/1.01  
% 3.63/1.01  ------ Abstraction refinement Options
% 3.63/1.01  
% 3.63/1.01  --abstr_ref                             []
% 3.63/1.01  --abstr_ref_prep                        false
% 3.63/1.01  --abstr_ref_until_sat                   false
% 3.63/1.01  --abstr_ref_sig_restrict                funpre
% 3.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.01  --abstr_ref_under                       []
% 3.63/1.01  
% 3.63/1.01  ------ SAT Options
% 3.63/1.01  
% 3.63/1.01  --sat_mode                              false
% 3.63/1.01  --sat_fm_restart_options                ""
% 3.63/1.01  --sat_gr_def                            false
% 3.63/1.01  --sat_epr_types                         true
% 3.63/1.01  --sat_non_cyclic_types                  false
% 3.63/1.01  --sat_finite_models                     false
% 3.63/1.01  --sat_fm_lemmas                         false
% 3.63/1.01  --sat_fm_prep                           false
% 3.63/1.01  --sat_fm_uc_incr                        true
% 3.63/1.01  --sat_out_model                         small
% 3.63/1.01  --sat_out_clauses                       false
% 3.63/1.01  
% 3.63/1.01  ------ QBF Options
% 3.63/1.01  
% 3.63/1.01  --qbf_mode                              false
% 3.63/1.01  --qbf_elim_univ                         false
% 3.63/1.01  --qbf_dom_inst                          none
% 3.63/1.01  --qbf_dom_pre_inst                      false
% 3.63/1.01  --qbf_sk_in                             false
% 3.63/1.01  --qbf_pred_elim                         true
% 3.63/1.01  --qbf_split                             512
% 3.63/1.01  
% 3.63/1.01  ------ BMC1 Options
% 3.63/1.01  
% 3.63/1.01  --bmc1_incremental                      false
% 3.63/1.01  --bmc1_axioms                           reachable_all
% 3.63/1.01  --bmc1_min_bound                        0
% 3.63/1.01  --bmc1_max_bound                        -1
% 3.63/1.01  --bmc1_max_bound_default                -1
% 3.63/1.01  --bmc1_symbol_reachability              true
% 3.63/1.01  --bmc1_property_lemmas                  false
% 3.63/1.01  --bmc1_k_induction                      false
% 3.63/1.01  --bmc1_non_equiv_states                 false
% 3.63/1.01  --bmc1_deadlock                         false
% 3.63/1.01  --bmc1_ucm                              false
% 3.63/1.01  --bmc1_add_unsat_core                   none
% 3.63/1.01  --bmc1_unsat_core_children              false
% 3.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.01  --bmc1_out_stat                         full
% 3.63/1.01  --bmc1_ground_init                      false
% 3.63/1.01  --bmc1_pre_inst_next_state              false
% 3.63/1.01  --bmc1_pre_inst_state                   false
% 3.63/1.01  --bmc1_pre_inst_reach_state             false
% 3.63/1.01  --bmc1_out_unsat_core                   false
% 3.63/1.01  --bmc1_aig_witness_out                  false
% 3.63/1.01  --bmc1_verbose                          false
% 3.63/1.01  --bmc1_dump_clauses_tptp                false
% 3.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.01  --bmc1_dump_file                        -
% 3.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.01  --bmc1_ucm_extend_mode                  1
% 3.63/1.01  --bmc1_ucm_init_mode                    2
% 3.63/1.01  --bmc1_ucm_cone_mode                    none
% 3.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.01  --bmc1_ucm_relax_model                  4
% 3.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.01  --bmc1_ucm_layered_model                none
% 3.63/1.01  --bmc1_ucm_max_lemma_size               10
% 3.63/1.01  
% 3.63/1.01  ------ AIG Options
% 3.63/1.01  
% 3.63/1.01  --aig_mode                              false
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation Options
% 3.63/1.01  
% 3.63/1.01  --instantiation_flag                    true
% 3.63/1.01  --inst_sos_flag                         true
% 3.63/1.01  --inst_sos_phase                        true
% 3.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel_side                     none
% 3.63/1.01  --inst_solver_per_active                1400
% 3.63/1.01  --inst_solver_calls_frac                1.
% 3.63/1.01  --inst_passive_queue_type               priority_queues
% 3.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.01  --inst_passive_queues_freq              [25;2]
% 3.63/1.01  --inst_dismatching                      true
% 3.63/1.01  --inst_eager_unprocessed_to_passive     true
% 3.63/1.01  --inst_prop_sim_given                   true
% 3.63/1.01  --inst_prop_sim_new                     false
% 3.63/1.01  --inst_subs_new                         false
% 3.63/1.01  --inst_eq_res_simp                      false
% 3.63/1.01  --inst_subs_given                       false
% 3.63/1.01  --inst_orphan_elimination               true
% 3.63/1.01  --inst_learning_loop_flag               true
% 3.63/1.01  --inst_learning_start                   3000
% 3.63/1.01  --inst_learning_factor                  2
% 3.63/1.01  --inst_start_prop_sim_after_learn       3
% 3.63/1.01  --inst_sel_renew                        solver
% 3.63/1.01  --inst_lit_activity_flag                true
% 3.63/1.01  --inst_restr_to_given                   false
% 3.63/1.01  --inst_activity_threshold               500
% 3.63/1.01  --inst_out_proof                        true
% 3.63/1.01  
% 3.63/1.01  ------ Resolution Options
% 3.63/1.01  
% 3.63/1.01  --resolution_flag                       false
% 3.63/1.01  --res_lit_sel                           adaptive
% 3.63/1.01  --res_lit_sel_side                      none
% 3.63/1.01  --res_ordering                          kbo
% 3.63/1.01  --res_to_prop_solver                    active
% 3.63/1.01  --res_prop_simpl_new                    false
% 3.63/1.01  --res_prop_simpl_given                  true
% 3.63/1.01  --res_passive_queue_type                priority_queues
% 3.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.01  --res_passive_queues_freq               [15;5]
% 3.63/1.01  --res_forward_subs                      full
% 3.63/1.01  --res_backward_subs                     full
% 3.63/1.01  --res_forward_subs_resolution           true
% 3.63/1.01  --res_backward_subs_resolution          true
% 3.63/1.01  --res_orphan_elimination                true
% 3.63/1.01  --res_time_limit                        2.
% 3.63/1.01  --res_out_proof                         true
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Options
% 3.63/1.01  
% 3.63/1.01  --superposition_flag                    true
% 3.63/1.01  --sup_passive_queue_type                priority_queues
% 3.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.01  --demod_completeness_check              fast
% 3.63/1.01  --demod_use_ground                      true
% 3.63/1.01  --sup_to_prop_solver                    passive
% 3.63/1.01  --sup_prop_simpl_new                    true
% 3.63/1.01  --sup_prop_simpl_given                  true
% 3.63/1.01  --sup_fun_splitting                     true
% 3.63/1.01  --sup_smt_interval                      50000
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Simplification Setup
% 3.63/1.01  
% 3.63/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_immed_triv                        [TrivRules]
% 3.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_bw_main                     []
% 3.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_input_bw                          []
% 3.63/1.01  
% 3.63/1.01  ------ Combination Options
% 3.63/1.01  
% 3.63/1.01  --comb_res_mult                         3
% 3.63/1.01  --comb_sup_mult                         2
% 3.63/1.01  --comb_inst_mult                        10
% 3.63/1.01  
% 3.63/1.01  ------ Debug Options
% 3.63/1.01  
% 3.63/1.01  --dbg_backtrace                         false
% 3.63/1.01  --dbg_dump_prop_clauses                 false
% 3.63/1.01  --dbg_dump_prop_clauses_file            -
% 3.63/1.01  --dbg_out_stat                          false
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  ------ Proving...
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  % SZS status Theorem for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01   Resolution empty clause
% 3.63/1.01  
% 3.63/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  fof(f20,axiom,(
% 3.63/1.01    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f57,plain,(
% 3.63/1.01    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f20])).
% 3.63/1.01  
% 3.63/1.01  fof(f11,axiom,(
% 3.63/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f44,plain,(
% 3.63/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f11])).
% 3.63/1.01  
% 3.63/1.01  fof(f12,axiom,(
% 3.63/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f45,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f12])).
% 3.63/1.01  
% 3.63/1.01  fof(f13,axiom,(
% 3.63/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f46,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f13])).
% 3.63/1.01  
% 3.63/1.01  fof(f14,axiom,(
% 3.63/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f47,plain,(
% 3.63/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f14])).
% 3.63/1.01  
% 3.63/1.01  fof(f15,axiom,(
% 3.63/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f48,plain,(
% 3.63/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f15])).
% 3.63/1.01  
% 3.63/1.01  fof(f16,axiom,(
% 3.63/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f49,plain,(
% 3.63/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f16])).
% 3.63/1.01  
% 3.63/1.01  fof(f17,axiom,(
% 3.63/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f50,plain,(
% 3.63/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f17])).
% 3.63/1.01  
% 3.63/1.01  fof(f63,plain,(
% 3.63/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f49,f50])).
% 3.63/1.01  
% 3.63/1.01  fof(f64,plain,(
% 3.63/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f48,f63])).
% 3.63/1.01  
% 3.63/1.01  fof(f65,plain,(
% 3.63/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f47,f64])).
% 3.63/1.01  
% 3.63/1.01  fof(f66,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f46,f65])).
% 3.63/1.01  
% 3.63/1.01  fof(f67,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f45,f66])).
% 3.63/1.01  
% 3.63/1.01  fof(f71,plain,(
% 3.63/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f44,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f82,plain,(
% 3.63/1.01    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.63/1.01    inference(definition_unfolding,[],[f57,f71])).
% 3.63/1.01  
% 3.63/1.01  fof(f6,axiom,(
% 3.63/1.01    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f39,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f6])).
% 3.63/1.01  
% 3.63/1.01  fof(f19,axiom,(
% 3.63/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f56,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.63/1.01    inference(cnf_transformation,[],[f19])).
% 3.63/1.01  
% 3.63/1.01  fof(f68,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.63/1.01    inference(definition_unfolding,[],[f56,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f76,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 3.63/1.01    inference(definition_unfolding,[],[f39,f68,f68,f68,f68])).
% 3.63/1.01  
% 3.63/1.01  fof(f4,axiom,(
% 3.63/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f26,plain,(
% 3.63/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.63/1.01    inference(nnf_transformation,[],[f4])).
% 3.63/1.01  
% 3.63/1.01  fof(f36,plain,(
% 3.63/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f26])).
% 3.63/1.01  
% 3.63/1.01  fof(f2,axiom,(
% 3.63/1.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f34,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f2])).
% 3.63/1.01  
% 3.63/1.01  fof(f10,axiom,(
% 3.63/1.01    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f43,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f10])).
% 3.63/1.01  
% 3.63/1.01  fof(f69,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f43,f68])).
% 3.63/1.01  
% 3.63/1.01  fof(f70,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f34,f69])).
% 3.63/1.01  
% 3.63/1.01  fof(f74,plain,(
% 3.63/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0) )),
% 3.63/1.01    inference(definition_unfolding,[],[f36,f70])).
% 3.63/1.01  
% 3.63/1.01  fof(f18,axiom,(
% 3.63/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f24,plain,(
% 3.63/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f18])).
% 3.63/1.01  
% 3.63/1.01  fof(f27,plain,(
% 3.63/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.63/1.01    inference(nnf_transformation,[],[f24])).
% 3.63/1.01  
% 3.63/1.01  fof(f28,plain,(
% 3.63/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.63/1.01    inference(flattening,[],[f27])).
% 3.63/1.01  
% 3.63/1.01  fof(f51,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.63/1.01    inference(cnf_transformation,[],[f28])).
% 3.63/1.01  
% 3.63/1.01  fof(f81,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.63/1.01    inference(definition_unfolding,[],[f51,f67,f71,f71,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f21,conjecture,(
% 3.63/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f22,negated_conjecture,(
% 3.63/1.01    ~! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.63/1.01    inference(negated_conjecture,[],[f21])).
% 3.63/1.01  
% 3.63/1.01  fof(f25,plain,(
% 3.63/1.01    ? [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f22])).
% 3.63/1.01  
% 3.63/1.01  fof(f29,plain,(
% 3.63/1.01    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 3.63/1.01    inference(nnf_transformation,[],[f25])).
% 3.63/1.01  
% 3.63/1.01  fof(f30,plain,(
% 3.63/1.01    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 3.63/1.01    inference(flattening,[],[f29])).
% 3.63/1.01  
% 3.63/1.01  fof(f31,plain,(
% 3.63/1.01    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0)) => (((k2_tarski(sK1,sK2) != sK0 & k1_tarski(sK2) != sK0 & k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0) | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0) & (k2_tarski(sK1,sK2) = sK0 | k1_tarski(sK2) = sK0 | k1_tarski(sK1) = sK0 | k1_xboole_0 = sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0))),
% 3.63/1.01    introduced(choice_axiom,[])).
% 3.63/1.01  
% 3.63/1.01  fof(f32,plain,(
% 3.63/1.01    ((k2_tarski(sK1,sK2) != sK0 & k1_tarski(sK2) != sK0 & k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0) | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0) & (k2_tarski(sK1,sK2) = sK0 | k1_tarski(sK2) = sK0 | k1_tarski(sK1) = sK0 | k1_xboole_0 = sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0)),
% 3.63/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f31])).
% 3.63/1.01  
% 3.63/1.01  fof(f58,plain,(
% 3.63/1.01    k2_tarski(sK1,sK2) = sK0 | k1_tarski(sK2) = sK0 | k1_tarski(sK1) = sK0 | k1_xboole_0 = sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0),
% 3.63/1.01    inference(cnf_transformation,[],[f32])).
% 3.63/1.01  
% 3.63/1.01  fof(f87,plain,(
% 3.63/1.01    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0 | k1_xboole_0 = sK0 | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) = k1_xboole_0),
% 3.63/1.01    inference(definition_unfolding,[],[f58,f67,f71,f71,f70,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f37,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f26])).
% 3.63/1.01  
% 3.63/1.01  fof(f73,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.63/1.01    inference(definition_unfolding,[],[f37,f70])).
% 3.63/1.01  
% 3.63/1.01  fof(f8,axiom,(
% 3.63/1.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f41,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f8])).
% 3.63/1.01  
% 3.63/1.01  fof(f1,axiom,(
% 3.63/1.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f33,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f1])).
% 3.63/1.01  
% 3.63/1.01  fof(f61,plain,(
% 3.63/1.01    k1_tarski(sK2) != sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0),
% 3.63/1.01    inference(cnf_transformation,[],[f32])).
% 3.63/1.01  
% 3.63/1.01  fof(f84,plain,(
% 3.63/1.01    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0 | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0),
% 3.63/1.01    inference(definition_unfolding,[],[f61,f71,f70,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f59,plain,(
% 3.63/1.01    k1_xboole_0 != sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0),
% 3.63/1.01    inference(cnf_transformation,[],[f32])).
% 3.63/1.01  
% 3.63/1.01  fof(f86,plain,(
% 3.63/1.01    k1_xboole_0 != sK0 | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0),
% 3.63/1.01    inference(definition_unfolding,[],[f59,f70,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f60,plain,(
% 3.63/1.01    k1_tarski(sK1) != sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0),
% 3.63/1.01    inference(cnf_transformation,[],[f32])).
% 3.63/1.01  
% 3.63/1.01  fof(f85,plain,(
% 3.63/1.01    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0),
% 3.63/1.01    inference(definition_unfolding,[],[f60,f71,f70,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f62,plain,(
% 3.63/1.01    k2_tarski(sK1,sK2) != sK0 | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0),
% 3.63/1.01    inference(cnf_transformation,[],[f32])).
% 3.63/1.01  
% 3.63/1.01  fof(f83,plain,(
% 3.63/1.01    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0 | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0),
% 3.63/1.01    inference(definition_unfolding,[],[f62,f67,f70,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f54,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f28])).
% 3.63/1.01  
% 3.63/1.01  fof(f78,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 3.63/1.01    inference(definition_unfolding,[],[f54,f67,f71])).
% 3.63/1.01  
% 3.63/1.01  fof(f89,plain,(
% 3.63/1.01    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.63/1.01    inference(equality_resolution,[],[f78])).
% 3.63/1.01  
% 3.63/1.01  fof(f5,axiom,(
% 3.63/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f38,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f5])).
% 3.63/1.01  
% 3.63/1.01  fof(f75,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))) )),
% 3.63/1.01    inference(definition_unfolding,[],[f38,f70,f70,f68])).
% 3.63/1.01  
% 3.63/1.01  fof(f7,axiom,(
% 3.63/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f40,plain,(
% 3.63/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f7])).
% 3.63/1.01  
% 3.63/1.01  fof(f9,axiom,(
% 3.63/1.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f42,plain,(
% 3.63/1.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f9])).
% 3.63/1.01  
% 3.63/1.01  fof(f53,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f28])).
% 3.63/1.01  
% 3.63/1.01  fof(f79,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.63/1.01    inference(definition_unfolding,[],[f53,f67,f71])).
% 3.63/1.01  
% 3.63/1.01  fof(f90,plain,(
% 3.63/1.01    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.63/1.01    inference(equality_resolution,[],[f79])).
% 3.63/1.01  
% 3.63/1.01  fof(f52,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 3.63/1.01    inference(cnf_transformation,[],[f28])).
% 3.63/1.01  
% 3.63/1.01  fof(f80,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 3.63/1.01    inference(definition_unfolding,[],[f52,f67])).
% 3.63/1.01  
% 3.63/1.01  fof(f91,plain,(
% 3.63/1.01    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.63/1.01    inference(equality_resolution,[],[f80])).
% 3.63/1.01  
% 3.63/1.01  cnf(c_14,plain,
% 3.63/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5,plain,
% 3.63/1.01      ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 3.63/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_932,plain,
% 3.63/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_14,c_5]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_3,plain,
% 3.63/1.01      ( r1_tarski(X0,X1)
% 3.63/1.01      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_80,plain,
% 3.63/1.01      ( r1_tarski(X0,X1)
% 3.63/1.01      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
% 3.63/1.01      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_13,plain,
% 3.63/1.01      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.63/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 3.63/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.63/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.63/1.01      | k1_xboole_0 = X0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_197,plain,
% 3.63/1.01      ( X0 != X1
% 3.63/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) != X4
% 3.63/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0
% 3.63/1.01      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) = X0
% 3.63/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.63/1.01      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X4),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X4)))) != k1_xboole_0
% 3.63/1.01      | k1_xboole_0 = X0 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_80,c_13]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_198,plain,
% 3.63/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.63/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 3.63/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 3.63/1.01      | k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) != k1_xboole_0
% 3.63/1.01      | k1_xboole_0 = X2 ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_197]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_19,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) = k1_xboole_0
% 3.63/1.01      | k1_xboole_0 = sK0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_266,plain,
% 3.63/1.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k1_xboole_0 = sK0 ),
% 3.63/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_198,c_19]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_933,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k3_tarski(k6_enumset1(k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),X0))
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_266,c_5]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_943,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k3_tarski(k6_enumset1(k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),k3_tarski(sK0),X0)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_932,c_933]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2,plain,
% 3.63/1.01      ( ~ r1_tarski(X0,X1)
% 3.63/1.01      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_7,plain,
% 3.63/1.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_0,plain,
% 3.63/1.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_284,plain,
% 3.63/1.01      ( ~ r1_tarski(X0,X1)
% 3.63/1.01      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_2,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_561,plain,
% 3.63/1.01      ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) = k1_xboole_0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_284]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_287,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_555,plain,
% 3.63/1.01      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_287]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_576,plain,
% 3.63/1.01      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_555]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_286,plain,( X0 = X0 ),theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_643,plain,
% 3.63/1.01      ( sK0 = sK0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_286]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_16,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_280,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_16,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_18,negated_conjecture,
% 3.63/1.01      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0
% 3.63/1.01      | k1_xboole_0 != sK0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_278,negated_conjecture,
% 3.63/1.01      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0
% 3.63/1.01      | sK0 != k1_xboole_0 ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_18,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_17,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_279,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_17,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_15,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) != k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_281,negated_conjecture,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != sK0
% 3.63/1.01      | k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_15,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_645,negated_conjecture,
% 3.63/1.01      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) != k1_xboole_0 ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_280,c_266,c_278,c_279,c_281,c_576,c_643]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_577,plain,
% 3.63/1.01      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_287]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_597,plain,
% 3.63/1.01      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_577]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_710,plain,
% 3.63/1.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK0
% 3.63/1.01      | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.63/1.01      | sK0 != sK0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_597]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_732,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_286]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_10,plain,
% 3.63/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_854,plain,
% 3.63/1.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_291,plain,
% 3.63/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.63/1.01      theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_569,plain,
% 3.63/1.01      ( ~ r1_tarski(X0,X1)
% 3.63/1.01      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X1
% 3.63/1.01      | sK0 != X0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_777,plain,
% 3.63/1.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
% 3.63/1.01      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != X0
% 3.63/1.01      | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_569]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1157,plain,
% 3.63/1.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))
% 3.63/1.01      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)
% 3.63/1.01      | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_777]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1159,plain,
% 3.63/1.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.63/1.01      | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_1157]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1272,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_943,c_266,c_278,c_279,c_280,c_281,c_561,c_576,c_643,
% 3.63/1.01                 c_710,c_732,c_854,c_1159]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1273,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = sK0
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(renaming,[status(thm)],[c_1272]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_4,plain,
% 3.63/1.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
% 3.63/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_282,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 3.63/1.01      inference(theory_normalisation,[status(thm)],[c_4,c_7,c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_539,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_282,c_5]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_540,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 3.63/1.01      inference(light_normalisation,[status(thm)],[c_539,c_14]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_6,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_8,plain,
% 3.63/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_541,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_540,c_6,c_8]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_647,plain,
% 3.63/1.01      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) != k1_xboole_0 ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_645,c_541]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1282,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_1273,c_647]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1284,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | sK0 = k1_xboole_0
% 3.63/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_1282,c_8,c_14]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1285,plain,
% 3.63/1.01      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(equality_resolution_simp,[status(thm)],[c_1284]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_11,plain,
% 3.63/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_533,plain,
% 3.63/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2227,plain,
% 3.63/1.01      ( sK0 = k1_xboole_0
% 3.63/1.01      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = iProver_top ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_1285,c_533]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_537,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0
% 3.63/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_9968,plain,
% 3.63/1.01      ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0
% 3.63/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_537,c_541]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_9980,plain,
% 3.63/1.01      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
% 3.63/1.01      | sK0 = k1_xboole_0 ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_2227,c_9968]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_12,plain,
% 3.63/1.01      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2646,plain,
% 3.63/1.01      ( r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_766,plain,
% 3.63/1.01      ( r1_tarski(X0,X1)
% 3.63/1.01      | ~ r1_tarski(k1_xboole_0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
% 3.63/1.01      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
% 3.63/1.01      | X0 != k1_xboole_0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1901,plain,
% 3.63/1.01      ( r1_tarski(sK0,X0)
% 3.63/1.01      | ~ r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.63/1.01      | X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
% 3.63/1.01      | sK0 != k1_xboole_0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_766]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5489,plain,
% 3.63/1.01      ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.63/1.01      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.63/1.01      | sK0 != k1_xboole_0 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_1901]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_10247,plain,
% 3.63/1.01      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0 ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_9980,c_266,c_278,c_279,c_280,c_281,c_561,c_576,c_643,
% 3.63/1.01                 c_732,c_2646,c_5489]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_10250,plain,
% 3.63/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.63/1.01      inference(demodulation,[status(thm)],[c_10247,c_647]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_10251,plain,
% 3.63/1.01      ( $false ),
% 3.63/1.01      inference(equality_resolution_simp,[status(thm)],[c_10250]) ).
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  ------                               Statistics
% 3.63/1.01  
% 3.63/1.01  ------ General
% 3.63/1.01  
% 3.63/1.01  abstr_ref_over_cycles:                  0
% 3.63/1.01  abstr_ref_under_cycles:                 0
% 3.63/1.01  gc_basic_clause_elim:                   0
% 3.63/1.01  forced_gc_time:                         0
% 3.63/1.01  parsing_time:                           0.015
% 3.63/1.01  unif_index_cands_time:                  0.
% 3.63/1.01  unif_index_add_time:                    0.
% 3.63/1.01  orderings_time:                         0.
% 3.63/1.01  out_proof_time:                         0.015
% 3.63/1.01  total_time:                             0.397
% 3.63/1.01  num_of_symbols:                         39
% 3.63/1.01  num_of_terms:                           12483
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing
% 3.63/1.01  
% 3.63/1.01  num_of_splits:                          0
% 3.63/1.01  num_of_split_atoms:                     0
% 3.63/1.01  num_of_reused_defs:                     0
% 3.63/1.01  num_eq_ax_congr_red:                    0
% 3.63/1.01  num_of_sem_filtered_clauses:            1
% 3.63/1.01  num_of_subtypes:                        0
% 3.63/1.01  monotx_restored_types:                  0
% 3.63/1.01  sat_num_of_epr_types:                   0
% 3.63/1.01  sat_num_of_non_cyclic_types:            0
% 3.63/1.01  sat_guarded_non_collapsed_types:        0
% 3.63/1.01  num_pure_diseq_elim:                    0
% 3.63/1.01  simp_replaced_by:                       0
% 3.63/1.01  res_preprocessed:                       73
% 3.63/1.01  prep_upred:                             0
% 3.63/1.01  prep_unflattend:                        22
% 3.63/1.01  smt_new_axioms:                         0
% 3.63/1.01  pred_elim_cands:                        1
% 3.63/1.01  pred_elim:                              0
% 3.63/1.01  pred_elim_cl:                           0
% 3.63/1.01  pred_elim_cycles:                       1
% 3.63/1.01  merged_defs:                            6
% 3.63/1.01  merged_defs_ncl:                        0
% 3.63/1.01  bin_hyper_res:                          6
% 3.63/1.01  prep_cycles:                            3
% 3.63/1.01  pred_elim_time:                         0.004
% 3.63/1.01  splitting_time:                         0.
% 3.63/1.01  sem_filter_time:                        0.
% 3.63/1.01  monotx_time:                            0.
% 3.63/1.01  subtype_inf_time:                       0.
% 3.63/1.01  
% 3.63/1.01  ------ Problem properties
% 3.63/1.01  
% 3.63/1.01  clauses:                                20
% 3.63/1.01  conjectures:                            4
% 3.63/1.01  epr:                                    0
% 3.63/1.01  horn:                                   18
% 3.63/1.01  ground:                                 5
% 3.63/1.01  unary:                                  11
% 3.63/1.01  binary:                                 7
% 3.63/1.01  lits:                                   34
% 3.63/1.01  lits_eq:                                26
% 3.63/1.01  fd_pure:                                0
% 3.63/1.01  fd_pseudo:                              0
% 3.63/1.01  fd_cond:                                0
% 3.63/1.01  fd_pseudo_cond:                         1
% 3.63/1.01  ac_symbols:                             1
% 3.63/1.01  
% 3.63/1.01  ------ Propositional Solver
% 3.63/1.01  
% 3.63/1.01  prop_solver_calls:                      26
% 3.63/1.01  prop_fast_solver_calls:                 489
% 3.63/1.01  smt_solver_calls:                       0
% 3.63/1.01  smt_fast_solver_calls:                  0
% 3.63/1.01  prop_num_of_clauses:                    2433
% 3.63/1.01  prop_preprocess_simplified:             6177
% 3.63/1.01  prop_fo_subsumed:                       10
% 3.63/1.01  prop_solver_time:                       0.
% 3.63/1.01  smt_solver_time:                        0.
% 3.63/1.01  smt_fast_solver_time:                   0.
% 3.63/1.01  prop_fast_solver_time:                  0.
% 3.63/1.01  prop_unsat_core_time:                   0.
% 3.63/1.01  
% 3.63/1.01  ------ QBF
% 3.63/1.01  
% 3.63/1.01  qbf_q_res:                              0
% 3.63/1.01  qbf_num_tautologies:                    0
% 3.63/1.01  qbf_prep_cycles:                        0
% 3.63/1.01  
% 3.63/1.01  ------ BMC1
% 3.63/1.01  
% 3.63/1.01  bmc1_current_bound:                     -1
% 3.63/1.01  bmc1_last_solved_bound:                 -1
% 3.63/1.01  bmc1_unsat_core_size:                   -1
% 3.63/1.01  bmc1_unsat_core_parents_size:           -1
% 3.63/1.01  bmc1_merge_next_fun:                    0
% 3.63/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation
% 3.63/1.01  
% 3.63/1.01  inst_num_of_clauses:                    809
% 3.63/1.01  inst_num_in_passive:                    164
% 3.63/1.01  inst_num_in_active:                     330
% 3.63/1.01  inst_num_in_unprocessed:                315
% 3.63/1.01  inst_num_of_loops:                      380
% 3.63/1.01  inst_num_of_learning_restarts:          0
% 3.63/1.01  inst_num_moves_active_passive:          47
% 3.63/1.01  inst_lit_activity:                      0
% 3.63/1.01  inst_lit_activity_moves:                0
% 3.63/1.01  inst_num_tautologies:                   0
% 3.63/1.01  inst_num_prop_implied:                  0
% 3.63/1.01  inst_num_existing_simplified:           0
% 3.63/1.01  inst_num_eq_res_simplified:             0
% 3.63/1.01  inst_num_child_elim:                    0
% 3.63/1.01  inst_num_of_dismatching_blockings:      668
% 3.63/1.01  inst_num_of_non_proper_insts:           1160
% 3.63/1.01  inst_num_of_duplicates:                 0
% 3.63/1.01  inst_inst_num_from_inst_to_res:         0
% 3.63/1.01  inst_dismatching_checking_time:         0.
% 3.63/1.01  
% 3.63/1.01  ------ Resolution
% 3.63/1.01  
% 3.63/1.01  res_num_of_clauses:                     0
% 3.63/1.01  res_num_in_passive:                     0
% 3.63/1.01  res_num_in_active:                      0
% 3.63/1.01  res_num_of_loops:                       76
% 3.63/1.01  res_forward_subset_subsumed:            206
% 3.63/1.01  res_backward_subset_subsumed:           2
% 3.63/1.01  res_forward_subsumed:                   1
% 3.63/1.01  res_backward_subsumed:                  0
% 3.63/1.01  res_forward_subsumption_resolution:     0
% 3.63/1.01  res_backward_subsumption_resolution:    1
% 3.63/1.01  res_clause_to_clause_subsumption:       8544
% 3.63/1.01  res_orphan_elimination:                 0
% 3.63/1.01  res_tautology_del:                      123
% 3.63/1.01  res_num_eq_res_simplified:              0
% 3.63/1.01  res_num_sel_changes:                    0
% 3.63/1.01  res_moves_from_active_to_pass:          0
% 3.63/1.01  
% 3.63/1.01  ------ Superposition
% 3.63/1.01  
% 3.63/1.01  sup_time_total:                         0.
% 3.63/1.01  sup_time_generating:                    0.
% 3.63/1.01  sup_time_sim_full:                      0.
% 3.63/1.01  sup_time_sim_immed:                     0.
% 3.63/1.01  
% 3.63/1.01  sup_num_of_clauses:                     389
% 3.63/1.01  sup_num_in_active:                      66
% 3.63/1.01  sup_num_in_passive:                     323
% 3.63/1.01  sup_num_of_loops:                       75
% 3.63/1.01  sup_fw_superposition:                   2423
% 3.63/1.01  sup_bw_superposition:                   1520
% 3.63/1.01  sup_immediate_simplified:               1163
% 3.63/1.01  sup_given_eliminated:                   3
% 3.63/1.01  comparisons_done:                       0
% 3.63/1.01  comparisons_avoided:                    27
% 3.63/1.01  
% 3.63/1.01  ------ Simplifications
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  sim_fw_subset_subsumed:                 9
% 3.63/1.01  sim_bw_subset_subsumed:                 1
% 3.63/1.01  sim_fw_subsumed:                        88
% 3.63/1.01  sim_bw_subsumed:                        7
% 3.63/1.01  sim_fw_subsumption_res:                 0
% 3.63/1.01  sim_bw_subsumption_res:                 0
% 3.63/1.01  sim_tautology_del:                      0
% 3.63/1.01  sim_eq_tautology_del:                   201
% 3.63/1.01  sim_eq_res_simp:                        9
% 3.63/1.01  sim_fw_demodulated:                     656
% 3.63/1.01  sim_bw_demodulated:                     23
% 3.63/1.01  sim_light_normalised:                   478
% 3.63/1.01  sim_joinable_taut:                      100
% 3.63/1.01  sim_joinable_simp:                      0
% 3.63/1.01  sim_ac_normalised:                      0
% 3.63/1.01  sim_smt_subsumption:                    0
% 3.63/1.01  
%------------------------------------------------------------------------------
