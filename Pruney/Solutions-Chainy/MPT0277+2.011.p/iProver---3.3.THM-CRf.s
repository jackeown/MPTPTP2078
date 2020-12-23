%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:30 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  172 (90666 expanded)
%              Number of clauses        :   96 (11432 expanded)
%              Number of leaves         :   20 (27936 expanded)
%              Depth                    :   43
%              Number of atoms          :  461 (138331 expanded)
%              Number of equality atoms :  427 (135910 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,
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
   => ( ( ( k2_tarski(sK3,sK4) != sK2
          & k1_tarski(sK4) != sK2
          & k1_tarski(sK3) != sK2
          & k1_xboole_0 != sK2 )
        | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 )
      & ( k2_tarski(sK3,sK4) = sK2
        | k1_tarski(sK4) = sK2
        | k1_tarski(sK3) = sK2
        | k1_xboole_0 = sK2
        | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( k2_tarski(sK3,sK4) != sK2
        & k1_tarski(sK4) != sK2
        & k1_tarski(sK3) != sK2
        & k1_xboole_0 != sK2 )
      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 )
    & ( k2_tarski(sK3,sK4) = sK2
      | k1_tarski(sK4) = sK2
      | k1_tarski(sK3) = sK2
      | k1_xboole_0 = sK2
      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f41])).

fof(f71,plain,
    ( k2_tarski(sK3,sK4) = sK2
    | k1_tarski(sK4) = sK2
    | k1_tarski(sK3) = sK2
    | k1_xboole_0 = sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f96,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k1_xboole_0 = sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f71,f78,f82,f82,f81,f78])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f79])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X1,X1,X1,X1,X1,X2) = X0
      | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f65,f78,f82,f82,f78])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f68,f78,f82])).

fof(f99,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f88])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f74,plain,
    ( k1_tarski(sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f74,f82,f81,f78])).

fof(f75,plain,
    ( k2_tarski(sK3,sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f75,f78,f81,f78])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f67,f78,f82])).

fof(f100,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f73,plain,
    ( k1_tarski(sK3) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f73,f82,f81,f78])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,
    ( k1_xboole_0 != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f72,f81,f78])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f101,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) = k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1117,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_24])).

cnf(c_1124,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_778,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_3,c_14])).

cnf(c_1130,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1124,c_778])).

cnf(c_1247,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1117,c_1130])).

cnf(c_1249,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1247,c_13])).

cnf(c_1254,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0)) = X0
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1249,c_778])).

cnf(c_1288,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_1254])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1296,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1288,c_9])).

cnf(c_1126,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_1291,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0),X0)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1254,c_1126])).

cnf(c_1615,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),X0),X0)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1296,c_1291])).

cnf(c_504,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_894,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_505,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_823,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_847,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_995,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
    | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0
    | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_801,plain,
    ( ~ r1_tarski(sK2,k4_enumset1(X0,X0,X0,X0,X0,X1))
    | k4_enumset1(X0,X0,X0,X0,X0,X1) = sK2
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = sK2
    | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1261,plain,
    ( ~ r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
    | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_768,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1613,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_768])).

cnf(c_1625,plain,
    ( r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
    | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1613])).

cnf(c_1705,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1615,c_894,c_995,c_1261,c_1625])).

cnf(c_1706,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1705])).

cnf(c_16,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_766,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2434,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,k4_enumset1(X0,X0,X0,X0,X0,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1706,c_766])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_771,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4403,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X0,X0,X0,X0,X0,sK4))) = k4_enumset1(X0,X0,X0,X0,X0,sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2434,c_771])).

cnf(c_21,negated_conjecture,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1119,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_21])).

cnf(c_1222,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1119,c_1130])).

cnf(c_6460,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4403,c_1222])).

cnf(c_6463,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6460,c_14])).

cnf(c_6464,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6463])).

cnf(c_6556,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6464,c_1706])).

cnf(c_6564,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6556,c_1222])).

cnf(c_6571,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6564,c_3,c_14])).

cnf(c_6572,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6571])).

cnf(c_20,negated_conjecture,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1120,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_20])).

cnf(c_1246,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1120,c_1130])).

cnf(c_6562,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6556,c_1246])).

cnf(c_6573,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6562,c_3,c_14])).

cnf(c_6574,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6573])).

cnf(c_7688,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6572,c_6556,c_6574])).

cnf(c_1707,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1706,c_3])).

cnf(c_2126,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1707,c_1222])).

cnf(c_2133,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2126,c_3,c_14])).

cnf(c_2134,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2133])).

cnf(c_2124,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1707,c_1246])).

cnf(c_2135,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2124,c_3,c_14])).

cnf(c_2136,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
    | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2135])).

cnf(c_2143,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_1707,c_2136])).

cnf(c_17,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_765,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2145,plain,
    ( k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2143,c_765])).

cnf(c_4402,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0))) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2145,c_771])).

cnf(c_22,negated_conjecture,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1118,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_22])).

cnf(c_1221,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1118,c_1130])).

cnf(c_5385,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4402,c_1221])).

cnf(c_5387,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5385,c_14])).

cnf(c_5388,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5387])).

cnf(c_5406,plain,
    ( k3_tarski(sK2) = sK4
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5388,c_2143])).

cnf(c_7692,plain,
    ( k3_tarski(sK2) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7688,c_3])).

cnf(c_7832,plain,
    ( sK2 = k1_xboole_0
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_5406,c_7692])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1121,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13,c_23])).

cnf(c_1208,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1121,c_1130])).

cnf(c_7851,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_7832,c_1208])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_764,plain,
    ( r1_tarski(k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4393,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1))) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_764,c_771])).

cnf(c_7856,plain,
    ( sK2 != k1_xboole_0
    | sK4 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7851,c_14,c_4393])).

cnf(c_7857,plain,
    ( sK2 != k1_xboole_0
    | sK4 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_7856])).

cnf(c_7934,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7857,c_7832])).

cnf(c_7940,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7934,c_1208])).

cnf(c_7937,plain,
    ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7934,c_1246])).

cnf(c_7941,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7940,c_6556,c_6574,c_7937])).

cnf(c_7943,plain,
    ( k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7688,c_7941])).

cnf(c_7945,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7943,c_3,c_14])).

cnf(c_7946,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7945])).

cnf(c_9289,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7946,c_7941])).

cnf(c_9292,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9289,c_14,c_4393])).

cnf(c_9293,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9292])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.16/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.16/1.49  
% 7.16/1.49  ------  iProver source info
% 7.16/1.49  
% 7.16/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.16/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.16/1.49  git: non_committed_changes: false
% 7.16/1.49  git: last_make_outside_of_git: false
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    ""
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         true
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     num_symb
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       true
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     true
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.16/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_input_bw                          []
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  ------ Parsing...
% 7.16/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.16/1.49  ------ Proving...
% 7.16/1.49  ------ Problem Properties 
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  clauses                                 25
% 7.16/1.49  conjectures                             5
% 7.16/1.49  EPR                                     4
% 7.16/1.49  Horn                                    20
% 7.16/1.49  unary                                   11
% 7.16/1.49  binary                                  10
% 7.16/1.49  lits                                    47
% 7.16/1.49  lits eq                                 24
% 7.16/1.49  fd_pure                                 0
% 7.16/1.49  fd_pseudo                               0
% 7.16/1.49  fd_cond                                 1
% 7.16/1.49  fd_pseudo_cond                          1
% 7.16/1.49  AC symbols                              0
% 7.16/1.49  
% 7.16/1.49  ------ Schedule dynamic 5 is on 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  Current options:
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    ""
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         true
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     none
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       false
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     true
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.16/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_input_bw                          []
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ Proving...
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  % SZS status Theorem for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49   Resolution empty clause
% 7.16/1.49  
% 7.16/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  fof(f11,axiom,(
% 7.16/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f58,plain,(
% 7.16/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f11])).
% 7.16/1.49  
% 7.16/1.49  fof(f10,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f57,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f10])).
% 7.16/1.49  
% 7.16/1.49  fof(f20,conjecture,(
% 7.16/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f21,negated_conjecture,(
% 7.16/1.49    ~! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.16/1.49    inference(negated_conjecture,[],[f20])).
% 7.16/1.49  
% 7.16/1.49  fof(f30,plain,(
% 7.16/1.49    ? [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.16/1.49    inference(ennf_transformation,[],[f21])).
% 7.16/1.49  
% 7.16/1.49  fof(f39,plain,(
% 7.16/1.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 7.16/1.49    inference(nnf_transformation,[],[f30])).
% 7.16/1.49  
% 7.16/1.49  fof(f40,plain,(
% 7.16/1.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 7.16/1.49    inference(flattening,[],[f39])).
% 7.16/1.49  
% 7.16/1.49  fof(f41,plain,(
% 7.16/1.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0)) => (((k2_tarski(sK3,sK4) != sK2 & k1_tarski(sK4) != sK2 & k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2) | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0) & (k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0))),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f42,plain,(
% 7.16/1.49    ((k2_tarski(sK3,sK4) != sK2 & k1_tarski(sK4) != sK2 & k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2) | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0) & (k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0)),
% 7.16/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f41])).
% 7.16/1.49  
% 7.16/1.49  fof(f71,plain,(
% 7.16/1.49    k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f13,axiom,(
% 7.16/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f60,plain,(
% 7.16/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f13])).
% 7.16/1.49  
% 7.16/1.49  fof(f82,plain,(
% 7.16/1.49    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 7.16/1.49    inference(definition_unfolding,[],[f60,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f5,axiom,(
% 7.16/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f51,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f5])).
% 7.16/1.49  
% 7.16/1.49  fof(f12,axiom,(
% 7.16/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f59,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f12])).
% 7.16/1.49  
% 7.16/1.49  fof(f19,axiom,(
% 7.16/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f70,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f19])).
% 7.16/1.49  
% 7.16/1.49  fof(f79,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f70,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f80,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f59,f79])).
% 7.16/1.49  
% 7.16/1.49  fof(f81,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f51,f80])).
% 7.16/1.49  
% 7.16/1.49  fof(f14,axiom,(
% 7.16/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f61,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f14])).
% 7.16/1.49  
% 7.16/1.49  fof(f15,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f62,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f15])).
% 7.16/1.49  
% 7.16/1.49  fof(f16,axiom,(
% 7.16/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f63,plain,(
% 7.16/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f16])).
% 7.16/1.49  
% 7.16/1.49  fof(f17,axiom,(
% 7.16/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f64,plain,(
% 7.16/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f17])).
% 7.16/1.49  
% 7.16/1.49  fof(f76,plain,(
% 7.16/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.16/1.49    inference(definition_unfolding,[],[f63,f64])).
% 7.16/1.49  
% 7.16/1.49  fof(f77,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.16/1.49    inference(definition_unfolding,[],[f62,f76])).
% 7.16/1.49  
% 7.16/1.49  fof(f78,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.16/1.49    inference(definition_unfolding,[],[f61,f77])).
% 7.16/1.49  
% 7.16/1.49  fof(f96,plain,(
% 7.16/1.49    k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2 | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2 | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2 | k1_xboole_0 = sK2 | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) = k1_xboole_0),
% 7.16/1.49    inference(definition_unfolding,[],[f71,f78,f82,f82,f81,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f3,axiom,(
% 7.16/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f23,plain,(
% 7.16/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.16/1.49    inference(rectify,[],[f3])).
% 7.16/1.49  
% 7.16/1.49  fof(f47,plain,(
% 7.16/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f23])).
% 7.16/1.49  
% 7.16/1.49  fof(f84,plain,(
% 7.16/1.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.16/1.49    inference(definition_unfolding,[],[f47,f80])).
% 7.16/1.49  
% 7.16/1.49  fof(f2,axiom,(
% 7.16/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f22,plain,(
% 7.16/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.16/1.49    inference(rectify,[],[f2])).
% 7.16/1.49  
% 7.16/1.49  fof(f46,plain,(
% 7.16/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f22])).
% 7.16/1.49  
% 7.16/1.49  fof(f83,plain,(
% 7.16/1.49    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.16/1.49    inference(definition_unfolding,[],[f46,f79])).
% 7.16/1.49  
% 7.16/1.49  fof(f7,axiom,(
% 7.16/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f53,plain,(
% 7.16/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f7])).
% 7.16/1.49  
% 7.16/1.49  fof(f18,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f29,plain,(
% 7.16/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.16/1.49    inference(ennf_transformation,[],[f18])).
% 7.16/1.49  
% 7.16/1.49  fof(f37,plain,(
% 7.16/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.16/1.49    inference(nnf_transformation,[],[f29])).
% 7.16/1.49  
% 7.16/1.49  fof(f38,plain,(
% 7.16/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.16/1.49    inference(flattening,[],[f37])).
% 7.16/1.49  
% 7.16/1.49  fof(f65,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f38])).
% 7.16/1.49  
% 7.16/1.49  fof(f91,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k4_enumset1(X1,X1,X1,X1,X1,X2) = X0 | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f65,f78,f82,f82,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f9,axiom,(
% 7.16/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f56,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f9])).
% 7.16/1.49  
% 7.16/1.49  fof(f86,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f56,f79])).
% 7.16/1.49  
% 7.16/1.49  fof(f68,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f38])).
% 7.16/1.49  
% 7.16/1.49  fof(f88,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0) )),
% 7.16/1.49    inference(definition_unfolding,[],[f68,f78,f82])).
% 7.16/1.49  
% 7.16/1.49  fof(f99,plain,(
% 7.16/1.49    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 7.16/1.49    inference(equality_resolution,[],[f88])).
% 7.16/1.49  
% 7.16/1.49  fof(f6,axiom,(
% 7.16/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f27,plain,(
% 7.16/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.16/1.49    inference(ennf_transformation,[],[f6])).
% 7.16/1.49  
% 7.16/1.49  fof(f52,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f27])).
% 7.16/1.49  
% 7.16/1.49  fof(f85,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.16/1.49    inference(definition_unfolding,[],[f52,f79])).
% 7.16/1.49  
% 7.16/1.49  fof(f74,plain,(
% 7.16/1.49    k1_tarski(sK4) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f93,plain,(
% 7.16/1.49    k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2 | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0),
% 7.16/1.49    inference(definition_unfolding,[],[f74,f82,f81,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f75,plain,(
% 7.16/1.49    k2_tarski(sK3,sK4) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f92,plain,(
% 7.16/1.49    k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2 | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0),
% 7.16/1.49    inference(definition_unfolding,[],[f75,f78,f81,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f67,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f38])).
% 7.16/1.49  
% 7.16/1.49  fof(f89,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0) )),
% 7.16/1.49    inference(definition_unfolding,[],[f67,f78,f82])).
% 7.16/1.49  
% 7.16/1.49  fof(f100,plain,(
% 7.16/1.49    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 7.16/1.49    inference(equality_resolution,[],[f89])).
% 7.16/1.49  
% 7.16/1.49  fof(f73,plain,(
% 7.16/1.49    k1_tarski(sK3) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f94,plain,(
% 7.16/1.49    k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2 | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0),
% 7.16/1.49    inference(definition_unfolding,[],[f73,f82,f81,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f72,plain,(
% 7.16/1.49    k1_xboole_0 != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 7.16/1.49    inference(cnf_transformation,[],[f42])).
% 7.16/1.49  
% 7.16/1.49  fof(f95,plain,(
% 7.16/1.49    k1_xboole_0 != sK2 | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0),
% 7.16/1.49    inference(definition_unfolding,[],[f72,f81,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f66,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f38])).
% 7.16/1.49  
% 7.16/1.49  fof(f90,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 7.16/1.49    inference(definition_unfolding,[],[f66,f78])).
% 7.16/1.49  
% 7.16/1.49  fof(f101,plain,(
% 7.16/1.49    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 7.16/1.49    inference(equality_resolution,[],[f90])).
% 7.16/1.49  
% 7.16/1.49  cnf(c_14,plain,
% 7.16/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_13,plain,
% 7.16/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_24,negated_conjecture,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 = sK2 ),
% 7.16/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1117,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) = k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_13,c_24]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1124,plain,
% 7.16/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4,plain,
% 7.16/1.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_3,plain,
% 7.16/1.49      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_778,plain,
% 7.16/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.16/1.49      inference(light_normalisation,[status(thm)],[c_4,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1130,plain,
% 7.16/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1124,c_778]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1247,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) = k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1117,c_1130]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1249,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0)
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1247,c_13]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1254,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0)) = X0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(light_normalisation,[status(thm)],[c_1249,c_778]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1288,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k1_xboole_0)
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_14,c_1254]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9,plain,
% 7.16/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1296,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1288,c_9]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1126,plain,
% 7.16/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1291,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),X0),X0)) = k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1254,c_1126]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1615,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),X0),X0)) = k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1296,c_1291]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_504,plain,( X0 = X0 ),theory(equality) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_894,plain,
% 7.16/1.49      ( sK2 = sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_504]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_505,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_823,plain,
% 7.16/1.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_505]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_847,plain,
% 7.16/1.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_823]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_995,plain,
% 7.16/1.49      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_847]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_19,plain,
% 7.16/1.49      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
% 7.16/1.49      | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0
% 7.16/1.49      | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0
% 7.16/1.49      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
% 7.16/1.49      | k1_xboole_0 = X0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_801,plain,
% 7.16/1.49      ( ~ r1_tarski(sK2,k4_enumset1(X0,X0,X0,X0,X0,X1))
% 7.16/1.49      | k4_enumset1(X0,X0,X0,X0,X0,X1) = sK2
% 7.16/1.49      | k4_enumset1(X1,X1,X1,X1,X1,X1) = sK2
% 7.16/1.49      | k4_enumset1(X0,X0,X0,X0,X0,X0) = sK2
% 7.16/1.49      | k1_xboole_0 = sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1261,plain,
% 7.16/1.49      ( ~ r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
% 7.16/1.49      | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k1_xboole_0 = sK2 ),
% 7.16/1.49      inference(instantiation,[status(thm)],[c_801]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_12,plain,
% 7.16/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 7.16/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_768,plain,
% 7.16/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1613,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1296,c_768]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1625,plain,
% 7.16/1.49      ( r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
% 7.16/1.49      | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1613]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1705,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_1615,c_894,c_995,c_1261,c_1625]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1706,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(renaming,[status(thm)],[c_1705]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_16,plain,
% 7.16/1.49      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_766,plain,
% 7.16/1.49      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2434,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | r1_tarski(sK2,k4_enumset1(X0,X0,X0,X0,X0,sK4)) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1706,c_766]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_8,plain,
% 7.16/1.49      ( ~ r1_tarski(X0,X1) | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 ),
% 7.16/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_771,plain,
% 7.16/1.49      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
% 7.16/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4403,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X0,X0,X0,X0,X0,sK4))) = k4_enumset1(X0,X0,X0,X0,X0,sK4)
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2434,c_771]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_21,negated_conjecture,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1119,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_13,c_21]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1222,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1119,c_1130]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6460,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_4403,c_1222]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6463,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_6460,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6464,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_6463]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6556,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6464,c_1706]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6564,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_6556,c_1222]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6571,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_6564,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6572,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_6571]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_20,negated_conjecture,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1120,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_13,c_20]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1246,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1120,c_1130]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6562,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_6556,c_1246]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6573,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_6562,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_6574,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_6573]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7688,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2 | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_6572,c_6556,c_6574]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1707,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) = sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1706,c_3]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2126,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1707,c_1222]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2133,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_2126,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2134,plain,
% 7.16/1.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_2133]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2124,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_1707,c_1246]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2135,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_2124,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2136,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) != sK2
% 7.16/1.49      | k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_2135]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2143,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) = sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_2134,c_1707,c_2136]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_17,plain,
% 7.16/1.49      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_765,plain,
% 7.16/1.49      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_2145,plain,
% 7.16/1.49      ( k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | r1_tarski(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)) = iProver_top ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2143,c_765]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4402,plain,
% 7.16/1.49      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0))) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_2145,c_771]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_22,negated_conjecture,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0 ),
% 7.16/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1118,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_13,c_22]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1221,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1118,c_1130]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5385,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_4402,c_1221]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5387,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_5385,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5388,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k3_tarski(sK2) = sK4
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_5387]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_5406,plain,
% 7.16/1.49      ( k3_tarski(sK2) = sK4 | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5388,c_2143]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7692,plain,
% 7.16/1.49      ( k3_tarski(sK2) = sK3 | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_7688,c_3]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7832,plain,
% 7.16/1.49      ( sK2 = k1_xboole_0 | sK4 = sK3 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_5406,c_7692]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_23,negated_conjecture,
% 7.16/1.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))))) != k1_xboole_0
% 7.16/1.49      | k1_xboole_0 != sK2 ),
% 7.16/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1121,plain,
% 7.16/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))))) != k1_xboole_0
% 7.16/1.49      | sK2 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_13,c_23]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_1208,plain,
% 7.16/1.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0
% 7.16/1.49      | sK2 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_1121,c_1130]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7851,plain,
% 7.16/1.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)))) != k1_xboole_0
% 7.16/1.49      | sK2 != k1_xboole_0
% 7.16/1.49      | sK4 = sK3 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_7832,c_1208]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_18,plain,
% 7.16/1.49      ( r1_tarski(k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 7.16/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_764,plain,
% 7.16/1.49      ( r1_tarski(k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.16/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_4393,plain,
% 7.16/1.49      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(X0,X0,X0,X0,X0,X1))) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_764,c_771]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7856,plain,
% 7.16/1.49      ( sK2 != k1_xboole_0 | sK4 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7851,c_14,c_4393]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7857,plain,
% 7.16/1.49      ( sK2 != k1_xboole_0 | sK4 = sK3 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_7856]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7934,plain,
% 7.16/1.49      ( sK4 = sK3 ),
% 7.16/1.49      inference(global_propositional_subsumption,[status(thm)],[c_7857,c_7832]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7940,plain,
% 7.16/1.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0
% 7.16/1.49      | sK2 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7934,c_1208]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7937,plain,
% 7.16/1.49      ( k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) != sK2
% 7.16/1.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7934,c_1246]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7941,plain,
% 7.16/1.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
% 7.16/1.49      inference(global_propositional_subsumption,
% 7.16/1.49                [status(thm)],
% 7.16/1.49                [c_7940,c_6556,c_6574,c_7937]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7943,plain,
% 7.16/1.49      ( k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 7.16/1.49      | sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(superposition,[status(thm)],[c_7688,c_7941]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7945,plain,
% 7.16/1.49      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7943,c_3,c_14]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_7946,plain,
% 7.16/1.49      ( sK2 = k1_xboole_0 ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_7945]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9289,plain,
% 7.16/1.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_7946,c_7941]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9292,plain,
% 7.16/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.16/1.49      inference(demodulation,[status(thm)],[c_9289,c_14,c_4393]) ).
% 7.16/1.49  
% 7.16/1.49  cnf(c_9293,plain,
% 7.16/1.49      ( $false ),
% 7.16/1.49      inference(equality_resolution_simp,[status(thm)],[c_9292]) ).
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  ------                               Statistics
% 7.16/1.49  
% 7.16/1.49  ------ General
% 7.16/1.49  
% 7.16/1.49  abstr_ref_over_cycles:                  0
% 7.16/1.49  abstr_ref_under_cycles:                 0
% 7.16/1.49  gc_basic_clause_elim:                   0
% 7.16/1.49  forced_gc_time:                         0
% 7.16/1.49  parsing_time:                           0.008
% 7.16/1.49  unif_index_cands_time:                  0.
% 7.16/1.49  unif_index_add_time:                    0.
% 7.16/1.49  orderings_time:                         0.
% 7.16/1.49  out_proof_time:                         0.014
% 7.16/1.49  total_time:                             0.577
% 7.16/1.49  num_of_symbols:                         43
% 7.16/1.49  num_of_terms:                           13774
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing
% 7.16/1.49  
% 7.16/1.49  num_of_splits:                          0
% 7.16/1.49  num_of_split_atoms:                     0
% 7.16/1.49  num_of_reused_defs:                     0
% 7.16/1.49  num_eq_ax_congr_red:                    10
% 7.16/1.49  num_of_sem_filtered_clauses:            1
% 7.16/1.49  num_of_subtypes:                        0
% 7.16/1.49  monotx_restored_types:                  0
% 7.16/1.49  sat_num_of_epr_types:                   0
% 7.16/1.49  sat_num_of_non_cyclic_types:            0
% 7.16/1.49  sat_guarded_non_collapsed_types:        0
% 7.16/1.49  num_pure_diseq_elim:                    0
% 7.16/1.49  simp_replaced_by:                       0
% 7.16/1.49  res_preprocessed:                       92
% 7.16/1.49  prep_upred:                             0
% 7.16/1.49  prep_unflattend:                        40
% 7.16/1.49  smt_new_axioms:                         0
% 7.16/1.49  pred_elim_cands:                        3
% 7.16/1.49  pred_elim:                              0
% 7.16/1.49  pred_elim_cl:                           0
% 7.16/1.49  pred_elim_cycles:                       2
% 7.16/1.49  merged_defs:                            0
% 7.16/1.49  merged_defs_ncl:                        0
% 7.16/1.49  bin_hyper_res:                          0
% 7.16/1.49  prep_cycles:                            3
% 7.16/1.49  pred_elim_time:                         0.008
% 7.16/1.49  splitting_time:                         0.
% 7.16/1.49  sem_filter_time:                        0.
% 7.16/1.49  monotx_time:                            0.
% 7.16/1.49  subtype_inf_time:                       0.
% 7.16/1.49  
% 7.16/1.49  ------ Problem properties
% 7.16/1.49  
% 7.16/1.49  clauses:                                25
% 7.16/1.49  conjectures:                            5
% 7.16/1.49  epr:                                    4
% 7.16/1.49  horn:                                   20
% 7.16/1.49  ground:                                 6
% 7.16/1.49  unary:                                  11
% 7.16/1.49  binary:                                 10
% 7.16/1.49  lits:                                   47
% 7.16/1.49  lits_eq:                                24
% 7.16/1.49  fd_pure:                                0
% 7.16/1.49  fd_pseudo:                              0
% 7.16/1.49  fd_cond:                                1
% 7.16/1.49  fd_pseudo_cond:                         1
% 7.16/1.49  ac_symbols:                             1
% 7.16/1.49  
% 7.16/1.49  ------ Propositional Solver
% 7.16/1.49  
% 7.16/1.49  prop_solver_calls:                      28
% 7.16/1.49  prop_fast_solver_calls:                 844
% 7.16/1.49  smt_solver_calls:                       0
% 7.16/1.49  smt_fast_solver_calls:                  0
% 7.16/1.49  prop_num_of_clauses:                    3105
% 7.16/1.49  prop_preprocess_simplified:             6106
% 7.16/1.49  prop_fo_subsumed:                       30
% 7.16/1.49  prop_solver_time:                       0.
% 7.16/1.49  smt_solver_time:                        0.
% 7.16/1.49  smt_fast_solver_time:                   0.
% 7.16/1.49  prop_fast_solver_time:                  0.
% 7.16/1.49  prop_unsat_core_time:                   0.
% 7.16/1.49  
% 7.16/1.49  ------ QBF
% 7.16/1.49  
% 7.16/1.49  qbf_q_res:                              0
% 7.16/1.49  qbf_num_tautologies:                    0
% 7.16/1.49  qbf_prep_cycles:                        0
% 7.16/1.49  
% 7.16/1.49  ------ BMC1
% 7.16/1.49  
% 7.16/1.49  bmc1_current_bound:                     -1
% 7.16/1.49  bmc1_last_solved_bound:                 -1
% 7.16/1.49  bmc1_unsat_core_size:                   -1
% 7.16/1.49  bmc1_unsat_core_parents_size:           -1
% 7.16/1.49  bmc1_merge_next_fun:                    0
% 7.16/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation
% 7.16/1.49  
% 7.16/1.49  inst_num_of_clauses:                    923
% 7.16/1.49  inst_num_in_passive:                    137
% 7.16/1.49  inst_num_in_active:                     360
% 7.16/1.49  inst_num_in_unprocessed:                426
% 7.16/1.49  inst_num_of_loops:                      460
% 7.16/1.49  inst_num_of_learning_restarts:          0
% 7.16/1.49  inst_num_moves_active_passive:          96
% 7.16/1.49  inst_lit_activity:                      0
% 7.16/1.49  inst_lit_activity_moves:                0
% 7.16/1.49  inst_num_tautologies:                   0
% 7.16/1.49  inst_num_prop_implied:                  0
% 7.16/1.49  inst_num_existing_simplified:           0
% 7.16/1.49  inst_num_eq_res_simplified:             0
% 7.16/1.49  inst_num_child_elim:                    0
% 7.16/1.49  inst_num_of_dismatching_blockings:      353
% 7.16/1.49  inst_num_of_non_proper_insts:           995
% 7.16/1.49  inst_num_of_duplicates:                 0
% 7.16/1.49  inst_inst_num_from_inst_to_res:         0
% 7.16/1.49  inst_dismatching_checking_time:         0.
% 7.16/1.49  
% 7.16/1.49  ------ Resolution
% 7.16/1.49  
% 7.16/1.49  res_num_of_clauses:                     0
% 7.16/1.49  res_num_in_passive:                     0
% 7.16/1.49  res_num_in_active:                      0
% 7.16/1.49  res_num_of_loops:                       95
% 7.16/1.49  res_forward_subset_subsumed:            129
% 7.16/1.49  res_backward_subset_subsumed:           0
% 7.16/1.49  res_forward_subsumed:                   1
% 7.16/1.49  res_backward_subsumed:                  0
% 7.16/1.49  res_forward_subsumption_resolution:     0
% 7.16/1.49  res_backward_subsumption_resolution:    0
% 7.16/1.49  res_clause_to_clause_subsumption:       7841
% 7.16/1.49  res_orphan_elimination:                 0
% 7.16/1.49  res_tautology_del:                      126
% 7.16/1.49  res_num_eq_res_simplified:              0
% 7.16/1.49  res_num_sel_changes:                    0
% 7.16/1.49  res_moves_from_active_to_pass:          0
% 7.16/1.49  
% 7.16/1.49  ------ Superposition
% 7.16/1.49  
% 7.16/1.49  sup_time_total:                         0.
% 7.16/1.49  sup_time_generating:                    0.
% 7.16/1.49  sup_time_sim_full:                      0.
% 7.16/1.49  sup_time_sim_immed:                     0.
% 7.16/1.49  
% 7.16/1.49  sup_num_of_clauses:                     384
% 7.16/1.49  sup_num_in_active:                      34
% 7.16/1.49  sup_num_in_passive:                     350
% 7.16/1.49  sup_num_of_loops:                       90
% 7.16/1.49  sup_fw_superposition:                   1139
% 7.16/1.49  sup_bw_superposition:                   1104
% 7.16/1.49  sup_immediate_simplified:               1076
% 7.16/1.49  sup_given_eliminated:                   1
% 7.16/1.49  comparisons_done:                       0
% 7.16/1.49  comparisons_avoided:                    108
% 7.16/1.49  
% 7.16/1.49  ------ Simplifications
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  sim_fw_subset_subsumed:                 11
% 7.16/1.49  sim_bw_subset_subsumed:                 23
% 7.16/1.49  sim_fw_subsumed:                        62
% 7.16/1.49  sim_bw_subsumed:                        21
% 7.16/1.49  sim_fw_subsumption_res:                 0
% 7.16/1.49  sim_bw_subsumption_res:                 0
% 7.16/1.49  sim_tautology_del:                      20
% 7.16/1.49  sim_eq_tautology_del:                   112
% 7.16/1.49  sim_eq_res_simp:                        13
% 7.16/1.49  sim_fw_demodulated:                     913
% 7.16/1.49  sim_bw_demodulated:                     79
% 7.16/1.49  sim_light_normalised:                   430
% 7.16/1.49  sim_joinable_taut:                      12
% 7.16/1.49  sim_joinable_simp:                      0
% 7.16/1.49  sim_ac_normalised:                      0
% 7.16/1.49  sim_smt_subsumption:                    0
% 7.16/1.49  
%------------------------------------------------------------------------------
