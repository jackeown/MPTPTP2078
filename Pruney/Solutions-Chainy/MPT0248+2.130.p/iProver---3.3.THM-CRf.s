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
% DateTime   : Thu Dec  3 11:32:29 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  176 (94426 expanded)
%              Number of clauses        :   96 (11313 expanded)
%              Number of leaves         :   23 (28979 expanded)
%              Depth                    :   41
%              Number of atoms          :  339 (114274 expanded)
%              Number of equality atoms :  248 (110455 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK3
        | k1_tarski(sK1) != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_xboole_0 != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_tarski(sK1) != sK2 )
      & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_xboole_0 != sK3
      | k1_tarski(sK1) != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_xboole_0 != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_tarski(sK1) != sK2 )
    & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f37])).

fof(f66,plain,(
    k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f89,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f66,f75,f78])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f62,f78,f78])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f43,f76])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f75])).

fof(f67,plain,
    ( k1_tarski(sK1) != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f67,f78,f78])).

fof(f68,plain,
    ( k1_tarski(sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f69,plain,
    ( k1_xboole_0 != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( k1_xboole_0 != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_373,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6445,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_373])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_372,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4556,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_372])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_369,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5758,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4556,c_369])).

cnf(c_5761,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5758,c_369])).

cnf(c_7719,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6445,c_5761])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_585,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_382,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_3,c_13])).

cnf(c_588,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_585,c_382])).

cnf(c_7905,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7719,c_588])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5764,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5758,c_19])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_404,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_406,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_4560,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4556])).

cnf(c_5959,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5764,c_19,c_18,c_406,c_4560])).

cnf(c_7935,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7719,c_6445])).

cnf(c_17,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5766,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5758,c_17])).

cnf(c_594,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_12,c_588])).

cnf(c_757,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_588,c_594])).

cnf(c_1244,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_13,c_757])).

cnf(c_1466,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1244,c_588])).

cnf(c_1949,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_1466])).

cnf(c_7932,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK3),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7719,c_1949])).

cnf(c_754,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_13,c_594])).

cnf(c_593,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_588])).

cnf(c_770,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_754,c_593])).

cnf(c_587,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_664,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_587,c_588])).

cnf(c_672,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_664,c_593])).

cnf(c_808,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_672,c_588])).

cnf(c_804,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_594,c_672])).

cnf(c_2346,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_808,c_804])).

cnf(c_7954,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7932,c_770,c_2346])).

cnf(c_8051,plain,
    ( sK2 = k1_xboole_0
    | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7935,c_5766,c_7954])).

cnf(c_8052,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8051])).

cnf(c_906,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_808,c_594])).

cnf(c_8119,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK3),sK2),k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8052,c_906])).

cnf(c_8123,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8119,c_588,c_1244])).

cnf(c_9431,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7905,c_19,c_18,c_406,c_4560,c_8123])).

cnf(c_7574,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_6445])).

cnf(c_800,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_12,c_672])).

cnf(c_746,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_588,c_594])).

cnf(c_1650,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_800,c_746])).

cnf(c_7578,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7574,c_1650])).

cnf(c_7662,plain,
    ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_7578])).

cnf(c_9434,plain,
    ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9431,c_7662])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_374,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15663,plain,
    ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9434,c_374])).

cnf(c_6444,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_373])).

cnf(c_6449,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6444,c_13,c_382])).

cnf(c_19439,plain,
    ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15663,c_6449])).

cnf(c_19447,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19439,c_369])).

cnf(c_24535,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k3_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = X0 ),
    inference(superposition,[status(thm)],[c_19447,c_3])).

cnf(c_26188,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k3_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24535,c_13])).

cnf(c_27660,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19447,c_26188])).

cnf(c_27661,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_27660,c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_379,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15697,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9434,c_379])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_376,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17561,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_376])).

cnf(c_19446,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19439,c_379])).

cnf(c_22484,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15697,c_17561,c_19446])).

cnf(c_29579,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27661,c_22484])).

cnf(c_744,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = X3 ),
    inference(superposition,[status(thm)],[c_12,c_594])).

cnf(c_29574,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_27661,c_744])).

cnf(c_29587,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X1,X0)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = X2 ),
    inference(light_normalisation,[status(thm)],[c_29574,c_1244])).

cnf(c_811,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_672,c_594])).

cnf(c_597,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_588,c_12])).

cnf(c_599,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_597,c_12])).

cnf(c_1000,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
    inference(superposition,[status(thm)],[c_811,c_599])).

cnf(c_29588,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_29587,c_1000])).

cnf(c_29894,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29579,c_19,c_18,c_406,c_4560,c_29588])).

cnf(c_30051,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_29894,c_29894])).

cnf(c_29901,plain,
    ( k3_tarski(k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_29894,c_3])).

cnf(c_29975,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29894,c_5959])).

cnf(c_30032,plain,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29901,c_29975])).

cnf(c_30167,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_30051,c_30032])).

cnf(c_30170,plain,
    ( k1_xboole_0 != sK1 ),
    inference(grounding,[status(thm)],[c_30167:[bind(X0,$fot(sK1))]])).

cnf(c_30171,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | k1_xboole_0 = sK1 ),
    inference(grounding,[status(thm)],[c_29588:[bind(X0,$fot(sK1))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30170,c_30171,c_5959])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.92/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/1.48  
% 7.92/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.48  
% 7.92/1.48  ------  iProver source info
% 7.92/1.48  
% 7.92/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.48  git: non_committed_changes: false
% 7.92/1.48  git: last_make_outside_of_git: false
% 7.92/1.48  
% 7.92/1.48  ------ 
% 7.92/1.48  
% 7.92/1.48  ------ Input Options
% 7.92/1.48  
% 7.92/1.48  --out_options                           all
% 7.92/1.48  --tptp_safe_out                         true
% 7.92/1.48  --problem_path                          ""
% 7.92/1.48  --include_path                          ""
% 7.92/1.48  --clausifier                            res/vclausify_rel
% 7.92/1.48  --clausifier_options                    ""
% 7.92/1.48  --stdin                                 false
% 7.92/1.48  --stats_out                             all
% 7.92/1.48  
% 7.92/1.48  ------ General Options
% 7.92/1.48  
% 7.92/1.48  --fof                                   false
% 7.92/1.48  --time_out_real                         305.
% 7.92/1.48  --time_out_virtual                      -1.
% 7.92/1.48  --symbol_type_check                     false
% 7.92/1.48  --clausify_out                          false
% 7.92/1.48  --sig_cnt_out                           false
% 7.92/1.48  --trig_cnt_out                          false
% 7.92/1.48  --trig_cnt_out_tolerance                1.
% 7.92/1.48  --trig_cnt_out_sk_spl                   false
% 7.92/1.48  --abstr_cl_out                          false
% 7.92/1.48  
% 7.92/1.48  ------ Global Options
% 7.92/1.48  
% 7.92/1.48  --schedule                              default
% 7.92/1.48  --add_important_lit                     false
% 7.92/1.48  --prop_solver_per_cl                    1000
% 7.92/1.48  --min_unsat_core                        false
% 7.92/1.48  --soft_assumptions                      false
% 7.92/1.48  --soft_lemma_size                       3
% 7.92/1.48  --prop_impl_unit_size                   0
% 7.92/1.48  --prop_impl_unit                        []
% 7.92/1.48  --share_sel_clauses                     true
% 7.92/1.48  --reset_solvers                         false
% 7.92/1.48  --bc_imp_inh                            [conj_cone]
% 7.92/1.48  --conj_cone_tolerance                   3.
% 7.92/1.48  --extra_neg_conj                        none
% 7.92/1.48  --large_theory_mode                     true
% 7.92/1.48  --prolific_symb_bound                   200
% 7.92/1.48  --lt_threshold                          2000
% 7.92/1.48  --clause_weak_htbl                      true
% 7.92/1.48  --gc_record_bc_elim                     false
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing Options
% 7.92/1.48  
% 7.92/1.48  --preprocessing_flag                    true
% 7.92/1.48  --time_out_prep_mult                    0.1
% 7.92/1.48  --splitting_mode                        input
% 7.92/1.48  --splitting_grd                         true
% 7.92/1.48  --splitting_cvd                         false
% 7.92/1.48  --splitting_cvd_svl                     false
% 7.92/1.48  --splitting_nvd                         32
% 7.92/1.48  --sub_typing                            true
% 7.92/1.48  --prep_gs_sim                           true
% 7.92/1.48  --prep_unflatten                        true
% 7.92/1.48  --prep_res_sim                          true
% 7.92/1.48  --prep_upred                            true
% 7.92/1.48  --prep_sem_filter                       exhaustive
% 7.92/1.48  --prep_sem_filter_out                   false
% 7.92/1.48  --pred_elim                             true
% 7.92/1.48  --res_sim_input                         true
% 7.92/1.48  --eq_ax_congr_red                       true
% 7.92/1.48  --pure_diseq_elim                       true
% 7.92/1.48  --brand_transform                       false
% 7.92/1.48  --non_eq_to_eq                          false
% 7.92/1.48  --prep_def_merge                        true
% 7.92/1.48  --prep_def_merge_prop_impl              false
% 7.92/1.48  --prep_def_merge_mbd                    true
% 7.92/1.48  --prep_def_merge_tr_red                 false
% 7.92/1.48  --prep_def_merge_tr_cl                  false
% 7.92/1.48  --smt_preprocessing                     true
% 7.92/1.48  --smt_ac_axioms                         fast
% 7.92/1.48  --preprocessed_out                      false
% 7.92/1.48  --preprocessed_stats                    false
% 7.92/1.48  
% 7.92/1.48  ------ Abstraction refinement Options
% 7.92/1.48  
% 7.92/1.48  --abstr_ref                             []
% 7.92/1.48  --abstr_ref_prep                        false
% 7.92/1.48  --abstr_ref_until_sat                   false
% 7.92/1.48  --abstr_ref_sig_restrict                funpre
% 7.92/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.48  --abstr_ref_under                       []
% 7.92/1.48  
% 7.92/1.48  ------ SAT Options
% 7.92/1.48  
% 7.92/1.48  --sat_mode                              false
% 7.92/1.48  --sat_fm_restart_options                ""
% 7.92/1.48  --sat_gr_def                            false
% 7.92/1.48  --sat_epr_types                         true
% 7.92/1.48  --sat_non_cyclic_types                  false
% 7.92/1.48  --sat_finite_models                     false
% 7.92/1.48  --sat_fm_lemmas                         false
% 7.92/1.48  --sat_fm_prep                           false
% 7.92/1.48  --sat_fm_uc_incr                        true
% 7.92/1.48  --sat_out_model                         small
% 7.92/1.48  --sat_out_clauses                       false
% 7.92/1.48  
% 7.92/1.48  ------ QBF Options
% 7.92/1.48  
% 7.92/1.48  --qbf_mode                              false
% 7.92/1.48  --qbf_elim_univ                         false
% 7.92/1.48  --qbf_dom_inst                          none
% 7.92/1.48  --qbf_dom_pre_inst                      false
% 7.92/1.48  --qbf_sk_in                             false
% 7.92/1.48  --qbf_pred_elim                         true
% 7.92/1.48  --qbf_split                             512
% 7.92/1.48  
% 7.92/1.48  ------ BMC1 Options
% 7.92/1.48  
% 7.92/1.48  --bmc1_incremental                      false
% 7.92/1.48  --bmc1_axioms                           reachable_all
% 7.92/1.48  --bmc1_min_bound                        0
% 7.92/1.48  --bmc1_max_bound                        -1
% 7.92/1.48  --bmc1_max_bound_default                -1
% 7.92/1.48  --bmc1_symbol_reachability              true
% 7.92/1.48  --bmc1_property_lemmas                  false
% 7.92/1.48  --bmc1_k_induction                      false
% 7.92/1.48  --bmc1_non_equiv_states                 false
% 7.92/1.48  --bmc1_deadlock                         false
% 7.92/1.48  --bmc1_ucm                              false
% 7.92/1.48  --bmc1_add_unsat_core                   none
% 7.92/1.48  --bmc1_unsat_core_children              false
% 7.92/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.48  --bmc1_out_stat                         full
% 7.92/1.48  --bmc1_ground_init                      false
% 7.92/1.48  --bmc1_pre_inst_next_state              false
% 7.92/1.48  --bmc1_pre_inst_state                   false
% 7.92/1.48  --bmc1_pre_inst_reach_state             false
% 7.92/1.48  --bmc1_out_unsat_core                   false
% 7.92/1.48  --bmc1_aig_witness_out                  false
% 7.92/1.48  --bmc1_verbose                          false
% 7.92/1.48  --bmc1_dump_clauses_tptp                false
% 7.92/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.48  --bmc1_dump_file                        -
% 7.92/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.48  --bmc1_ucm_extend_mode                  1
% 7.92/1.48  --bmc1_ucm_init_mode                    2
% 7.92/1.48  --bmc1_ucm_cone_mode                    none
% 7.92/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.48  --bmc1_ucm_relax_model                  4
% 7.92/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.48  --bmc1_ucm_layered_model                none
% 7.92/1.48  --bmc1_ucm_max_lemma_size               10
% 7.92/1.48  
% 7.92/1.48  ------ AIG Options
% 7.92/1.48  
% 7.92/1.48  --aig_mode                              false
% 7.92/1.48  
% 7.92/1.48  ------ Instantiation Options
% 7.92/1.48  
% 7.92/1.48  --instantiation_flag                    true
% 7.92/1.48  --inst_sos_flag                         true
% 7.92/1.48  --inst_sos_phase                        true
% 7.92/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.48  --inst_lit_sel_side                     num_symb
% 7.92/1.48  --inst_solver_per_active                1400
% 7.92/1.48  --inst_solver_calls_frac                1.
% 7.92/1.48  --inst_passive_queue_type               priority_queues
% 7.92/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.92/1.48  --inst_passive_queues_freq              [25;2]
% 7.92/1.48  --inst_dismatching                      true
% 7.92/1.48  --inst_eager_unprocessed_to_passive     true
% 7.92/1.48  --inst_prop_sim_given                   true
% 7.92/1.48  --inst_prop_sim_new                     false
% 7.92/1.48  --inst_subs_new                         false
% 7.92/1.48  --inst_eq_res_simp                      false
% 7.92/1.48  --inst_subs_given                       false
% 7.92/1.48  --inst_orphan_elimination               true
% 7.92/1.48  --inst_learning_loop_flag               true
% 7.92/1.48  --inst_learning_start                   3000
% 7.92/1.48  --inst_learning_factor                  2
% 7.92/1.48  --inst_start_prop_sim_after_learn       3
% 7.92/1.48  --inst_sel_renew                        solver
% 7.92/1.48  --inst_lit_activity_flag                true
% 7.92/1.48  --inst_restr_to_given                   false
% 7.92/1.48  --inst_activity_threshold               500
% 7.92/1.48  --inst_out_proof                        true
% 7.92/1.48  
% 7.92/1.48  ------ Resolution Options
% 7.92/1.48  
% 7.92/1.48  --resolution_flag                       true
% 7.92/1.48  --res_lit_sel                           adaptive
% 7.92/1.48  --res_lit_sel_side                      none
% 7.92/1.48  --res_ordering                          kbo
% 7.92/1.48  --res_to_prop_solver                    active
% 7.92/1.48  --res_prop_simpl_new                    false
% 7.92/1.48  --res_prop_simpl_given                  true
% 7.92/1.48  --res_passive_queue_type                priority_queues
% 7.92/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.92/1.48  --res_passive_queues_freq               [15;5]
% 7.92/1.48  --res_forward_subs                      full
% 7.92/1.48  --res_backward_subs                     full
% 7.92/1.48  --res_forward_subs_resolution           true
% 7.92/1.48  --res_backward_subs_resolution          true
% 7.92/1.48  --res_orphan_elimination                true
% 7.92/1.48  --res_time_limit                        2.
% 7.92/1.48  --res_out_proof                         true
% 7.92/1.48  
% 7.92/1.48  ------ Superposition Options
% 7.92/1.48  
% 7.92/1.48  --superposition_flag                    true
% 7.92/1.48  --sup_passive_queue_type                priority_queues
% 7.92/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.48  --demod_completeness_check              fast
% 7.92/1.48  --demod_use_ground                      true
% 7.92/1.48  --sup_to_prop_solver                    passive
% 7.92/1.48  --sup_prop_simpl_new                    true
% 7.92/1.48  --sup_prop_simpl_given                  true
% 7.92/1.48  --sup_fun_splitting                     true
% 7.92/1.48  --sup_smt_interval                      50000
% 7.92/1.48  
% 7.92/1.48  ------ Superposition Simplification Setup
% 7.92/1.48  
% 7.92/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.48  --sup_immed_triv                        [TrivRules]
% 7.92/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_immed_bw_main                     []
% 7.92/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_input_bw                          []
% 7.92/1.48  
% 7.92/1.48  ------ Combination Options
% 7.92/1.48  
% 7.92/1.48  --comb_res_mult                         3
% 7.92/1.48  --comb_sup_mult                         2
% 7.92/1.48  --comb_inst_mult                        10
% 7.92/1.48  
% 7.92/1.48  ------ Debug Options
% 7.92/1.48  
% 7.92/1.48  --dbg_backtrace                         false
% 7.92/1.48  --dbg_dump_prop_clauses                 false
% 7.92/1.48  --dbg_dump_prop_clauses_file            -
% 7.92/1.48  --dbg_out_stat                          false
% 7.92/1.48  ------ Parsing...
% 7.92/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.92/1.48  ------ Proving...
% 7.92/1.48  ------ Problem Properties 
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  clauses                                 21
% 7.92/1.48  conjectures                             4
% 7.92/1.48  EPR                                     2
% 7.92/1.48  Horn                                    16
% 7.92/1.48  unary                                   9
% 7.92/1.48  binary                                  5
% 7.92/1.48  lits                                    40
% 7.92/1.48  lits eq                                 13
% 7.92/1.48  fd_pure                                 0
% 7.92/1.48  fd_pseudo                               0
% 7.92/1.48  fd_cond                                 0
% 7.92/1.48  fd_pseudo_cond                          1
% 7.92/1.48  AC symbols                              0
% 7.92/1.48  
% 7.92/1.48  ------ Schedule dynamic 5 is on 
% 7.92/1.48  
% 7.92/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  ------ 
% 7.92/1.48  Current options:
% 7.92/1.48  ------ 
% 7.92/1.48  
% 7.92/1.48  ------ Input Options
% 7.92/1.48  
% 7.92/1.48  --out_options                           all
% 7.92/1.48  --tptp_safe_out                         true
% 7.92/1.48  --problem_path                          ""
% 7.92/1.48  --include_path                          ""
% 7.92/1.48  --clausifier                            res/vclausify_rel
% 7.92/1.48  --clausifier_options                    ""
% 7.92/1.48  --stdin                                 false
% 7.92/1.48  --stats_out                             all
% 7.92/1.48  
% 7.92/1.48  ------ General Options
% 7.92/1.48  
% 7.92/1.48  --fof                                   false
% 7.92/1.48  --time_out_real                         305.
% 7.92/1.48  --time_out_virtual                      -1.
% 7.92/1.48  --symbol_type_check                     false
% 7.92/1.48  --clausify_out                          false
% 7.92/1.48  --sig_cnt_out                           false
% 7.92/1.48  --trig_cnt_out                          false
% 7.92/1.48  --trig_cnt_out_tolerance                1.
% 7.92/1.48  --trig_cnt_out_sk_spl                   false
% 7.92/1.48  --abstr_cl_out                          false
% 7.92/1.48  
% 7.92/1.48  ------ Global Options
% 7.92/1.48  
% 7.92/1.48  --schedule                              default
% 7.92/1.48  --add_important_lit                     false
% 7.92/1.48  --prop_solver_per_cl                    1000
% 7.92/1.48  --min_unsat_core                        false
% 7.92/1.48  --soft_assumptions                      false
% 7.92/1.48  --soft_lemma_size                       3
% 7.92/1.48  --prop_impl_unit_size                   0
% 7.92/1.48  --prop_impl_unit                        []
% 7.92/1.48  --share_sel_clauses                     true
% 7.92/1.48  --reset_solvers                         false
% 7.92/1.48  --bc_imp_inh                            [conj_cone]
% 7.92/1.48  --conj_cone_tolerance                   3.
% 7.92/1.48  --extra_neg_conj                        none
% 7.92/1.48  --large_theory_mode                     true
% 7.92/1.48  --prolific_symb_bound                   200
% 7.92/1.48  --lt_threshold                          2000
% 7.92/1.48  --clause_weak_htbl                      true
% 7.92/1.48  --gc_record_bc_elim                     false
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing Options
% 7.92/1.48  
% 7.92/1.48  --preprocessing_flag                    true
% 7.92/1.48  --time_out_prep_mult                    0.1
% 7.92/1.48  --splitting_mode                        input
% 7.92/1.48  --splitting_grd                         true
% 7.92/1.48  --splitting_cvd                         false
% 7.92/1.48  --splitting_cvd_svl                     false
% 7.92/1.48  --splitting_nvd                         32
% 7.92/1.48  --sub_typing                            true
% 7.92/1.48  --prep_gs_sim                           true
% 7.92/1.48  --prep_unflatten                        true
% 7.92/1.48  --prep_res_sim                          true
% 7.92/1.48  --prep_upred                            true
% 7.92/1.48  --prep_sem_filter                       exhaustive
% 7.92/1.48  --prep_sem_filter_out                   false
% 7.92/1.48  --pred_elim                             true
% 7.92/1.48  --res_sim_input                         true
% 7.92/1.48  --eq_ax_congr_red                       true
% 7.92/1.48  --pure_diseq_elim                       true
% 7.92/1.48  --brand_transform                       false
% 7.92/1.48  --non_eq_to_eq                          false
% 7.92/1.48  --prep_def_merge                        true
% 7.92/1.48  --prep_def_merge_prop_impl              false
% 7.92/1.48  --prep_def_merge_mbd                    true
% 7.92/1.48  --prep_def_merge_tr_red                 false
% 7.92/1.48  --prep_def_merge_tr_cl                  false
% 7.92/1.48  --smt_preprocessing                     true
% 7.92/1.48  --smt_ac_axioms                         fast
% 7.92/1.48  --preprocessed_out                      false
% 7.92/1.48  --preprocessed_stats                    false
% 7.92/1.48  
% 7.92/1.48  ------ Abstraction refinement Options
% 7.92/1.48  
% 7.92/1.48  --abstr_ref                             []
% 7.92/1.48  --abstr_ref_prep                        false
% 7.92/1.48  --abstr_ref_until_sat                   false
% 7.92/1.48  --abstr_ref_sig_restrict                funpre
% 7.92/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.48  --abstr_ref_under                       []
% 7.92/1.48  
% 7.92/1.48  ------ SAT Options
% 7.92/1.48  
% 7.92/1.48  --sat_mode                              false
% 7.92/1.48  --sat_fm_restart_options                ""
% 7.92/1.48  --sat_gr_def                            false
% 7.92/1.48  --sat_epr_types                         true
% 7.92/1.48  --sat_non_cyclic_types                  false
% 7.92/1.48  --sat_finite_models                     false
% 7.92/1.48  --sat_fm_lemmas                         false
% 7.92/1.48  --sat_fm_prep                           false
% 7.92/1.48  --sat_fm_uc_incr                        true
% 7.92/1.48  --sat_out_model                         small
% 7.92/1.48  --sat_out_clauses                       false
% 7.92/1.48  
% 7.92/1.48  ------ QBF Options
% 7.92/1.48  
% 7.92/1.48  --qbf_mode                              false
% 7.92/1.48  --qbf_elim_univ                         false
% 7.92/1.48  --qbf_dom_inst                          none
% 7.92/1.48  --qbf_dom_pre_inst                      false
% 7.92/1.48  --qbf_sk_in                             false
% 7.92/1.48  --qbf_pred_elim                         true
% 7.92/1.48  --qbf_split                             512
% 7.92/1.48  
% 7.92/1.48  ------ BMC1 Options
% 7.92/1.48  
% 7.92/1.48  --bmc1_incremental                      false
% 7.92/1.48  --bmc1_axioms                           reachable_all
% 7.92/1.48  --bmc1_min_bound                        0
% 7.92/1.48  --bmc1_max_bound                        -1
% 7.92/1.48  --bmc1_max_bound_default                -1
% 7.92/1.48  --bmc1_symbol_reachability              true
% 7.92/1.48  --bmc1_property_lemmas                  false
% 7.92/1.48  --bmc1_k_induction                      false
% 7.92/1.48  --bmc1_non_equiv_states                 false
% 7.92/1.48  --bmc1_deadlock                         false
% 7.92/1.48  --bmc1_ucm                              false
% 7.92/1.48  --bmc1_add_unsat_core                   none
% 7.92/1.48  --bmc1_unsat_core_children              false
% 7.92/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.48  --bmc1_out_stat                         full
% 7.92/1.48  --bmc1_ground_init                      false
% 7.92/1.48  --bmc1_pre_inst_next_state              false
% 7.92/1.48  --bmc1_pre_inst_state                   false
% 7.92/1.48  --bmc1_pre_inst_reach_state             false
% 7.92/1.48  --bmc1_out_unsat_core                   false
% 7.92/1.48  --bmc1_aig_witness_out                  false
% 7.92/1.48  --bmc1_verbose                          false
% 7.92/1.48  --bmc1_dump_clauses_tptp                false
% 7.92/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.48  --bmc1_dump_file                        -
% 7.92/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.48  --bmc1_ucm_extend_mode                  1
% 7.92/1.48  --bmc1_ucm_init_mode                    2
% 7.92/1.48  --bmc1_ucm_cone_mode                    none
% 7.92/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.48  --bmc1_ucm_relax_model                  4
% 7.92/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.48  --bmc1_ucm_layered_model                none
% 7.92/1.48  --bmc1_ucm_max_lemma_size               10
% 7.92/1.48  
% 7.92/1.48  ------ AIG Options
% 7.92/1.48  
% 7.92/1.48  --aig_mode                              false
% 7.92/1.48  
% 7.92/1.48  ------ Instantiation Options
% 7.92/1.48  
% 7.92/1.48  --instantiation_flag                    true
% 7.92/1.48  --inst_sos_flag                         true
% 7.92/1.48  --inst_sos_phase                        true
% 7.92/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.48  --inst_lit_sel_side                     none
% 7.92/1.48  --inst_solver_per_active                1400
% 7.92/1.48  --inst_solver_calls_frac                1.
% 7.92/1.48  --inst_passive_queue_type               priority_queues
% 7.92/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.92/1.48  --inst_passive_queues_freq              [25;2]
% 7.92/1.48  --inst_dismatching                      true
% 7.92/1.48  --inst_eager_unprocessed_to_passive     true
% 7.92/1.48  --inst_prop_sim_given                   true
% 7.92/1.48  --inst_prop_sim_new                     false
% 7.92/1.48  --inst_subs_new                         false
% 7.92/1.48  --inst_eq_res_simp                      false
% 7.92/1.48  --inst_subs_given                       false
% 7.92/1.48  --inst_orphan_elimination               true
% 7.92/1.48  --inst_learning_loop_flag               true
% 7.92/1.48  --inst_learning_start                   3000
% 7.92/1.48  --inst_learning_factor                  2
% 7.92/1.48  --inst_start_prop_sim_after_learn       3
% 7.92/1.48  --inst_sel_renew                        solver
% 7.92/1.48  --inst_lit_activity_flag                true
% 7.92/1.48  --inst_restr_to_given                   false
% 7.92/1.48  --inst_activity_threshold               500
% 7.92/1.48  --inst_out_proof                        true
% 7.92/1.48  
% 7.92/1.48  ------ Resolution Options
% 7.92/1.48  
% 7.92/1.48  --resolution_flag                       false
% 7.92/1.48  --res_lit_sel                           adaptive
% 7.92/1.48  --res_lit_sel_side                      none
% 7.92/1.48  --res_ordering                          kbo
% 7.92/1.48  --res_to_prop_solver                    active
% 7.92/1.48  --res_prop_simpl_new                    false
% 7.92/1.48  --res_prop_simpl_given                  true
% 7.92/1.48  --res_passive_queue_type                priority_queues
% 7.92/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.92/1.48  --res_passive_queues_freq               [15;5]
% 7.92/1.48  --res_forward_subs                      full
% 7.92/1.48  --res_backward_subs                     full
% 7.92/1.48  --res_forward_subs_resolution           true
% 7.92/1.48  --res_backward_subs_resolution          true
% 7.92/1.48  --res_orphan_elimination                true
% 7.92/1.48  --res_time_limit                        2.
% 7.92/1.48  --res_out_proof                         true
% 7.92/1.48  
% 7.92/1.48  ------ Superposition Options
% 7.92/1.48  
% 7.92/1.48  --superposition_flag                    true
% 7.92/1.48  --sup_passive_queue_type                priority_queues
% 7.92/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.48  --demod_completeness_check              fast
% 7.92/1.48  --demod_use_ground                      true
% 7.92/1.48  --sup_to_prop_solver                    passive
% 7.92/1.48  --sup_prop_simpl_new                    true
% 7.92/1.48  --sup_prop_simpl_given                  true
% 7.92/1.48  --sup_fun_splitting                     true
% 7.92/1.48  --sup_smt_interval                      50000
% 7.92/1.48  
% 7.92/1.48  ------ Superposition Simplification Setup
% 7.92/1.48  
% 7.92/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.48  --sup_immed_triv                        [TrivRules]
% 7.92/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_immed_bw_main                     []
% 7.92/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.48  --sup_input_bw                          []
% 7.92/1.48  
% 7.92/1.48  ------ Combination Options
% 7.92/1.48  
% 7.92/1.48  --comb_res_mult                         3
% 7.92/1.48  --comb_sup_mult                         2
% 7.92/1.48  --comb_inst_mult                        10
% 7.92/1.48  
% 7.92/1.48  ------ Debug Options
% 7.92/1.48  
% 7.92/1.48  --dbg_backtrace                         false
% 7.92/1.48  --dbg_dump_prop_clauses                 false
% 7.92/1.48  --dbg_dump_prop_clauses_file            -
% 7.92/1.48  --dbg_out_stat                          false
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  ------ Proving...
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  % SZS status Theorem for theBenchmark.p
% 7.92/1.48  
% 7.92/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.48  
% 7.92/1.48  fof(f21,conjecture,(
% 7.92/1.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f22,negated_conjecture,(
% 7.92/1.48    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.92/1.48    inference(negated_conjecture,[],[f21])).
% 7.92/1.48  
% 7.92/1.48  fof(f29,plain,(
% 7.92/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.92/1.48    inference(ennf_transformation,[],[f22])).
% 7.92/1.48  
% 7.92/1.48  fof(f37,plain,(
% 7.92/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1))),
% 7.92/1.48    introduced(choice_axiom,[])).
% 7.92/1.48  
% 7.92/1.48  fof(f38,plain,(
% 7.92/1.48    (k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 7.92/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f37])).
% 7.92/1.48  
% 7.92/1.48  fof(f66,plain,(
% 7.92/1.48    k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 7.92/1.48    inference(cnf_transformation,[],[f38])).
% 7.92/1.48  
% 7.92/1.48  fof(f20,axiom,(
% 7.92/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f65,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.92/1.48    inference(cnf_transformation,[],[f20])).
% 7.92/1.48  
% 7.92/1.48  fof(f75,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.92/1.48    inference(definition_unfolding,[],[f65,f74])).
% 7.92/1.48  
% 7.92/1.48  fof(f12,axiom,(
% 7.92/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f55,plain,(
% 7.92/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f12])).
% 7.92/1.48  
% 7.92/1.48  fof(f13,axiom,(
% 7.92/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f56,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f13])).
% 7.92/1.48  
% 7.92/1.48  fof(f14,axiom,(
% 7.92/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f57,plain,(
% 7.92/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f14])).
% 7.92/1.48  
% 7.92/1.48  fof(f15,axiom,(
% 7.92/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f58,plain,(
% 7.92/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f15])).
% 7.92/1.48  
% 7.92/1.48  fof(f16,axiom,(
% 7.92/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f59,plain,(
% 7.92/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f16])).
% 7.92/1.48  
% 7.92/1.48  fof(f17,axiom,(
% 7.92/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f60,plain,(
% 7.92/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f17])).
% 7.92/1.48  
% 7.92/1.48  fof(f18,axiom,(
% 7.92/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f61,plain,(
% 7.92/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f18])).
% 7.92/1.48  
% 7.92/1.48  fof(f70,plain,(
% 7.92/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f60,f61])).
% 7.92/1.48  
% 7.92/1.48  fof(f71,plain,(
% 7.92/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f59,f70])).
% 7.92/1.48  
% 7.92/1.48  fof(f72,plain,(
% 7.92/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f58,f71])).
% 7.92/1.48  
% 7.92/1.48  fof(f73,plain,(
% 7.92/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f57,f72])).
% 7.92/1.48  
% 7.92/1.48  fof(f74,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f56,f73])).
% 7.92/1.48  
% 7.92/1.48  fof(f78,plain,(
% 7.92/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f55,f74])).
% 7.92/1.48  
% 7.92/1.48  fof(f89,plain,(
% 7.92/1.48    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 7.92/1.48    inference(definition_unfolding,[],[f66,f75,f78])).
% 7.92/1.48  
% 7.92/1.48  fof(f7,axiom,(
% 7.92/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f50,plain,(
% 7.92/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f7])).
% 7.92/1.48  
% 7.92/1.48  fof(f5,axiom,(
% 7.92/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f48,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f5])).
% 7.92/1.48  
% 7.92/1.48  fof(f11,axiom,(
% 7.92/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f54,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.92/1.48    inference(cnf_transformation,[],[f11])).
% 7.92/1.48  
% 7.92/1.48  fof(f76,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.92/1.48    inference(definition_unfolding,[],[f54,f75])).
% 7.92/1.48  
% 7.92/1.48  fof(f77,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f48,f76])).
% 7.92/1.48  
% 7.92/1.48  fof(f81,plain,(
% 7.92/1.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 7.92/1.48    inference(definition_unfolding,[],[f50,f77])).
% 7.92/1.48  
% 7.92/1.48  fof(f8,axiom,(
% 7.92/1.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f51,plain,(
% 7.92/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.92/1.48    inference(cnf_transformation,[],[f8])).
% 7.92/1.48  
% 7.92/1.48  fof(f82,plain,(
% 7.92/1.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.92/1.48    inference(definition_unfolding,[],[f51,f75])).
% 7.92/1.48  
% 7.92/1.48  fof(f19,axiom,(
% 7.92/1.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f35,plain,(
% 7.92/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.92/1.48    inference(nnf_transformation,[],[f19])).
% 7.92/1.48  
% 7.92/1.48  fof(f36,plain,(
% 7.92/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.92/1.48    inference(flattening,[],[f35])).
% 7.92/1.48  
% 7.92/1.48  fof(f62,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.92/1.48    inference(cnf_transformation,[],[f36])).
% 7.92/1.48  
% 7.92/1.48  fof(f85,plain,(
% 7.92/1.48    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.92/1.48    inference(definition_unfolding,[],[f62,f78,f78])).
% 7.92/1.48  
% 7.92/1.48  fof(f10,axiom,(
% 7.92/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f53,plain,(
% 7.92/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.92/1.48    inference(cnf_transformation,[],[f10])).
% 7.92/1.48  
% 7.92/1.48  fof(f9,axiom,(
% 7.92/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f52,plain,(
% 7.92/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f9])).
% 7.92/1.48  
% 7.92/1.48  fof(f3,axiom,(
% 7.92/1.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f24,plain,(
% 7.92/1.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.92/1.48    inference(rectify,[],[f3])).
% 7.92/1.48  
% 7.92/1.48  fof(f43,plain,(
% 7.92/1.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.92/1.48    inference(cnf_transformation,[],[f24])).
% 7.92/1.48  
% 7.92/1.48  fof(f80,plain,(
% 7.92/1.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.92/1.48    inference(definition_unfolding,[],[f43,f76])).
% 7.92/1.48  
% 7.92/1.48  fof(f2,axiom,(
% 7.92/1.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f23,plain,(
% 7.92/1.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.92/1.48    inference(rectify,[],[f2])).
% 7.92/1.48  
% 7.92/1.48  fof(f42,plain,(
% 7.92/1.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.92/1.48    inference(cnf_transformation,[],[f23])).
% 7.92/1.48  
% 7.92/1.48  fof(f79,plain,(
% 7.92/1.48    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.92/1.48    inference(definition_unfolding,[],[f42,f75])).
% 7.92/1.48  
% 7.92/1.48  fof(f67,plain,(
% 7.92/1.48    k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2),
% 7.92/1.48    inference(cnf_transformation,[],[f38])).
% 7.92/1.48  
% 7.92/1.48  fof(f88,plain,(
% 7.92/1.48    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 7.92/1.48    inference(definition_unfolding,[],[f67,f78,f78])).
% 7.92/1.48  
% 7.92/1.48  fof(f68,plain,(
% 7.92/1.48    k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2),
% 7.92/1.48    inference(cnf_transformation,[],[f38])).
% 7.92/1.48  
% 7.92/1.48  fof(f87,plain,(
% 7.92/1.48    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k1_xboole_0 != sK2),
% 7.92/1.48    inference(definition_unfolding,[],[f68,f78])).
% 7.92/1.48  
% 7.92/1.48  fof(f69,plain,(
% 7.92/1.48    k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2),
% 7.92/1.48    inference(cnf_transformation,[],[f38])).
% 7.92/1.48  
% 7.92/1.48  fof(f86,plain,(
% 7.92/1.48    k1_xboole_0 != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 7.92/1.48    inference(definition_unfolding,[],[f69,f78])).
% 7.92/1.48  
% 7.92/1.48  fof(f6,axiom,(
% 7.92/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f27,plain,(
% 7.92/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.92/1.48    inference(ennf_transformation,[],[f6])).
% 7.92/1.48  
% 7.92/1.48  fof(f28,plain,(
% 7.92/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.92/1.48    inference(flattening,[],[f27])).
% 7.92/1.48  
% 7.92/1.48  fof(f49,plain,(
% 7.92/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f28])).
% 7.92/1.48  
% 7.92/1.48  fof(f1,axiom,(
% 7.92/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f25,plain,(
% 7.92/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.92/1.48    inference(ennf_transformation,[],[f1])).
% 7.92/1.48  
% 7.92/1.48  fof(f30,plain,(
% 7.92/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.92/1.48    inference(nnf_transformation,[],[f25])).
% 7.92/1.48  
% 7.92/1.48  fof(f31,plain,(
% 7.92/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.92/1.48    inference(rectify,[],[f30])).
% 7.92/1.48  
% 7.92/1.48  fof(f32,plain,(
% 7.92/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.92/1.48    introduced(choice_axiom,[])).
% 7.92/1.48  
% 7.92/1.48  fof(f33,plain,(
% 7.92/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.92/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.92/1.48  
% 7.92/1.48  fof(f39,plain,(
% 7.92/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.92/1.48    inference(cnf_transformation,[],[f33])).
% 7.92/1.48  
% 7.92/1.48  fof(f4,axiom,(
% 7.92/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.92/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.48  
% 7.92/1.48  fof(f26,plain,(
% 7.92/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.92/1.48    inference(ennf_transformation,[],[f4])).
% 7.92/1.48  
% 7.92/1.48  fof(f34,plain,(
% 7.92/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.92/1.48    inference(nnf_transformation,[],[f26])).
% 7.92/1.48  
% 7.92/1.48  fof(f45,plain,(
% 7.92/1.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.92/1.48    inference(cnf_transformation,[],[f34])).
% 7.92/1.48  
% 7.92/1.48  cnf(c_20,negated_conjecture,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 7.92/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_10,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 7.92/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_373,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_6445,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_20,c_373]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_11,plain,
% 7.92/1.48      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 7.92/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_372,plain,
% 7.92/1.48      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_4556,plain,
% 7.92/1.48      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_20,c_372]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_16,plain,
% 7.92/1.48      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.92/1.48      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.92/1.48      | k1_xboole_0 = X0 ),
% 7.92/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_369,plain,
% 7.92/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.92/1.48      | k1_xboole_0 = X1
% 7.92/1.48      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_5758,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_4556,c_369]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_5761,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
% 7.92/1.48      | sK2 = k1_xboole_0
% 7.92/1.48      | k1_xboole_0 = X0
% 7.92/1.48      | r1_tarski(X0,sK2) != iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_5758,c_369]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7719,plain,
% 7.92/1.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 7.92/1.48      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_6445,c_5761]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_13,plain,
% 7.92/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.92/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_12,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.92/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_585,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_4,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.92/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_3,plain,
% 7.92/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.92/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_382,plain,
% 7.92/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.92/1.48      inference(light_normalisation,[status(thm)],[c_4,c_3,c_13]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_588,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_585,c_382]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7905,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.92/1.48      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_7719,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_19,negated_conjecture,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 7.92/1.48      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 7.92/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_5764,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_5758,c_19]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_18,negated_conjecture,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 7.92/1.48      | k1_xboole_0 != sK2 ),
% 7.92/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_404,plain,
% 7.92/1.48      ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.92/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
% 7.92/1.48      | k1_xboole_0 = sK2 ),
% 7.92/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_406,plain,
% 7.92/1.48      ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.92/1.48      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 7.92/1.48      | k1_xboole_0 = sK2 ),
% 7.92/1.48      inference(instantiation,[status(thm)],[c_404]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_4560,plain,
% 7.92/1.48      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.92/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4556]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_5959,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_5764,c_19,c_18,c_406,c_4560]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7935,plain,
% 7.92/1.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0
% 7.92/1.48      | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_7719,c_6445]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_17,negated_conjecture,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 7.92/1.48      | k1_xboole_0 != sK3 ),
% 7.92/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_5766,plain,
% 7.92/1.48      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_5758,c_17]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_594,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_12,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_757,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_588,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_1244,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_13,c_757]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_1466,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_1244,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_1949,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_12,c_1466]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7932,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK3),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 7.92/1.48      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_7719,c_1949]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_754,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_13,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_593,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_13,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_770,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.92/1.48      inference(light_normalisation,[status(thm)],[c_754,c_593]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_587,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_664,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_587,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_672,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_664,c_593]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_808,plain,
% 7.92/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_672,c_588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_804,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_594,c_672]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_2346,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_808,c_804]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7954,plain,
% 7.92/1.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0
% 7.92/1.48      | sK3 = k1_xboole_0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_7932,c_770,c_2346]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_8051,plain,
% 7.92/1.48      ( sK2 = k1_xboole_0
% 7.92/1.48      | k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_7935,c_5766,c_7954]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_8052,plain,
% 7.92/1.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(renaming,[status(thm)],[c_8051]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_906,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_808,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_8119,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK3),sK2),k1_xboole_0)
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_8052,c_906]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_8123,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 7.92/1.48      | sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_8119,c_588,c_1244]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_9431,plain,
% 7.92/1.48      ( sK2 = k1_xboole_0 ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_7905,c_19,c_18,c_406,c_4560,c_8123]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7574,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_808,c_6445]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_800,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_12,c_672]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_746,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),X2))) = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_588,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_1650,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_800,c_746]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7578,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3),sK2) = iProver_top ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_7574,c_1650]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7662,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK2) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_808,c_7578]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_9434,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) = iProver_top ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_9431,c_7662]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_9,plain,
% 7.92/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.92/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_374,plain,
% 7.92/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.92/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.92/1.48      | r1_tarski(X0,X2) = iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_15663,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = iProver_top
% 7.92/1.48      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_9434,c_374]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_6444,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0)),X0) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_3,c_373]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_6449,plain,
% 7.92/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.92/1.48      inference(light_normalisation,[status(thm)],[c_6444,c_13,c_382]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_19439,plain,
% 7.92/1.48      ( r1_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = iProver_top ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_15663,c_6449]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_19447,plain,
% 7.92/1.48      ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 7.92/1.48      | k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_19439,c_369]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_24535,plain,
% 7.92/1.48      ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 7.92/1.48      | k3_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = X0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_19447,c_3]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_26188,plain,
% 7.92/1.48      ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 7.92/1.48      | k3_tarski(k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_24535,c_13]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_27660,plain,
% 7.92/1.48      ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 7.92/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_19447,c_26188]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_27661,plain,
% 7.92/1.48      ( k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 7.92/1.48      | k1_xboole_0 = X0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_27660,c_3]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_2,plain,
% 7.92/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.92/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_379,plain,
% 7.92/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.92/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.92/1.48      | r1_tarski(X1,X2) != iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_15697,plain,
% 7.92/1.48      ( r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top
% 7.92/1.48      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_9434,c_379]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_7,plain,
% 7.92/1.48      ( ~ r2_hidden(X0,X1)
% 7.92/1.48      | ~ r2_hidden(X0,X2)
% 7.92/1.48      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.92/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_376,plain,
% 7.92/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.92/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.92/1.48      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 7.92/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_17561,plain,
% 7.92/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.92/1.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_593,c_376]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_19446,plain,
% 7.92/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.92/1.48      | r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_19439,c_379]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_22484,plain,
% 7.92/1.48      ( r2_hidden(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != iProver_top ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_15697,c_17561,c_19446]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29579,plain,
% 7.92/1.48      ( k1_xboole_0 = X0 | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_27661,c_22484]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_744,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = X3 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_12,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29574,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 7.92/1.48      | k1_xboole_0 = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_27661,c_744]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29587,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X1,X0)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 7.92/1.48      | k1_xboole_0 = X2 ),
% 7.92/1.48      inference(light_normalisation,[status(thm)],[c_29574,c_1244]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_811,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_672,c_594]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_597,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_588,c_12]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_599,plain,
% 7.92/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 7.92/1.48      inference(light_normalisation,[status(thm)],[c_597,c_12]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_1000,plain,
% 7.92/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_811,c_599]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29588,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 7.92/1.48      | k1_xboole_0 = X0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_29587,c_1000]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29894,plain,
% 7.92/1.48      ( k1_xboole_0 = X0 ),
% 7.92/1.48      inference(global_propositional_subsumption,
% 7.92/1.48                [status(thm)],
% 7.92/1.48                [c_29579,c_19,c_18,c_406,c_4560,c_29588]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_30051,plain,
% 7.92/1.48      ( X0 = X1 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_29894,c_29894]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29901,plain,
% 7.92/1.48      ( k3_tarski(k1_xboole_0) = X0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_29894,c_3]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_29975,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_29894,c_5959]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_30032,plain,
% 7.92/1.48      ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
% 7.92/1.48      inference(demodulation,[status(thm)],[c_29901,c_29975]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_30167,plain,
% 7.92/1.48      ( k1_xboole_0 != X0 ),
% 7.92/1.48      inference(superposition,[status(thm)],[c_30051,c_30032]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_30170,plain,
% 7.92/1.48      ( k1_xboole_0 != sK1 ),
% 7.92/1.48      inference(grounding,[status(thm)],[c_30167:[bind(X0,$fot(sK1))]]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(c_30171,plain,
% 7.92/1.48      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 7.92/1.48      | k1_xboole_0 = sK1 ),
% 7.92/1.48      inference(grounding,[status(thm)],[c_29588:[bind(X0,$fot(sK1))]]) ).
% 7.92/1.48  
% 7.92/1.48  cnf(contradiction,plain,
% 7.92/1.48      ( $false ),
% 7.92/1.48      inference(minisat,[status(thm)],[c_30170,c_30171,c_5959]) ).
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.48  
% 7.92/1.48  ------                               Statistics
% 7.92/1.48  
% 7.92/1.48  ------ General
% 7.92/1.48  
% 7.92/1.48  abstr_ref_over_cycles:                  0
% 7.92/1.48  abstr_ref_under_cycles:                 0
% 7.92/1.48  gc_basic_clause_elim:                   0
% 7.92/1.48  forced_gc_time:                         0
% 7.92/1.48  parsing_time:                           0.01
% 7.92/1.48  unif_index_cands_time:                  0.
% 7.92/1.48  unif_index_add_time:                    0.
% 7.92/1.48  orderings_time:                         0.
% 7.92/1.48  out_proof_time:                         0.013
% 7.92/1.48  total_time:                             0.845
% 7.92/1.48  num_of_symbols:                         42
% 7.92/1.48  num_of_terms:                           51869
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing
% 7.92/1.48  
% 7.92/1.48  num_of_splits:                          0
% 7.92/1.48  num_of_split_atoms:                     1
% 7.92/1.48  num_of_reused_defs:                     3
% 7.92/1.48  num_eq_ax_congr_red:                    4
% 7.92/1.48  num_of_sem_filtered_clauses:            1
% 7.92/1.48  num_of_subtypes:                        0
% 7.92/1.48  monotx_restored_types:                  0
% 7.92/1.48  sat_num_of_epr_types:                   0
% 7.92/1.48  sat_num_of_non_cyclic_types:            0
% 7.92/1.48  sat_guarded_non_collapsed_types:        0
% 7.92/1.48  num_pure_diseq_elim:                    0
% 7.92/1.48  simp_replaced_by:                       0
% 7.92/1.48  res_preprocessed:                       78
% 7.92/1.48  prep_upred:                             0
% 7.92/1.48  prep_unflattend:                        0
% 7.92/1.48  smt_new_axioms:                         0
% 7.92/1.48  pred_elim_cands:                        2
% 7.92/1.48  pred_elim:                              0
% 7.92/1.48  pred_elim_cl:                           0
% 7.92/1.48  pred_elim_cycles:                       1
% 7.92/1.48  merged_defs:                            0
% 7.92/1.48  merged_defs_ncl:                        0
% 7.92/1.48  bin_hyper_res:                          0
% 7.92/1.48  prep_cycles:                            3
% 7.92/1.48  pred_elim_time:                         0.
% 7.92/1.48  splitting_time:                         0.
% 7.92/1.48  sem_filter_time:                        0.
% 7.92/1.48  monotx_time:                            0.001
% 7.92/1.48  subtype_inf_time:                       0.
% 7.92/1.48  
% 7.92/1.48  ------ Problem properties
% 7.92/1.48  
% 7.92/1.48  clauses:                                21
% 7.92/1.48  conjectures:                            4
% 7.92/1.48  epr:                                    2
% 7.92/1.48  horn:                                   16
% 7.92/1.48  ground:                                 4
% 7.92/1.48  unary:                                  9
% 7.92/1.48  binary:                                 5
% 7.92/1.48  lits:                                   40
% 7.92/1.48  lits_eq:                                13
% 7.92/1.48  fd_pure:                                0
% 7.92/1.48  fd_pseudo:                              0
% 7.92/1.48  fd_cond:                                0
% 7.92/1.48  fd_pseudo_cond:                         1
% 7.92/1.48  ac_symbols:                             1
% 7.92/1.48  
% 7.92/1.48  ------ Propositional Solver
% 7.92/1.48  
% 7.92/1.48  prop_solver_calls:                      29
% 7.92/1.48  prop_fast_solver_calls:                 755
% 7.92/1.48  smt_solver_calls:                       0
% 7.92/1.48  smt_fast_solver_calls:                  0
% 7.92/1.48  prop_num_of_clauses:                    5809
% 7.92/1.48  prop_preprocess_simplified:             9988
% 7.92/1.48  prop_fo_subsumed:                       87
% 7.92/1.48  prop_solver_time:                       0.
% 7.92/1.48  smt_solver_time:                        0.
% 7.92/1.48  smt_fast_solver_time:                   0.
% 7.92/1.48  prop_fast_solver_time:                  0.
% 7.92/1.48  prop_unsat_core_time:                   0.
% 7.92/1.48  
% 7.92/1.48  ------ QBF
% 7.92/1.48  
% 7.92/1.48  qbf_q_res:                              0
% 7.92/1.48  qbf_num_tautologies:                    0
% 7.92/1.48  qbf_prep_cycles:                        0
% 7.92/1.48  
% 7.92/1.48  ------ BMC1
% 7.92/1.48  
% 7.92/1.48  bmc1_current_bound:                     -1
% 7.92/1.48  bmc1_last_solved_bound:                 -1
% 7.92/1.48  bmc1_unsat_core_size:                   -1
% 7.92/1.48  bmc1_unsat_core_parents_size:           -1
% 7.92/1.48  bmc1_merge_next_fun:                    0
% 7.92/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.92/1.48  
% 7.92/1.48  ------ Instantiation
% 7.92/1.48  
% 7.92/1.48  inst_num_of_clauses:                    1364
% 7.92/1.48  inst_num_in_passive:                    568
% 7.92/1.48  inst_num_in_active:                     478
% 7.92/1.48  inst_num_in_unprocessed:                318
% 7.92/1.48  inst_num_of_loops:                      670
% 7.92/1.48  inst_num_of_learning_restarts:          0
% 7.92/1.48  inst_num_moves_active_passive:          187
% 7.92/1.48  inst_lit_activity:                      0
% 7.92/1.48  inst_lit_activity_moves:                0
% 7.92/1.48  inst_num_tautologies:                   0
% 7.92/1.48  inst_num_prop_implied:                  0
% 7.92/1.48  inst_num_existing_simplified:           0
% 7.92/1.48  inst_num_eq_res_simplified:             0
% 7.92/1.48  inst_num_child_elim:                    0
% 7.92/1.48  inst_num_of_dismatching_blockings:      556
% 7.92/1.48  inst_num_of_non_proper_insts:           1564
% 7.92/1.48  inst_num_of_duplicates:                 0
% 7.92/1.48  inst_inst_num_from_inst_to_res:         0
% 7.92/1.48  inst_dismatching_checking_time:         0.
% 7.92/1.48  
% 7.92/1.48  ------ Resolution
% 7.92/1.48  
% 7.92/1.48  res_num_of_clauses:                     0
% 7.92/1.48  res_num_in_passive:                     0
% 7.92/1.48  res_num_in_active:                      0
% 7.92/1.48  res_num_of_loops:                       81
% 7.92/1.48  res_forward_subset_subsumed:            127
% 7.92/1.48  res_backward_subset_subsumed:           0
% 7.92/1.48  res_forward_subsumed:                   0
% 7.92/1.48  res_backward_subsumed:                  0
% 7.92/1.48  res_forward_subsumption_resolution:     0
% 7.92/1.48  res_backward_subsumption_resolution:    0
% 7.92/1.48  res_clause_to_clause_subsumption:       52568
% 7.92/1.48  res_orphan_elimination:                 0
% 7.92/1.48  res_tautology_del:                      145
% 7.92/1.48  res_num_eq_res_simplified:              0
% 7.92/1.48  res_num_sel_changes:                    0
% 7.92/1.48  res_moves_from_active_to_pass:          0
% 7.92/1.48  
% 7.92/1.48  ------ Superposition
% 7.92/1.48  
% 7.92/1.48  sup_time_total:                         0.
% 7.92/1.48  sup_time_generating:                    0.
% 7.92/1.48  sup_time_sim_full:                      0.
% 7.92/1.48  sup_time_sim_immed:                     0.
% 7.92/1.48  
% 7.92/1.48  sup_num_of_clauses:                     1313
% 7.92/1.48  sup_num_in_active:                      6
% 7.92/1.48  sup_num_in_passive:                     1307
% 7.92/1.48  sup_num_of_loops:                       133
% 7.92/1.48  sup_fw_superposition:                   6511
% 7.92/1.48  sup_bw_superposition:                   5983
% 7.92/1.48  sup_immediate_simplified:               6488
% 7.92/1.48  sup_given_eliminated:                   11
% 7.92/1.48  comparisons_done:                       0
% 7.92/1.48  comparisons_avoided:                    18
% 7.92/1.48  
% 7.92/1.48  ------ Simplifications
% 7.92/1.48  
% 7.92/1.48  
% 7.92/1.48  sim_fw_subset_subsumed:                 210
% 7.92/1.48  sim_bw_subset_subsumed:                 91
% 7.92/1.48  sim_fw_subsumed:                        422
% 7.92/1.48  sim_bw_subsumed:                        105
% 7.92/1.48  sim_fw_subsumption_res:                 0
% 7.92/1.48  sim_bw_subsumption_res:                 0
% 7.92/1.48  sim_tautology_del:                      14
% 7.92/1.48  sim_eq_tautology_del:                   892
% 7.92/1.48  sim_eq_res_simp:                        2
% 7.92/1.48  sim_fw_demodulated:                     5522
% 7.92/1.48  sim_bw_demodulated:                     146
% 7.92/1.48  sim_light_normalised:                   2340
% 7.92/1.48  sim_joinable_taut:                      354
% 7.92/1.48  sim_joinable_simp:                      0
% 7.92/1.48  sim_ac_normalised:                      0
% 7.92/1.48  sim_smt_subsumption:                    0
% 7.92/1.48  
%------------------------------------------------------------------------------
