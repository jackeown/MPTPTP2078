%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:28 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  157 (1615 expanded)
%              Number of clauses        :   69 ( 144 expanded)
%              Number of leaves         :   23 ( 501 expanded)
%              Depth                    :   21
%              Number of atoms          :  410 (2610 expanded)
%              Number of equality atoms :  308 (2268 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f66,f78,f79])).

fof(f112,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f37])).

fof(f71,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f71,f78,f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f64,f78,f79,f79,f78])).

fof(f72,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f69,f79,f79,f79])).

fof(f114,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f70,f79,f79,f79])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f106,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f107,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f106])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f45,f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f73,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f60,f78,f79])).

cnf(c_19,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_499,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_496,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_497,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1212,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_496,c_497])).

cnf(c_2589,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_499])).

cnf(c_25,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_28,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_29,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_55,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_545,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))
    | sK1 = X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_626,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_802,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_1159,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1161,plain,
    ( r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1026,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1027,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1032,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1027,c_6])).

cnf(c_1029,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1030,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1029,c_5])).

cnf(c_1033,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1032,c_1030])).

cnf(c_1034,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1026,c_1033])).

cnf(c_1325,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23,c_1034])).

cnf(c_1326,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1374,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_497])).

cnf(c_2593,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_499,c_1374])).

cnf(c_3065,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2589,c_25,c_28,c_29,c_55,c_626,c_1161,c_1326,c_2593])).

cnf(c_3066,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3065])).

cnf(c_3070,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_497])).

cnf(c_1113,plain,
    ( ~ r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1114,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_512,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2034,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_496,c_512])).

cnf(c_2145,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2034,c_0])).

cnf(c_2149,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2145,c_1033])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_513,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2733,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_513])).

cnf(c_2800,plain,
    ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top
    | r1_tarski(X0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_2733])).

cnf(c_2801,plain,
    ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top
    | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2800,c_1032])).

cnf(c_3862,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3070,c_1114,c_2801])).

cnf(c_3868,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_499,c_3862])).

cnf(c_24,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_534,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))
    | sK1 = X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_565,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_936,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_938,plain,
    ( r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_5059,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3868,c_25,c_24,c_28,c_29,c_55,c_565,c_626,c_938,c_1161,c_1326])).

cnf(c_507,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5074,plain,
    ( r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5059,c_507])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_562,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_563,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_544,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5074,c_563,c_544,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:53:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.54/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.99  
% 3.54/0.99  ------  iProver source info
% 3.54/0.99  
% 3.54/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.99  git: non_committed_changes: false
% 3.54/0.99  git: last_make_outside_of_git: false
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options
% 3.54/0.99  
% 3.54/0.99  --out_options                           all
% 3.54/0.99  --tptp_safe_out                         true
% 3.54/0.99  --problem_path                          ""
% 3.54/0.99  --include_path                          ""
% 3.54/0.99  --clausifier                            res/vclausify_rel
% 3.54/0.99  --clausifier_options                    ""
% 3.54/0.99  --stdin                                 false
% 3.54/0.99  --stats_out                             all
% 3.54/0.99  
% 3.54/0.99  ------ General Options
% 3.54/0.99  
% 3.54/0.99  --fof                                   false
% 3.54/0.99  --time_out_real                         305.
% 3.54/0.99  --time_out_virtual                      -1.
% 3.54/0.99  --symbol_type_check                     false
% 3.54/0.99  --clausify_out                          false
% 3.54/0.99  --sig_cnt_out                           false
% 3.54/0.99  --trig_cnt_out                          false
% 3.54/0.99  --trig_cnt_out_tolerance                1.
% 3.54/0.99  --trig_cnt_out_sk_spl                   false
% 3.54/0.99  --abstr_cl_out                          false
% 3.54/0.99  
% 3.54/0.99  ------ Global Options
% 3.54/0.99  
% 3.54/0.99  --schedule                              default
% 3.54/0.99  --add_important_lit                     false
% 3.54/0.99  --prop_solver_per_cl                    1000
% 3.54/0.99  --min_unsat_core                        false
% 3.54/0.99  --soft_assumptions                      false
% 3.54/0.99  --soft_lemma_size                       3
% 3.54/0.99  --prop_impl_unit_size                   0
% 3.54/0.99  --prop_impl_unit                        []
% 3.54/0.99  --share_sel_clauses                     true
% 3.54/0.99  --reset_solvers                         false
% 3.54/0.99  --bc_imp_inh                            [conj_cone]
% 3.54/0.99  --conj_cone_tolerance                   3.
% 3.54/0.99  --extra_neg_conj                        none
% 3.54/0.99  --large_theory_mode                     true
% 3.54/0.99  --prolific_symb_bound                   200
% 3.54/0.99  --lt_threshold                          2000
% 3.54/0.99  --clause_weak_htbl                      true
% 3.54/0.99  --gc_record_bc_elim                     false
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing Options
% 3.54/0.99  
% 3.54/0.99  --preprocessing_flag                    true
% 3.54/0.99  --time_out_prep_mult                    0.1
% 3.54/0.99  --splitting_mode                        input
% 3.54/0.99  --splitting_grd                         true
% 3.54/0.99  --splitting_cvd                         false
% 3.54/0.99  --splitting_cvd_svl                     false
% 3.54/0.99  --splitting_nvd                         32
% 3.54/0.99  --sub_typing                            true
% 3.54/0.99  --prep_gs_sim                           true
% 3.54/0.99  --prep_unflatten                        true
% 3.54/0.99  --prep_res_sim                          true
% 3.54/0.99  --prep_upred                            true
% 3.54/0.99  --prep_sem_filter                       exhaustive
% 3.54/0.99  --prep_sem_filter_out                   false
% 3.54/0.99  --pred_elim                             true
% 3.54/0.99  --res_sim_input                         true
% 3.54/0.99  --eq_ax_congr_red                       true
% 3.54/0.99  --pure_diseq_elim                       true
% 3.54/0.99  --brand_transform                       false
% 3.54/0.99  --non_eq_to_eq                          false
% 3.54/0.99  --prep_def_merge                        true
% 3.54/0.99  --prep_def_merge_prop_impl              false
% 3.54/0.99  --prep_def_merge_mbd                    true
% 3.54/0.99  --prep_def_merge_tr_red                 false
% 3.54/0.99  --prep_def_merge_tr_cl                  false
% 3.54/0.99  --smt_preprocessing                     true
% 3.54/0.99  --smt_ac_axioms                         fast
% 3.54/0.99  --preprocessed_out                      false
% 3.54/0.99  --preprocessed_stats                    false
% 3.54/0.99  
% 3.54/0.99  ------ Abstraction refinement Options
% 3.54/0.99  
% 3.54/0.99  --abstr_ref                             []
% 3.54/0.99  --abstr_ref_prep                        false
% 3.54/0.99  --abstr_ref_until_sat                   false
% 3.54/0.99  --abstr_ref_sig_restrict                funpre
% 3.54/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.99  --abstr_ref_under                       []
% 3.54/0.99  
% 3.54/0.99  ------ SAT Options
% 3.54/0.99  
% 3.54/0.99  --sat_mode                              false
% 3.54/0.99  --sat_fm_restart_options                ""
% 3.54/0.99  --sat_gr_def                            false
% 3.54/0.99  --sat_epr_types                         true
% 3.54/0.99  --sat_non_cyclic_types                  false
% 3.54/0.99  --sat_finite_models                     false
% 3.54/0.99  --sat_fm_lemmas                         false
% 3.54/0.99  --sat_fm_prep                           false
% 3.54/0.99  --sat_fm_uc_incr                        true
% 3.54/0.99  --sat_out_model                         small
% 3.54/0.99  --sat_out_clauses                       false
% 3.54/0.99  
% 3.54/0.99  ------ QBF Options
% 3.54/0.99  
% 3.54/0.99  --qbf_mode                              false
% 3.54/0.99  --qbf_elim_univ                         false
% 3.54/0.99  --qbf_dom_inst                          none
% 3.54/0.99  --qbf_dom_pre_inst                      false
% 3.54/0.99  --qbf_sk_in                             false
% 3.54/0.99  --qbf_pred_elim                         true
% 3.54/0.99  --qbf_split                             512
% 3.54/0.99  
% 3.54/0.99  ------ BMC1 Options
% 3.54/0.99  
% 3.54/0.99  --bmc1_incremental                      false
% 3.54/0.99  --bmc1_axioms                           reachable_all
% 3.54/0.99  --bmc1_min_bound                        0
% 3.54/0.99  --bmc1_max_bound                        -1
% 3.54/0.99  --bmc1_max_bound_default                -1
% 3.54/0.99  --bmc1_symbol_reachability              true
% 3.54/0.99  --bmc1_property_lemmas                  false
% 3.54/0.99  --bmc1_k_induction                      false
% 3.54/0.99  --bmc1_non_equiv_states                 false
% 3.54/0.99  --bmc1_deadlock                         false
% 3.54/0.99  --bmc1_ucm                              false
% 3.54/0.99  --bmc1_add_unsat_core                   none
% 3.54/0.99  --bmc1_unsat_core_children              false
% 3.54/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.99  --bmc1_out_stat                         full
% 3.54/0.99  --bmc1_ground_init                      false
% 3.54/0.99  --bmc1_pre_inst_next_state              false
% 3.54/0.99  --bmc1_pre_inst_state                   false
% 3.54/0.99  --bmc1_pre_inst_reach_state             false
% 3.54/0.99  --bmc1_out_unsat_core                   false
% 3.54/0.99  --bmc1_aig_witness_out                  false
% 3.54/0.99  --bmc1_verbose                          false
% 3.54/0.99  --bmc1_dump_clauses_tptp                false
% 3.54/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.99  --bmc1_dump_file                        -
% 3.54/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.99  --bmc1_ucm_extend_mode                  1
% 3.54/0.99  --bmc1_ucm_init_mode                    2
% 3.54/0.99  --bmc1_ucm_cone_mode                    none
% 3.54/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.99  --bmc1_ucm_relax_model                  4
% 3.54/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.99  --bmc1_ucm_layered_model                none
% 3.54/0.99  --bmc1_ucm_max_lemma_size               10
% 3.54/0.99  
% 3.54/0.99  ------ AIG Options
% 3.54/0.99  
% 3.54/0.99  --aig_mode                              false
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation Options
% 3.54/0.99  
% 3.54/0.99  --instantiation_flag                    true
% 3.54/0.99  --inst_sos_flag                         true
% 3.54/0.99  --inst_sos_phase                        true
% 3.54/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel_side                     num_symb
% 3.54/0.99  --inst_solver_per_active                1400
% 3.54/0.99  --inst_solver_calls_frac                1.
% 3.54/0.99  --inst_passive_queue_type               priority_queues
% 3.54/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.99  --inst_passive_queues_freq              [25;2]
% 3.54/0.99  --inst_dismatching                      true
% 3.54/0.99  --inst_eager_unprocessed_to_passive     true
% 3.54/0.99  --inst_prop_sim_given                   true
% 3.54/0.99  --inst_prop_sim_new                     false
% 3.54/0.99  --inst_subs_new                         false
% 3.54/0.99  --inst_eq_res_simp                      false
% 3.54/0.99  --inst_subs_given                       false
% 3.54/0.99  --inst_orphan_elimination               true
% 3.54/0.99  --inst_learning_loop_flag               true
% 3.54/0.99  --inst_learning_start                   3000
% 3.54/0.99  --inst_learning_factor                  2
% 3.54/0.99  --inst_start_prop_sim_after_learn       3
% 3.54/0.99  --inst_sel_renew                        solver
% 3.54/0.99  --inst_lit_activity_flag                true
% 3.54/0.99  --inst_restr_to_given                   false
% 3.54/0.99  --inst_activity_threshold               500
% 3.54/0.99  --inst_out_proof                        true
% 3.54/0.99  
% 3.54/0.99  ------ Resolution Options
% 3.54/0.99  
% 3.54/0.99  --resolution_flag                       true
% 3.54/0.99  --res_lit_sel                           adaptive
% 3.54/0.99  --res_lit_sel_side                      none
% 3.54/0.99  --res_ordering                          kbo
% 3.54/0.99  --res_to_prop_solver                    active
% 3.54/0.99  --res_prop_simpl_new                    false
% 3.54/0.99  --res_prop_simpl_given                  true
% 3.54/0.99  --res_passive_queue_type                priority_queues
% 3.54/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.99  --res_passive_queues_freq               [15;5]
% 3.54/0.99  --res_forward_subs                      full
% 3.54/0.99  --res_backward_subs                     full
% 3.54/0.99  --res_forward_subs_resolution           true
% 3.54/0.99  --res_backward_subs_resolution          true
% 3.54/0.99  --res_orphan_elimination                true
% 3.54/0.99  --res_time_limit                        2.
% 3.54/0.99  --res_out_proof                         true
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Options
% 3.54/0.99  
% 3.54/0.99  --superposition_flag                    true
% 3.54/0.99  --sup_passive_queue_type                priority_queues
% 3.54/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.99  --demod_completeness_check              fast
% 3.54/0.99  --demod_use_ground                      true
% 3.54/0.99  --sup_to_prop_solver                    passive
% 3.54/0.99  --sup_prop_simpl_new                    true
% 3.54/0.99  --sup_prop_simpl_given                  true
% 3.54/0.99  --sup_fun_splitting                     true
% 3.54/0.99  --sup_smt_interval                      50000
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Simplification Setup
% 3.54/0.99  
% 3.54/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.54/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.54/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.54/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.54/0.99  --sup_immed_triv                        [TrivRules]
% 3.54/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_bw_main                     []
% 3.54/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.54/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_input_bw                          []
% 3.54/0.99  
% 3.54/0.99  ------ Combination Options
% 3.54/0.99  
% 3.54/0.99  --comb_res_mult                         3
% 3.54/0.99  --comb_sup_mult                         2
% 3.54/0.99  --comb_inst_mult                        10
% 3.54/0.99  
% 3.54/0.99  ------ Debug Options
% 3.54/0.99  
% 3.54/0.99  --dbg_backtrace                         false
% 3.54/0.99  --dbg_dump_prop_clauses                 false
% 3.54/0.99  --dbg_dump_prop_clauses_file            -
% 3.54/0.99  --dbg_out_stat                          false
% 3.54/0.99  ------ Parsing...
% 3.54/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.99  ------ Proving...
% 3.54/0.99  ------ Problem Properties 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  clauses                                 27
% 3.54/0.99  conjectures                             3
% 3.54/0.99  EPR                                     2
% 3.54/0.99  Horn                                    20
% 3.54/0.99  unary                                   15
% 3.54/0.99  binary                                  5
% 3.54/0.99  lits                                    49
% 3.54/0.99  lits eq                                 29
% 3.54/0.99  fd_pure                                 0
% 3.54/0.99  fd_pseudo                               0
% 3.54/0.99  fd_cond                                 0
% 3.54/0.99  fd_pseudo_cond                          6
% 3.54/0.99  AC symbols                              0
% 3.54/0.99  
% 3.54/0.99  ------ Schedule dynamic 5 is on 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  Current options:
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options
% 3.54/0.99  
% 3.54/0.99  --out_options                           all
% 3.54/0.99  --tptp_safe_out                         true
% 3.54/0.99  --problem_path                          ""
% 3.54/0.99  --include_path                          ""
% 3.54/0.99  --clausifier                            res/vclausify_rel
% 3.54/0.99  --clausifier_options                    ""
% 3.54/0.99  --stdin                                 false
% 3.54/0.99  --stats_out                             all
% 3.54/0.99  
% 3.54/0.99  ------ General Options
% 3.54/0.99  
% 3.54/0.99  --fof                                   false
% 3.54/0.99  --time_out_real                         305.
% 3.54/0.99  --time_out_virtual                      -1.
% 3.54/0.99  --symbol_type_check                     false
% 3.54/0.99  --clausify_out                          false
% 3.54/0.99  --sig_cnt_out                           false
% 3.54/0.99  --trig_cnt_out                          false
% 3.54/0.99  --trig_cnt_out_tolerance                1.
% 3.54/0.99  --trig_cnt_out_sk_spl                   false
% 3.54/0.99  --abstr_cl_out                          false
% 3.54/0.99  
% 3.54/0.99  ------ Global Options
% 3.54/0.99  
% 3.54/0.99  --schedule                              default
% 3.54/0.99  --add_important_lit                     false
% 3.54/0.99  --prop_solver_per_cl                    1000
% 3.54/0.99  --min_unsat_core                        false
% 3.54/0.99  --soft_assumptions                      false
% 3.54/0.99  --soft_lemma_size                       3
% 3.54/0.99  --prop_impl_unit_size                   0
% 3.54/0.99  --prop_impl_unit                        []
% 3.54/0.99  --share_sel_clauses                     true
% 3.54/0.99  --reset_solvers                         false
% 3.54/0.99  --bc_imp_inh                            [conj_cone]
% 3.54/0.99  --conj_cone_tolerance                   3.
% 3.54/0.99  --extra_neg_conj                        none
% 3.54/0.99  --large_theory_mode                     true
% 3.54/0.99  --prolific_symb_bound                   200
% 3.54/0.99  --lt_threshold                          2000
% 3.54/0.99  --clause_weak_htbl                      true
% 3.54/0.99  --gc_record_bc_elim                     false
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing Options
% 3.54/0.99  
% 3.54/0.99  --preprocessing_flag                    true
% 3.54/0.99  --time_out_prep_mult                    0.1
% 3.54/0.99  --splitting_mode                        input
% 3.54/0.99  --splitting_grd                         true
% 3.54/0.99  --splitting_cvd                         false
% 3.54/0.99  --splitting_cvd_svl                     false
% 3.54/0.99  --splitting_nvd                         32
% 3.54/0.99  --sub_typing                            true
% 3.54/0.99  --prep_gs_sim                           true
% 3.54/0.99  --prep_unflatten                        true
% 3.54/0.99  --prep_res_sim                          true
% 3.54/0.99  --prep_upred                            true
% 3.54/0.99  --prep_sem_filter                       exhaustive
% 3.54/0.99  --prep_sem_filter_out                   false
% 3.54/0.99  --pred_elim                             true
% 3.54/0.99  --res_sim_input                         true
% 3.54/0.99  --eq_ax_congr_red                       true
% 3.54/0.99  --pure_diseq_elim                       true
% 3.54/0.99  --brand_transform                       false
% 3.54/0.99  --non_eq_to_eq                          false
% 3.54/0.99  --prep_def_merge                        true
% 3.54/0.99  --prep_def_merge_prop_impl              false
% 3.54/0.99  --prep_def_merge_mbd                    true
% 3.54/0.99  --prep_def_merge_tr_red                 false
% 3.54/0.99  --prep_def_merge_tr_cl                  false
% 3.54/0.99  --smt_preprocessing                     true
% 3.54/0.99  --smt_ac_axioms                         fast
% 3.54/0.99  --preprocessed_out                      false
% 3.54/0.99  --preprocessed_stats                    false
% 3.54/0.99  
% 3.54/0.99  ------ Abstraction refinement Options
% 3.54/0.99  
% 3.54/0.99  --abstr_ref                             []
% 3.54/0.99  --abstr_ref_prep                        false
% 3.54/0.99  --abstr_ref_until_sat                   false
% 3.54/0.99  --abstr_ref_sig_restrict                funpre
% 3.54/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.99  --abstr_ref_under                       []
% 3.54/0.99  
% 3.54/0.99  ------ SAT Options
% 3.54/0.99  
% 3.54/0.99  --sat_mode                              false
% 3.54/0.99  --sat_fm_restart_options                ""
% 3.54/0.99  --sat_gr_def                            false
% 3.54/0.99  --sat_epr_types                         true
% 3.54/0.99  --sat_non_cyclic_types                  false
% 3.54/0.99  --sat_finite_models                     false
% 3.54/0.99  --sat_fm_lemmas                         false
% 3.54/0.99  --sat_fm_prep                           false
% 3.54/0.99  --sat_fm_uc_incr                        true
% 3.54/0.99  --sat_out_model                         small
% 3.54/0.99  --sat_out_clauses                       false
% 3.54/0.99  
% 3.54/0.99  ------ QBF Options
% 3.54/0.99  
% 3.54/0.99  --qbf_mode                              false
% 3.54/0.99  --qbf_elim_univ                         false
% 3.54/0.99  --qbf_dom_inst                          none
% 3.54/0.99  --qbf_dom_pre_inst                      false
% 3.54/0.99  --qbf_sk_in                             false
% 3.54/0.99  --qbf_pred_elim                         true
% 3.54/0.99  --qbf_split                             512
% 3.54/0.99  
% 3.54/0.99  ------ BMC1 Options
% 3.54/0.99  
% 3.54/0.99  --bmc1_incremental                      false
% 3.54/0.99  --bmc1_axioms                           reachable_all
% 3.54/0.99  --bmc1_min_bound                        0
% 3.54/0.99  --bmc1_max_bound                        -1
% 3.54/0.99  --bmc1_max_bound_default                -1
% 3.54/0.99  --bmc1_symbol_reachability              true
% 3.54/0.99  --bmc1_property_lemmas                  false
% 3.54/0.99  --bmc1_k_induction                      false
% 3.54/0.99  --bmc1_non_equiv_states                 false
% 3.54/0.99  --bmc1_deadlock                         false
% 3.54/0.99  --bmc1_ucm                              false
% 3.54/0.99  --bmc1_add_unsat_core                   none
% 3.54/0.99  --bmc1_unsat_core_children              false
% 3.54/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.99  --bmc1_out_stat                         full
% 3.54/0.99  --bmc1_ground_init                      false
% 3.54/0.99  --bmc1_pre_inst_next_state              false
% 3.54/0.99  --bmc1_pre_inst_state                   false
% 3.54/0.99  --bmc1_pre_inst_reach_state             false
% 3.54/0.99  --bmc1_out_unsat_core                   false
% 3.54/0.99  --bmc1_aig_witness_out                  false
% 3.54/0.99  --bmc1_verbose                          false
% 3.54/0.99  --bmc1_dump_clauses_tptp                false
% 3.54/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.99  --bmc1_dump_file                        -
% 3.54/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.99  --bmc1_ucm_extend_mode                  1
% 3.54/0.99  --bmc1_ucm_init_mode                    2
% 3.54/0.99  --bmc1_ucm_cone_mode                    none
% 3.54/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.99  --bmc1_ucm_relax_model                  4
% 3.54/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.99  --bmc1_ucm_layered_model                none
% 3.54/0.99  --bmc1_ucm_max_lemma_size               10
% 3.54/0.99  
% 3.54/0.99  ------ AIG Options
% 3.54/0.99  
% 3.54/0.99  --aig_mode                              false
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation Options
% 3.54/0.99  
% 3.54/0.99  --instantiation_flag                    true
% 3.54/0.99  --inst_sos_flag                         true
% 3.54/0.99  --inst_sos_phase                        true
% 3.54/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel_side                     none
% 3.54/0.99  --inst_solver_per_active                1400
% 3.54/0.99  --inst_solver_calls_frac                1.
% 3.54/0.99  --inst_passive_queue_type               priority_queues
% 3.54/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.99  --inst_passive_queues_freq              [25;2]
% 3.54/0.99  --inst_dismatching                      true
% 3.54/0.99  --inst_eager_unprocessed_to_passive     true
% 3.54/0.99  --inst_prop_sim_given                   true
% 3.54/0.99  --inst_prop_sim_new                     false
% 3.54/0.99  --inst_subs_new                         false
% 3.54/0.99  --inst_eq_res_simp                      false
% 3.54/0.99  --inst_subs_given                       false
% 3.54/0.99  --inst_orphan_elimination               true
% 3.54/0.99  --inst_learning_loop_flag               true
% 3.54/0.99  --inst_learning_start                   3000
% 3.54/0.99  --inst_learning_factor                  2
% 3.54/0.99  --inst_start_prop_sim_after_learn       3
% 3.54/0.99  --inst_sel_renew                        solver
% 3.54/0.99  --inst_lit_activity_flag                true
% 3.54/0.99  --inst_restr_to_given                   false
% 3.54/0.99  --inst_activity_threshold               500
% 3.54/0.99  --inst_out_proof                        true
% 3.54/0.99  
% 3.54/0.99  ------ Resolution Options
% 3.54/0.99  
% 3.54/0.99  --resolution_flag                       false
% 3.54/0.99  --res_lit_sel                           adaptive
% 3.54/0.99  --res_lit_sel_side                      none
% 3.54/0.99  --res_ordering                          kbo
% 3.54/0.99  --res_to_prop_solver                    active
% 3.54/0.99  --res_prop_simpl_new                    false
% 3.54/0.99  --res_prop_simpl_given                  true
% 3.54/0.99  --res_passive_queue_type                priority_queues
% 3.54/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.99  --res_passive_queues_freq               [15;5]
% 3.54/0.99  --res_forward_subs                      full
% 3.54/0.99  --res_backward_subs                     full
% 3.54/0.99  --res_forward_subs_resolution           true
% 3.54/0.99  --res_backward_subs_resolution          true
% 3.54/0.99  --res_orphan_elimination                true
% 3.54/0.99  --res_time_limit                        2.
% 3.54/0.99  --res_out_proof                         true
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Options
% 3.54/0.99  
% 3.54/0.99  --superposition_flag                    true
% 3.54/0.99  --sup_passive_queue_type                priority_queues
% 3.54/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.99  --demod_completeness_check              fast
% 3.54/0.99  --demod_use_ground                      true
% 3.54/0.99  --sup_to_prop_solver                    passive
% 3.54/0.99  --sup_prop_simpl_new                    true
% 3.54/0.99  --sup_prop_simpl_given                  true
% 3.54/0.99  --sup_fun_splitting                     true
% 3.54/0.99  --sup_smt_interval                      50000
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Simplification Setup
% 3.54/0.99  
% 3.54/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.54/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.54/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.54/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.54/0.99  --sup_immed_triv                        [TrivRules]
% 3.54/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_bw_main                     []
% 3.54/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.54/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_input_bw                          []
% 3.54/0.99  
% 3.54/0.99  ------ Combination Options
% 3.54/0.99  
% 3.54/0.99  --comb_res_mult                         3
% 3.54/0.99  --comb_sup_mult                         2
% 3.54/0.99  --comb_inst_mult                        10
% 3.54/0.99  
% 3.54/0.99  ------ Debug Options
% 3.54/0.99  
% 3.54/0.99  --dbg_backtrace                         false
% 3.54/0.99  --dbg_dump_prop_clauses                 false
% 3.54/0.99  --dbg_dump_prop_clauses_file            -
% 3.54/0.99  --dbg_out_stat                          false
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ Proving...
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS status Theorem for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  fof(f18,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f25,plain,(
% 3.54/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f18])).
% 3.54/0.99  
% 3.54/0.99  fof(f34,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.54/0.99    inference(nnf_transformation,[],[f25])).
% 3.54/0.99  
% 3.54/0.99  fof(f35,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.54/0.99    inference(flattening,[],[f34])).
% 3.54/0.99  
% 3.54/0.99  fof(f66,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f35])).
% 3.54/0.99  
% 3.54/0.99  fof(f10,axiom,(
% 3.54/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f53,plain,(
% 3.54/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f10])).
% 3.54/0.99  
% 3.54/0.99  fof(f11,axiom,(
% 3.54/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f54,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f11])).
% 3.54/0.99  
% 3.54/0.99  fof(f12,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f55,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f12])).
% 3.54/0.99  
% 3.54/0.99  fof(f13,axiom,(
% 3.54/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f56,plain,(
% 3.54/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f13])).
% 3.54/0.99  
% 3.54/0.99  fof(f14,axiom,(
% 3.54/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f57,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f14])).
% 3.54/0.99  
% 3.54/0.99  fof(f15,axiom,(
% 3.54/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f58,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f15])).
% 3.54/0.99  
% 3.54/0.99  fof(f16,axiom,(
% 3.54/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f59,plain,(
% 3.54/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f16])).
% 3.54/0.99  
% 3.54/0.99  fof(f74,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.54/0.99  
% 3.54/0.99  fof(f75,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f57,f74])).
% 3.54/0.99  
% 3.54/0.99  fof(f76,plain,(
% 3.54/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f56,f75])).
% 3.54/0.99  
% 3.54/0.99  fof(f77,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f55,f76])).
% 3.54/0.99  
% 3.54/0.99  fof(f78,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f54,f77])).
% 3.54/0.99  
% 3.54/0.99  fof(f79,plain,(
% 3.54/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f53,f78])).
% 3.54/0.99  
% 3.54/0.99  fof(f98,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.54/0.99    inference(definition_unfolding,[],[f66,f78,f79])).
% 3.54/0.99  
% 3.54/0.99  fof(f112,plain,(
% 3.54/0.99    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.54/0.99    inference(equality_resolution,[],[f98])).
% 3.54/0.99  
% 3.54/0.99  fof(f20,conjecture,(
% 3.54/0.99    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f21,negated_conjecture,(
% 3.54/0.99    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.54/0.99    inference(negated_conjecture,[],[f20])).
% 3.54/0.99  
% 3.54/0.99  fof(f26,plain,(
% 3.54/0.99    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.54/0.99    inference(ennf_transformation,[],[f21])).
% 3.54/0.99  
% 3.54/0.99  fof(f37,plain,(
% 3.54/0.99    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f38,plain,(
% 3.54/0.99    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f37])).
% 3.54/0.99  
% 3.54/0.99  fof(f71,plain,(
% 3.54/0.99    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.54/0.99    inference(cnf_transformation,[],[f38])).
% 3.54/0.99  
% 3.54/0.99  fof(f103,plain,(
% 3.54/0.99    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 3.54/0.99    inference(definition_unfolding,[],[f71,f78,f78])).
% 3.54/0.99  
% 3.54/0.99  fof(f64,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f35])).
% 3.54/0.99  
% 3.54/0.99  fof(f100,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f64,f78,f79,f79,f78])).
% 3.54/0.99  
% 3.54/0.99  fof(f72,plain,(
% 3.54/0.99    sK1 != sK3),
% 3.54/0.99    inference(cnf_transformation,[],[f38])).
% 3.54/0.99  
% 3.54/0.99  fof(f19,axiom,(
% 3.54/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f36,plain,(
% 3.54/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.54/0.99    inference(nnf_transformation,[],[f19])).
% 3.54/0.99  
% 3.54/0.99  fof(f69,plain,(
% 3.54/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f36])).
% 3.54/0.99  
% 3.54/0.99  fof(f102,plain,(
% 3.54/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f69,f79,f79,f79])).
% 3.54/0.99  
% 3.54/0.99  fof(f114,plain,(
% 3.54/0.99    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.54/0.99    inference(equality_resolution,[],[f102])).
% 3.54/0.99  
% 3.54/0.99  fof(f70,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.54/0.99    inference(cnf_transformation,[],[f36])).
% 3.54/0.99  
% 3.54/0.99  fof(f101,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.54/0.99    inference(definition_unfolding,[],[f70,f79,f79,f79])).
% 3.54/0.99  
% 3.54/0.99  fof(f9,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f27,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.99    inference(nnf_transformation,[],[f9])).
% 3.54/0.99  
% 3.54/0.99  fof(f28,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.99    inference(flattening,[],[f27])).
% 3.54/0.99  
% 3.54/0.99  fof(f29,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.99    inference(rectify,[],[f28])).
% 3.54/0.99  
% 3.54/0.99  fof(f30,plain,(
% 3.54/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f31,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.54/0.99  
% 3.54/0.99  fof(f48,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.54/0.99    inference(cnf_transformation,[],[f31])).
% 3.54/0.99  
% 3.54/0.99  fof(f90,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.54/0.99    inference(definition_unfolding,[],[f48,f78])).
% 3.54/0.99  
% 3.54/0.99  fof(f106,plain,(
% 3.54/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 3.54/0.99    inference(equality_resolution,[],[f90])).
% 3.54/0.99  
% 3.54/0.99  fof(f107,plain,(
% 3.54/0.99    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 3.54/0.99    inference(equality_resolution,[],[f106])).
% 3.54/0.99  
% 3.54/0.99  fof(f47,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.54/0.99    inference(cnf_transformation,[],[f31])).
% 3.54/0.99  
% 3.54/0.99  fof(f91,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.54/0.99    inference(definition_unfolding,[],[f47,f78])).
% 3.54/0.99  
% 3.54/0.99  fof(f108,plain,(
% 3.54/0.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.54/0.99    inference(equality_resolution,[],[f91])).
% 3.54/0.99  
% 3.54/0.99  fof(f2,axiom,(
% 3.54/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f22,plain,(
% 3.54/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.54/0.99    inference(rectify,[],[f2])).
% 3.54/0.99  
% 3.54/0.99  fof(f40,plain,(
% 3.54/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f22])).
% 3.54/0.99  
% 3.54/0.99  fof(f7,axiom,(
% 3.54/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f45,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f7])).
% 3.54/0.99  
% 3.54/0.99  fof(f82,plain,(
% 3.54/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.54/0.99    inference(definition_unfolding,[],[f40,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f3,axiom,(
% 3.54/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f41,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f3])).
% 3.54/0.99  
% 3.54/0.99  fof(f80,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f41,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f6,axiom,(
% 3.54/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f44,plain,(
% 3.54/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f6])).
% 3.54/0.99  
% 3.54/0.99  fof(f85,plain,(
% 3.54/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.54/0.99    inference(definition_unfolding,[],[f44,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f8,axiom,(
% 3.54/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f46,plain,(
% 3.54/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f8])).
% 3.54/0.99  
% 3.54/0.99  fof(f5,axiom,(
% 3.54/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f24,plain,(
% 3.54/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.54/0.99    inference(ennf_transformation,[],[f5])).
% 3.54/0.99  
% 3.54/0.99  fof(f43,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f24])).
% 3.54/0.99  
% 3.54/0.99  fof(f84,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f43,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f1,axiom,(
% 3.54/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f39,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f1])).
% 3.54/0.99  
% 3.54/0.99  fof(f81,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f39,f45,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f4,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f23,plain,(
% 3.54/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.54/0.99    inference(ennf_transformation,[],[f4])).
% 3.54/0.99  
% 3.54/0.99  fof(f42,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f23])).
% 3.54/0.99  
% 3.54/0.99  fof(f83,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f42,f45])).
% 3.54/0.99  
% 3.54/0.99  fof(f73,plain,(
% 3.54/0.99    sK1 != sK4),
% 3.54/0.99    inference(cnf_transformation,[],[f38])).
% 3.54/0.99  
% 3.54/0.99  fof(f17,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f32,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.54/0.99    inference(nnf_transformation,[],[f17])).
% 3.54/0.99  
% 3.54/0.99  fof(f33,plain,(
% 3.54/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.54/0.99    inference(flattening,[],[f32])).
% 3.54/0.99  
% 3.54/0.99  fof(f60,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f33])).
% 3.54/0.99  
% 3.54/0.99  fof(f95,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f60,f78,f79])).
% 3.54/0.99  
% 3.54/0.99  cnf(c_19,plain,
% 3.54/0.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_499,plain,
% 3.54/0.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_26,negated_conjecture,
% 3.54/0.99      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_496,plain,
% 3.54/0.99      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_21,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.54/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 3.54/0.99      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.54/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.54/0.99      | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_497,plain,
% 3.54/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.54/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 3.54/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 3.54/0.99      | k1_xboole_0 = X2
% 3.54/0.99      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1212,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_496,c_497]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2589,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.54/0.99      | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1212,c_499]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_25,negated_conjecture,
% 3.54/0.99      ( sK1 != sK3 ),
% 3.54/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_23,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_28,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_22,plain,
% 3.54/0.99      ( X0 = X1
% 3.54/0.99      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_29,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | sK1 = sK1 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11,plain,
% 3.54/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_55,plain,
% 3.54/0.99      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_12,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.54/0.99      | X0 = X1
% 3.54/0.99      | X0 = X2 ),
% 3.54/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_545,plain,
% 3.54/0.99      ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))
% 3.54/0.99      | sK1 = X0
% 3.54/0.99      | sK1 = sK3 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_626,plain,
% 3.54/0.99      ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.54/0.99      | sK1 = sK3 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_545]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_221,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.54/0.99      theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_802,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,X1)
% 3.54/0.99      | r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X1
% 3.54/0.99      | sK1 != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_221]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1159,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.54/0.99      | r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
% 3.54/0.99      | sK1 != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_802]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1161,plain,
% 3.54/0.99      ( r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.54/0.99      | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | sK1 != sK1 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_1159]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_0,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1026,plain,
% 3.54/0.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1027,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1032,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1027,c_6]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1029,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1030,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1029,c_5]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1033,plain,
% 3.54/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1032,c_1030]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1034,plain,
% 3.54/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1026,c_1033]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1325,plain,
% 3.54/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_23,c_1034]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1326,plain,
% 3.54/0.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_1325]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1374,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = X0
% 3.54/0.99      | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1212,c_497]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2593,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_499,c_1374]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3065,plain,
% 3.54/0.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2589,c_25,c_28,c_29,c_55,c_626,c_1161,c_1326,c_2593]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3066,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_3065]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3070,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = X0
% 3.54/0.99      | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_3066,c_497]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1113,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 3.54/0.99      | k1_xboole_0 = X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1114,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 3.54/0.99      | k1_xboole_0 = X0
% 3.54/0.99      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_512,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.54/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2034,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_496,c_512]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2145,plain,
% 3.54/0.99      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2034,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2149,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2145,c_1033]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3,plain,
% 3.54/0.99      ( r1_tarski(X0,X1)
% 3.54/0.99      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.54/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_513,plain,
% 3.54/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.54/0.99      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2733,plain,
% 3.54/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.54/0.99      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1,c_513]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2800,plain,
% 3.54/0.99      ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top
% 3.54/0.99      | r1_tarski(X0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2149,c_2733]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2801,plain,
% 3.54/0.99      ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top
% 3.54/0.99      | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2800,c_1032]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3862,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.54/0.99      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 3.54/0.99      | k1_xboole_0 = X0
% 3.54/0.99      | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_3070,c_1114,c_2801]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3868,plain,
% 3.54/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.54/0.99      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_499,c_3862]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_24,negated_conjecture,
% 3.54/0.99      ( sK1 != sK4 ),
% 3.54/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_534,plain,
% 3.54/0.99      ( ~ r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))
% 3.54/0.99      | sK1 = X0
% 3.54/0.99      | sK1 = sK4 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_565,plain,
% 3.54/0.99      ( ~ r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.54/0.99      | sK1 = sK4 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_534]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_613,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,X1)
% 3.54/0.99      | r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1
% 3.54/0.99      | sK1 != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_221]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_936,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.54/0.99      | r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
% 3.54/0.99      | sK1 != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_613]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_938,plain,
% 3.54/0.99      ( r2_hidden(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.54/0.99      | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.54/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.54/0.99      | sK1 != sK1 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_936]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5059,plain,
% 3.54/0.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_3868,c_25,c_24,c_28,c_29,c_55,c_565,c_626,c_938,
% 3.54/0.99                 c_1161,c_1326]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_507,plain,
% 3.54/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5074,plain,
% 3.54/0.99      ( r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_5059,c_507]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_16,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,X1)
% 3.54/0.99      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_562,plain,
% 3.54/0.99      ( ~ r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.54/0.99      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_563,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.54/0.99      | r2_hidden(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_544,plain,
% 3.54/0.99      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.54/0.99      | sK1 = sK3 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,[status(thm)],[c_5074,c_563,c_544,c_25]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ General
% 3.54/0.99  
% 3.54/0.99  abstr_ref_over_cycles:                  0
% 3.54/0.99  abstr_ref_under_cycles:                 0
% 3.54/0.99  gc_basic_clause_elim:                   0
% 3.54/0.99  forced_gc_time:                         0
% 3.54/0.99  parsing_time:                           0.008
% 3.54/0.99  unif_index_cands_time:                  0.
% 3.54/0.99  unif_index_add_time:                    0.
% 3.54/0.99  orderings_time:                         0.
% 3.54/0.99  out_proof_time:                         0.01
% 3.54/0.99  total_time:                             0.251
% 3.54/0.99  num_of_symbols:                         42
% 3.54/0.99  num_of_terms:                           7067
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing
% 3.54/0.99  
% 3.54/0.99  num_of_splits:                          0
% 3.54/0.99  num_of_split_atoms:                     0
% 3.54/0.99  num_of_reused_defs:                     0
% 3.54/0.99  num_eq_ax_congr_red:                    8
% 3.54/0.99  num_of_sem_filtered_clauses:            1
% 3.54/0.99  num_of_subtypes:                        0
% 3.54/0.99  monotx_restored_types:                  0
% 3.54/0.99  sat_num_of_epr_types:                   0
% 3.54/0.99  sat_num_of_non_cyclic_types:            0
% 3.54/0.99  sat_guarded_non_collapsed_types:        0
% 3.54/0.99  num_pure_diseq_elim:                    0
% 3.54/0.99  simp_replaced_by:                       0
% 3.54/0.99  res_preprocessed:                       96
% 3.54/0.99  prep_upred:                             0
% 3.54/0.99  prep_unflattend:                        0
% 3.54/0.99  smt_new_axioms:                         0
% 3.54/0.99  pred_elim_cands:                        2
% 3.54/0.99  pred_elim:                              0
% 3.54/0.99  pred_elim_cl:                           0
% 3.54/0.99  pred_elim_cycles:                       1
% 3.54/0.99  merged_defs:                            0
% 3.54/0.99  merged_defs_ncl:                        0
% 3.54/0.99  bin_hyper_res:                          0
% 3.54/0.99  prep_cycles:                            3
% 3.54/0.99  pred_elim_time:                         0.
% 3.54/0.99  splitting_time:                         0.
% 3.54/0.99  sem_filter_time:                        0.
% 3.54/0.99  monotx_time:                            0.
% 3.54/0.99  subtype_inf_time:                       0.
% 3.54/0.99  
% 3.54/0.99  ------ Problem properties
% 3.54/0.99  
% 3.54/0.99  clauses:                                27
% 3.54/0.99  conjectures:                            3
% 3.54/0.99  epr:                                    2
% 3.54/0.99  horn:                                   20
% 3.54/0.99  ground:                                 3
% 3.54/0.99  unary:                                  15
% 3.54/0.99  binary:                                 5
% 3.54/0.99  lits:                                   49
% 3.54/0.99  lits_eq:                                29
% 3.54/0.99  fd_pure:                                0
% 3.54/0.99  fd_pseudo:                              0
% 3.54/0.99  fd_cond:                                0
% 3.54/0.99  fd_pseudo_cond:                         6
% 3.54/0.99  ac_symbols:                             0
% 3.54/0.99  
% 3.54/0.99  ------ Propositional Solver
% 3.54/0.99  
% 3.54/0.99  prop_solver_calls:                      24
% 3.54/0.99  prop_fast_solver_calls:                 579
% 3.54/0.99  smt_solver_calls:                       0
% 3.54/0.99  smt_fast_solver_calls:                  0
% 3.54/0.99  prop_num_of_clauses:                    2081
% 3.54/0.99  prop_preprocess_simplified:             5771
% 3.54/0.99  prop_fo_subsumed:                       12
% 3.54/0.99  prop_solver_time:                       0.
% 3.54/0.99  smt_solver_time:                        0.
% 3.54/0.99  smt_fast_solver_time:                   0.
% 3.54/0.99  prop_fast_solver_time:                  0.
% 3.54/0.99  prop_unsat_core_time:                   0.
% 3.54/0.99  
% 3.54/0.99  ------ QBF
% 3.54/0.99  
% 3.54/0.99  qbf_q_res:                              0
% 3.54/0.99  qbf_num_tautologies:                    0
% 3.54/0.99  qbf_prep_cycles:                        0
% 3.54/0.99  
% 3.54/0.99  ------ BMC1
% 3.54/0.99  
% 3.54/0.99  bmc1_current_bound:                     -1
% 3.54/0.99  bmc1_last_solved_bound:                 -1
% 3.54/0.99  bmc1_unsat_core_size:                   -1
% 3.54/0.99  bmc1_unsat_core_parents_size:           -1
% 3.54/0.99  bmc1_merge_next_fun:                    0
% 3.54/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation
% 3.54/0.99  
% 3.54/0.99  inst_num_of_clauses:                    618
% 3.54/0.99  inst_num_in_passive:                    205
% 3.54/0.99  inst_num_in_active:                     248
% 3.54/0.99  inst_num_in_unprocessed:                165
% 3.54/0.99  inst_num_of_loops:                      300
% 3.54/0.99  inst_num_of_learning_restarts:          0
% 3.54/0.99  inst_num_moves_active_passive:          49
% 3.54/0.99  inst_lit_activity:                      0
% 3.54/0.99  inst_lit_activity_moves:                0
% 3.54/0.99  inst_num_tautologies:                   0
% 3.54/0.99  inst_num_prop_implied:                  0
% 3.54/0.99  inst_num_existing_simplified:           0
% 3.54/0.99  inst_num_eq_res_simplified:             0
% 3.54/0.99  inst_num_child_elim:                    0
% 3.54/0.99  inst_num_of_dismatching_blockings:      354
% 3.54/0.99  inst_num_of_non_proper_insts:           844
% 3.54/0.99  inst_num_of_duplicates:                 0
% 3.54/0.99  inst_inst_num_from_inst_to_res:         0
% 3.54/0.99  inst_dismatching_checking_time:         0.
% 3.54/0.99  
% 3.54/0.99  ------ Resolution
% 3.54/0.99  
% 3.54/0.99  res_num_of_clauses:                     0
% 3.54/0.99  res_num_in_passive:                     0
% 3.54/0.99  res_num_in_active:                      0
% 3.54/0.99  res_num_of_loops:                       99
% 3.54/0.99  res_forward_subset_subsumed:            151
% 3.54/0.99  res_backward_subset_subsumed:           12
% 3.54/0.99  res_forward_subsumed:                   0
% 3.54/0.99  res_backward_subsumed:                  0
% 3.54/0.99  res_forward_subsumption_resolution:     0
% 3.54/0.99  res_backward_subsumption_resolution:    0
% 3.54/0.99  res_clause_to_clause_subsumption:       739
% 3.54/0.99  res_orphan_elimination:                 0
% 3.54/0.99  res_tautology_del:                      103
% 3.54/0.99  res_num_eq_res_simplified:              0
% 3.54/0.99  res_num_sel_changes:                    0
% 3.54/0.99  res_moves_from_active_to_pass:          0
% 3.54/0.99  
% 3.54/0.99  ------ Superposition
% 3.54/0.99  
% 3.54/0.99  sup_time_total:                         0.
% 3.54/0.99  sup_time_generating:                    0.
% 3.54/0.99  sup_time_sim_full:                      0.
% 3.54/0.99  sup_time_sim_immed:                     0.
% 3.54/0.99  
% 3.54/0.99  sup_num_of_clauses:                     100
% 3.54/0.99  sup_num_in_active:                      34
% 3.54/0.99  sup_num_in_passive:                     66
% 3.54/0.99  sup_num_of_loops:                       59
% 3.54/0.99  sup_fw_superposition:                   297
% 3.54/0.99  sup_bw_superposition:                   144
% 3.54/0.99  sup_immediate_simplified:               212
% 3.54/0.99  sup_given_eliminated:                   1
% 3.54/0.99  comparisons_done:                       0
% 3.54/0.99  comparisons_avoided:                    47
% 3.54/0.99  
% 3.54/0.99  ------ Simplifications
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  sim_fw_subset_subsumed:                 1
% 3.54/0.99  sim_bw_subset_subsumed:                 59
% 3.54/0.99  sim_fw_subsumed:                        21
% 3.54/0.99  sim_bw_subsumed:                        7
% 3.54/0.99  sim_fw_subsumption_res:                 0
% 3.54/0.99  sim_bw_subsumption_res:                 0
% 3.54/0.99  sim_tautology_del:                      32
% 3.54/0.99  sim_eq_tautology_del:                   93
% 3.54/0.99  sim_eq_res_simp:                        0
% 3.54/0.99  sim_fw_demodulated:                     171
% 3.54/0.99  sim_bw_demodulated:                     13
% 3.54/0.99  sim_light_normalised:                   66
% 3.54/0.99  sim_joinable_taut:                      0
% 3.54/0.99  sim_joinable_simp:                      0
% 3.54/0.99  sim_ac_normalised:                      0
% 3.54/0.99  sim_smt_subsumption:                    0
% 3.54/0.99  
%------------------------------------------------------------------------------
