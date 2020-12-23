%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:27 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  121 (1711 expanded)
%              Number of clauses        :   49 ( 154 expanded)
%              Number of leaves         :   19 ( 500 expanded)
%              Depth                    :   23
%              Number of atoms          :  377 (5059 expanded)
%              Number of equality atoms :  300 (4155 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f36])).

fof(f70,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f102,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f70,f77,f77])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f65,f77,f78,f78,f77])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f71,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f107,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f108,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f107])).

fof(f72,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f103,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f104,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f103])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f105,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f106,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f61,f77,f78])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_579,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_580,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1185,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_579,c_580])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_589,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9660,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_589])).

cnf(c_25,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_50,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_53,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_230,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_763,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_764,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1163,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3195,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_3196,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3195])).

cnf(c_9730,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1
    | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9660])).

cnf(c_10052,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9660,c_25,c_50,c_53,c_764,c_3196,c_9730])).

cnf(c_10065,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_580])).

cnf(c_24,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_761,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_762,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_592,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10058,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | r2_hidden(sK4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_592])).

cnf(c_10060,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10052,c_589])).

cnf(c_10150,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1
    | sK4 = sK1
    | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10060])).

cnf(c_10161,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10058,c_25,c_24,c_50,c_53,c_762,c_764,c_3196,c_10150])).

cnf(c_10162,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10161])).

cnf(c_10168,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10162,c_589])).

cnf(c_10214,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK4 = sK1
    | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10168])).

cnf(c_11498,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10065,c_24,c_50,c_53,c_762,c_3196,c_10214])).

cnf(c_12,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_591,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11517,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11498,c_591])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_969,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_979,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_969,c_6])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_585,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11268,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_585])).

cnf(c_11304,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11268])).

cnf(c_234,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_239,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11517,c_11304,c_239,c_53,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.62/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.00  
% 3.62/1.00  ------  iProver source info
% 3.62/1.00  
% 3.62/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.00  git: non_committed_changes: false
% 3.62/1.00  git: last_make_outside_of_git: false
% 3.62/1.00  
% 3.62/1.00  ------ 
% 3.62/1.00  ------ Parsing...
% 3.62/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.00  ------ Proving...
% 3.62/1.00  ------ Problem Properties 
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  clauses                                 27
% 3.62/1.00  conjectures                             3
% 3.62/1.00  EPR                                     2
% 3.62/1.00  Horn                                    21
% 3.62/1.00  unary                                   15
% 3.62/1.00  binary                                  4
% 3.62/1.00  lits                                    52
% 3.62/1.00  lits eq                                 30
% 3.62/1.00  fd_pure                                 0
% 3.62/1.00  fd_pseudo                               0
% 3.62/1.00  fd_cond                                 0
% 3.62/1.00  fd_pseudo_cond                          6
% 3.62/1.00  AC symbols                              0
% 3.62/1.00  
% 3.62/1.00  ------ Input Options Time Limit: Unbounded
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  ------ 
% 3.62/1.00  Current options:
% 3.62/1.00  ------ 
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  ------ Proving...
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  % SZS status Theorem for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  fof(f19,conjecture,(
% 3.62/1.00    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f20,negated_conjecture,(
% 3.62/1.00    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.62/1.00    inference(negated_conjecture,[],[f19])).
% 3.62/1.00  
% 3.62/1.00  fof(f26,plain,(
% 3.62/1.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.62/1.00    inference(ennf_transformation,[],[f20])).
% 3.62/1.00  
% 3.62/1.00  fof(f36,plain,(
% 3.62/1.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 3.62/1.00    introduced(choice_axiom,[])).
% 3.62/1.00  
% 3.62/1.00  fof(f37,plain,(
% 3.62/1.00    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f36])).
% 3.62/1.00  
% 3.62/1.00  fof(f70,plain,(
% 3.62/1.00    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.62/1.00    inference(cnf_transformation,[],[f37])).
% 3.62/1.00  
% 3.62/1.00  fof(f11,axiom,(
% 3.62/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f55,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f11])).
% 3.62/1.00  
% 3.62/1.00  fof(f12,axiom,(
% 3.62/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f56,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f12])).
% 3.62/1.00  
% 3.62/1.00  fof(f13,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f57,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f13])).
% 3.62/1.00  
% 3.62/1.00  fof(f14,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f58,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f14])).
% 3.62/1.00  
% 3.62/1.00  fof(f15,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f59,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f15])).
% 3.62/1.00  
% 3.62/1.00  fof(f16,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f60,plain,(
% 3.62/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f16])).
% 3.62/1.00  
% 3.62/1.00  fof(f73,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f59,f60])).
% 3.62/1.00  
% 3.62/1.00  fof(f74,plain,(
% 3.62/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f58,f73])).
% 3.62/1.00  
% 3.62/1.00  fof(f75,plain,(
% 3.62/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f57,f74])).
% 3.62/1.00  
% 3.62/1.00  fof(f76,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f56,f75])).
% 3.62/1.00  
% 3.62/1.00  fof(f77,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f55,f76])).
% 3.62/1.00  
% 3.62/1.00  fof(f102,plain,(
% 3.62/1.00    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 3.62/1.00    inference(definition_unfolding,[],[f70,f77,f77])).
% 3.62/1.00  
% 3.62/1.00  fof(f18,axiom,(
% 3.62/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f25,plain,(
% 3.62/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.62/1.00    inference(ennf_transformation,[],[f18])).
% 3.62/1.00  
% 3.62/1.00  fof(f34,plain,(
% 3.62/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.62/1.00    inference(nnf_transformation,[],[f25])).
% 3.62/1.00  
% 3.62/1.00  fof(f35,plain,(
% 3.62/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.62/1.00    inference(flattening,[],[f34])).
% 3.62/1.00  
% 3.62/1.00  fof(f65,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.62/1.00    inference(cnf_transformation,[],[f35])).
% 3.62/1.00  
% 3.62/1.00  fof(f10,axiom,(
% 3.62/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f54,plain,(
% 3.62/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f10])).
% 3.62/1.00  
% 3.62/1.00  fof(f78,plain,(
% 3.62/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f54,f77])).
% 3.62/1.00  
% 3.62/1.00  fof(f101,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.62/1.00    inference(definition_unfolding,[],[f65,f77,f78,f78,f77])).
% 3.62/1.00  
% 3.62/1.00  fof(f9,axiom,(
% 3.62/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f24,plain,(
% 3.62/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.62/1.00    inference(ennf_transformation,[],[f9])).
% 3.62/1.00  
% 3.62/1.00  fof(f27,plain,(
% 3.62/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.62/1.00    inference(nnf_transformation,[],[f24])).
% 3.62/1.00  
% 3.62/1.00  fof(f28,plain,(
% 3.62/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.62/1.00    inference(flattening,[],[f27])).
% 3.62/1.00  
% 3.62/1.00  fof(f29,plain,(
% 3.62/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.62/1.00    inference(rectify,[],[f28])).
% 3.62/1.00  
% 3.62/1.00  fof(f30,plain,(
% 3.62/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.62/1.00    introduced(choice_axiom,[])).
% 3.62/1.00  
% 3.62/1.00  fof(f31,plain,(
% 3.62/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.62/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.62/1.00  
% 3.62/1.00  fof(f46,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.62/1.00    inference(cnf_transformation,[],[f31])).
% 3.62/1.00  
% 3.62/1.00  fof(f92,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.62/1.00    inference(definition_unfolding,[],[f46,f76])).
% 3.62/1.00  
% 3.62/1.00  fof(f109,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.62/1.00    inference(equality_resolution,[],[f92])).
% 3.62/1.00  
% 3.62/1.00  fof(f71,plain,(
% 3.62/1.00    sK1 != sK3),
% 3.62/1.00    inference(cnf_transformation,[],[f37])).
% 3.62/1.00  
% 3.62/1.00  fof(f47,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.62/1.00    inference(cnf_transformation,[],[f31])).
% 3.62/1.00  
% 3.62/1.00  fof(f91,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.62/1.00    inference(definition_unfolding,[],[f47,f76])).
% 3.62/1.00  
% 3.62/1.00  fof(f107,plain,(
% 3.62/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.62/1.00    inference(equality_resolution,[],[f91])).
% 3.62/1.00  
% 3.62/1.00  fof(f108,plain,(
% 3.62/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.62/1.00    inference(equality_resolution,[],[f107])).
% 3.62/1.00  
% 3.62/1.00  fof(f72,plain,(
% 3.62/1.00    sK1 != sK4),
% 3.62/1.00    inference(cnf_transformation,[],[f37])).
% 3.62/1.00  
% 3.62/1.00  fof(f49,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.62/1.00    inference(cnf_transformation,[],[f31])).
% 3.62/1.00  
% 3.62/1.00  fof(f89,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.62/1.00    inference(definition_unfolding,[],[f49,f76])).
% 3.62/1.00  
% 3.62/1.00  fof(f103,plain,(
% 3.62/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.62/1.00    inference(equality_resolution,[],[f89])).
% 3.62/1.00  
% 3.62/1.00  fof(f104,plain,(
% 3.62/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 3.62/1.00    inference(equality_resolution,[],[f103])).
% 3.62/1.00  
% 3.62/1.00  fof(f48,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.62/1.00    inference(cnf_transformation,[],[f31])).
% 3.62/1.00  
% 3.62/1.00  fof(f90,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.62/1.00    inference(definition_unfolding,[],[f48,f76])).
% 3.62/1.00  
% 3.62/1.00  fof(f105,plain,(
% 3.62/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 3.62/1.00    inference(equality_resolution,[],[f90])).
% 3.62/1.00  
% 3.62/1.00  fof(f106,plain,(
% 3.62/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 3.62/1.00    inference(equality_resolution,[],[f105])).
% 3.62/1.00  
% 3.62/1.00  fof(f6,axiom,(
% 3.62/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f43,plain,(
% 3.62/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.62/1.00    inference(cnf_transformation,[],[f6])).
% 3.62/1.00  
% 3.62/1.00  fof(f7,axiom,(
% 3.62/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f44,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.62/1.00    inference(cnf_transformation,[],[f7])).
% 3.62/1.00  
% 3.62/1.00  fof(f84,plain,(
% 3.62/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.62/1.00    inference(definition_unfolding,[],[f43,f44])).
% 3.62/1.00  
% 3.62/1.00  fof(f3,axiom,(
% 3.62/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f40,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/1.00    inference(cnf_transformation,[],[f3])).
% 3.62/1.00  
% 3.62/1.00  fof(f79,plain,(
% 3.62/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.62/1.00    inference(definition_unfolding,[],[f40,f44])).
% 3.62/1.00  
% 3.62/1.00  fof(f8,axiom,(
% 3.62/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f45,plain,(
% 3.62/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/1.00    inference(cnf_transformation,[],[f8])).
% 3.62/1.00  
% 3.62/1.00  fof(f17,axiom,(
% 3.62/1.00    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f32,plain,(
% 3.62/1.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.62/1.00    inference(nnf_transformation,[],[f17])).
% 3.62/1.00  
% 3.62/1.00  fof(f33,plain,(
% 3.62/1.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.62/1.00    inference(flattening,[],[f32])).
% 3.62/1.00  
% 3.62/1.00  fof(f61,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f33])).
% 3.62/1.00  
% 3.62/1.00  fof(f96,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.62/1.00    inference(definition_unfolding,[],[f61,f77,f78])).
% 3.62/1.00  
% 3.62/1.00  cnf(c_26,negated_conjecture,
% 3.62/1.00      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_579,plain,
% 3.62/1.00      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_23,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.62/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 3.62/1.00      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.62/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.62/1.00      | k1_xboole_0 = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_580,plain,
% 3.62/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.62/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 3.62/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 3.62/1.00      | k1_xboole_0 = X2
% 3.62/1.00      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1185,plain,
% 3.62/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_579,c_580]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_14,plain,
% 3.62/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 3.62/1.00      | X0 = X1
% 3.62/1.00      | X0 = X2
% 3.62/1.00      | X0 = X3 ),
% 3.62/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_589,plain,
% 3.62/1.00      ( X0 = X1
% 3.62/1.00      | X0 = X2
% 3.62/1.00      | X0 = X3
% 3.62/1.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_9660,plain,
% 3.62/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK3 = X0
% 3.62/1.00      | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1185,c_589]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_25,negated_conjecture,
% 3.62/1.00      ( sK1 != sK3 ),
% 3.62/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_50,plain,
% 3.62/1.00      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.62/1.00      | sK1 = sK1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_13,plain,
% 3.62/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_53,plain,
% 3.62/1.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_230,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_763,plain,
% 3.62/1.00      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_230]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_764,plain,
% 3.62/1.00      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_763]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1163,plain,
% 3.62/1.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0,X1)) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3195,plain,
% 3.62/1.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1163]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3196,plain,
% 3.62/1.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_3195]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_9730,plain,
% 3.62/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK3 = sK1
% 3.62/1.00      | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_9660]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10052,plain,
% 3.62/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_9660,c_25,c_50,c_53,c_764,c_3196,c_9730]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10065,plain,
% 3.62/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 3.62/1.00      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = X0
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = X0
% 3.62/1.00      | r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_10052,c_580]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_24,negated_conjecture,
% 3.62/1.00      ( sK1 != sK4 ),
% 3.62/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_761,plain,
% 3.62/1.00      ( sK4 != X0 | sK1 != X0 | sK1 = sK4 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_230]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_762,plain,
% 3.62/1.00      ( sK4 != sK1 | sK1 = sK4 | sK1 != sK1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_761]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_11,plain,
% 3.62/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_592,plain,
% 3.62/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10058,plain,
% 3.62/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | r2_hidden(sK4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_10052,c_592]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10060,plain,
% 3.62/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK3 = X0
% 3.62/1.00      | sK4 = X0
% 3.62/1.00      | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_10052,c_589]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10150,plain,
% 3.62/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK3 = sK1
% 3.62/1.00      | sK4 = sK1
% 3.62/1.00      | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_10060]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10161,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_10058,c_25,c_24,c_50,c_53,c_762,c_764,c_3196,c_10150]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10162,plain,
% 3.62/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 3.62/1.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.62/1.00      inference(renaming,[status(thm)],[c_10161]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10168,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK4 = X0
% 3.62/1.00      | r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_10162,c_589]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10214,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 3.62/1.00      | sK4 = sK1
% 3.62/1.00      | r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_10168]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_11498,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_10065,c_24,c_50,c_53,c_762,c_3196,c_10214]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_12,plain,
% 3.62/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_591,plain,
% 3.62/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_11517,plain,
% 3.62/1.00      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_11498,c_591]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5,plain,
% 3.62/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_0,plain,
% 3.62/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_969,plain,
% 3.62/1.00      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_6,plain,
% 3.62/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_979,plain,
% 3.62/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.62/1.00      inference(light_normalisation,[status(thm)],[c_969,c_6]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_18,plain,
% 3.62/1.00      ( ~ r2_hidden(X0,X1)
% 3.62/1.00      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_585,plain,
% 3.62/1.00      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.62/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_11268,plain,
% 3.62/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.62/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_979,c_585]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_11304,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.62/1.00      | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_11268]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_234,plain,
% 3.62/1.00      ( X0 != X1
% 3.62/1.00      | X2 != X3
% 3.62/1.00      | X4 != X5
% 3.62/1.00      | X6 != X7
% 3.62/1.00      | X8 != X9
% 3.62/1.00      | X10 != X11
% 3.62/1.00      | X12 != X13
% 3.62/1.00      | X14 != X15
% 3.62/1.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.62/1.00      theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_239,plain,
% 3.62/1.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.62/1.00      | sK1 != sK1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_234]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(contradiction,plain,
% 3.62/1.00      ( $false ),
% 3.62/1.00      inference(minisat,[status(thm)],[c_11517,c_11304,c_239,c_53,c_50]) ).
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  ------                               Statistics
% 3.62/1.00  
% 3.62/1.00  ------ Selected
% 3.62/1.00  
% 3.62/1.00  total_time:                             0.503
% 3.62/1.00  
%------------------------------------------------------------------------------
