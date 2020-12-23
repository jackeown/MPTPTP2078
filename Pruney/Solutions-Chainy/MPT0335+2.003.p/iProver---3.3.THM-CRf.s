%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:25 EST 2020

% Result     : Theorem 27.50s
% Output     : CNFRefutation 27.50s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 575 expanded)
%              Number of clauses        :   74 ( 132 expanded)
%              Number of leaves         :   20 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  545 (2097 expanded)
%              Number of equality atoms :  233 (1026 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) = X1
      | sK3(X0,X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK3(X0,X1,X2) = X1
      | sK3(X0,X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK4,sK6) != k1_tarski(sK7)
      & r2_hidden(sK7,sK4)
      & k3_xboole_0(sK5,sK6) = k1_tarski(sK7)
      & r1_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k3_xboole_0(sK4,sK6) != k1_tarski(sK7)
    & r2_hidden(sK7,sK4)
    & k3_xboole_0(sK5,sK6) = k1_tarski(sK7)
    & r1_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f37])).

fof(f67,plain,(
    k3_xboole_0(sK5,sK6) = k1_tarski(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f83,plain,(
    k3_xboole_0(sK5,sK6) = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f66,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    k3_xboole_0(sK4,sK6) != k1_tarski(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    k3_xboole_0(sK4,sK6) != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f94,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f95,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f94])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f91,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f92,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f93,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f92])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    r2_hidden(sK7,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

cnf(c_20,plain,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK3(X0,X1,X2) = X1
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6338,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k2_enumset1(X3,X3,X3,X4))
    | r2_hidden(sK3(X3,X4,X1),X1)
    | X2 != X0
    | sK3(X3,X4,X1) = X4
    | sK3(X3,X4,X1) = X3 ),
    inference(resolution,[status(thm)],[c_20,c_426])).

cnf(c_423,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_422,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2120,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_423,c_422])).

cnf(c_26,negated_conjecture,
    ( k3_xboole_0(sK5,sK6) = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6885,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k3_xboole_0(sK5,sK6) ),
    inference(resolution,[status(thm)],[c_2120,c_26])).

cnf(c_46756,plain,
    ( r2_hidden(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ r2_hidden(k3_xboole_0(sK5,sK6),X2)
    | sK3(X0,X1,X2) = X1
    | sK3(X0,X1,X2) = X0 ),
    inference(resolution,[status(thm)],[c_6338,c_6885])).

cnf(c_2322,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(X1,k3_xboole_0(sK5,sK6))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_426,c_26])).

cnf(c_79015,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,sK6))
    | r2_hidden(sK3(sK7,sK7,X1),X1)
    | ~ r2_hidden(k3_xboole_0(sK5,sK6),X1)
    | X0 != k2_enumset1(sK7,sK7,sK7,sK7)
    | sK3(sK7,sK7,X1) = sK7 ),
    inference(resolution,[status(thm)],[c_46756,c_2322])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( k3_xboole_0(sK4,sK6) != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_34,plain,
    ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_427,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_430,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k2_enumset1(sK7,sK7,sK7,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1017,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
    | k3_xboole_0(sK4,sK6) = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1281,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2028,plain,
    ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2446,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_425,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2300,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | r1_tarski(X1,k3_xboole_0(sK5,sK6))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_425,c_26])).

cnf(c_2614,plain,
    ( r1_tarski(X0,k3_xboole_0(sK5,sK6))
    | X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_2300,c_12])).

cnf(c_2890,plain,
    ( r1_tarski(k3_xboole_0(sK5,sK6),k3_xboole_0(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_2614,c_26])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1458,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2674,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_3207,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK5)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2370,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
    inference(resolution,[status(thm)],[c_5,c_24])).

cnf(c_2643,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6)
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK7 ),
    inference(resolution,[status(thm)],[c_2370,c_17])).

cnf(c_21,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2632,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,sK6))
    | X0 != sK7 ),
    inference(resolution,[status(thm)],[c_2322,c_21])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2868,plain,
    ( r2_hidden(X0,sK6)
    | X0 != sK7 ),
    inference(resolution,[status(thm)],[c_2632,c_8])).

cnf(c_3284,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2643,c_2868])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3716,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK7,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_985,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK4)
    | X0 != sK7
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_1152,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
    | ~ r2_hidden(sK7,sK4)
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK7
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_1394,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_1757,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4102,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3716,c_25,c_1152,c_1394,c_1757])).

cnf(c_2304,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_425,c_422])).

cnf(c_8439,plain,
    ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
    | ~ r1_tarski(k3_xboole_0(sK5,sK6),X0) ),
    inference(resolution,[status(thm)],[c_2304,c_6885])).

cnf(c_6906,plain,
    ( r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(X1,k3_xboole_0(sK5,sK6))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6885,c_425])).

cnf(c_9550,plain,
    ( r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(k3_xboole_0(sK5,sK6),k3_xboole_0(sK5,sK6))
    | X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_8439,c_6906])).

cnf(c_10090,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2114,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_423,c_10])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2113,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_423,c_0])).

cnf(c_10730,plain,
    ( k3_xboole_0(sK6,sK5) = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_2113,c_6885])).

cnf(c_13979,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
    | X0 = k3_xboole_0(sK6,sK5) ),
    inference(resolution,[status(thm)],[c_2114,c_10730])).

cnf(c_1262,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X2)
    | X2 != X1
    | k2_enumset1(sK7,sK7,sK7,sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_5495,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X1,X2,X3),X4)
    | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X5)
    | X5 != X4
    | k2_enumset1(sK7,sK7,sK7,sK7) != k2_enumset1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_26383,plain,
    ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
    | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7))
    | X0 != k2_enumset1(sK7,sK7,sK7,sK7)
    | k2_enumset1(sK7,sK7,sK7,sK7) != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5495])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1471,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2712,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,X0))
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_52973,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,sK5))
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK5)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
    inference(instantiation,[status(thm)],[c_2712])).

cnf(c_1496,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X2)
    | X2 != X1
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_13610,plain,
    ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
    | X1 != X0
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_61793,plain,
    ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
    | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,sK5))
    | X0 != k3_xboole_0(sK6,sK5)
    | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_13610])).

cnf(c_79022,plain,
    ( X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79015,c_27,c_25,c_24,c_31,c_34,c_430,c_1017,c_1152,c_1281,c_1394,c_1757,c_2028,c_2446,c_2890,c_3207,c_3284,c_3716,c_9550,c_10090,c_13979,c_26383,c_52973,c_61793])).

cnf(c_79100,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_79022,c_10730])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.50/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.50/4.00  
% 27.50/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.50/4.00  
% 27.50/4.00  ------  iProver source info
% 27.50/4.00  
% 27.50/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.50/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.50/4.00  git: non_committed_changes: false
% 27.50/4.00  git: last_make_outside_of_git: false
% 27.50/4.00  
% 27.50/4.00  ------ 
% 27.50/4.00  ------ Parsing...
% 27.50/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.50/4.00  
% 27.50/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.50/4.00  
% 27.50/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.50/4.00  
% 27.50/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.50/4.00  ------ Proving...
% 27.50/4.00  ------ Problem Properties 
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  clauses                                 27
% 27.50/4.00  conjectures                             4
% 27.50/4.00  EPR                                     5
% 27.50/4.00  Horn                                    21
% 27.50/4.00  unary                                   9
% 27.50/4.00  binary                                  6
% 27.50/4.00  lits                                    59
% 27.50/4.00  lits eq                                 22
% 27.50/4.00  fd_pure                                 0
% 27.50/4.00  fd_pseudo                               0
% 27.50/4.00  fd_cond                                 0
% 27.50/4.00  fd_pseudo_cond                          9
% 27.50/4.00  AC symbols                              0
% 27.50/4.00  
% 27.50/4.00  ------ Input Options Time Limit: Unbounded
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  ------ 
% 27.50/4.00  Current options:
% 27.50/4.00  ------ 
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  ------ Proving...
% 27.50/4.00  
% 27.50/4.00  
% 27.50/4.00  % SZS status Theorem for theBenchmark.p
% 27.50/4.00  
% 27.50/4.00   Resolution empty clause
% 27.50/4.00  
% 27.50/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.50/4.00  
% 27.50/4.00  fof(f7,axiom,(
% 27.50/4.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f32,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.50/4.00    inference(nnf_transformation,[],[f7])).
% 27.50/4.00  
% 27.50/4.00  fof(f33,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.50/4.00    inference(flattening,[],[f32])).
% 27.50/4.00  
% 27.50/4.00  fof(f34,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.50/4.00    inference(rectify,[],[f33])).
% 27.50/4.00  
% 27.50/4.00  fof(f35,plain,(
% 27.50/4.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 27.50/4.00    introduced(choice_axiom,[])).
% 27.50/4.00  
% 27.50/4.00  fof(f36,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.50/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 27.50/4.00  
% 27.50/4.00  fof(f60,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f36])).
% 27.50/4.00  
% 27.50/4.00  fof(f9,axiom,(
% 27.50/4.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f64,plain,(
% 27.50/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f9])).
% 27.50/4.00  
% 27.50/4.00  fof(f10,axiom,(
% 27.50/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f65,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f10])).
% 27.50/4.00  
% 27.50/4.00  fof(f70,plain,(
% 27.50/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.50/4.00    inference(definition_unfolding,[],[f64,f65])).
% 27.50/4.00  
% 27.50/4.00  fof(f78,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 27.50/4.00    inference(definition_unfolding,[],[f60,f70])).
% 27.50/4.00  
% 27.50/4.00  fof(f11,conjecture,(
% 27.50/4.00    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f12,negated_conjecture,(
% 27.50/4.00    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 27.50/4.00    inference(negated_conjecture,[],[f11])).
% 27.50/4.00  
% 27.50/4.00  fof(f15,plain,(
% 27.50/4.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 27.50/4.00    inference(ennf_transformation,[],[f12])).
% 27.50/4.00  
% 27.50/4.00  fof(f16,plain,(
% 27.50/4.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 27.50/4.00    inference(flattening,[],[f15])).
% 27.50/4.00  
% 27.50/4.00  fof(f37,plain,(
% 27.50/4.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK4,sK6) != k1_tarski(sK7) & r2_hidden(sK7,sK4) & k3_xboole_0(sK5,sK6) = k1_tarski(sK7) & r1_tarski(sK4,sK5))),
% 27.50/4.00    introduced(choice_axiom,[])).
% 27.50/4.00  
% 27.50/4.00  fof(f38,plain,(
% 27.50/4.00    k3_xboole_0(sK4,sK6) != k1_tarski(sK7) & r2_hidden(sK7,sK4) & k3_xboole_0(sK5,sK6) = k1_tarski(sK7) & r1_tarski(sK4,sK5)),
% 27.50/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f37])).
% 27.50/4.00  
% 27.50/4.00  fof(f67,plain,(
% 27.50/4.00    k3_xboole_0(sK5,sK6) = k1_tarski(sK7)),
% 27.50/4.00    inference(cnf_transformation,[],[f38])).
% 27.50/4.00  
% 27.50/4.00  fof(f8,axiom,(
% 27.50/4.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f63,plain,(
% 27.50/4.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f8])).
% 27.50/4.00  
% 27.50/4.00  fof(f71,plain,(
% 27.50/4.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 27.50/4.00    inference(definition_unfolding,[],[f63,f70])).
% 27.50/4.00  
% 27.50/4.00  fof(f83,plain,(
% 27.50/4.00    k3_xboole_0(sK5,sK6) = k2_enumset1(sK7,sK7,sK7,sK7)),
% 27.50/4.00    inference(definition_unfolding,[],[f67,f71])).
% 27.50/4.00  
% 27.50/4.00  fof(f66,plain,(
% 27.50/4.00    r1_tarski(sK4,sK5)),
% 27.50/4.00    inference(cnf_transformation,[],[f38])).
% 27.50/4.00  
% 27.50/4.00  fof(f69,plain,(
% 27.50/4.00    k3_xboole_0(sK4,sK6) != k1_tarski(sK7)),
% 27.50/4.00    inference(cnf_transformation,[],[f38])).
% 27.50/4.00  
% 27.50/4.00  fof(f82,plain,(
% 27.50/4.00    k3_xboole_0(sK4,sK6) != k2_enumset1(sK7,sK7,sK7,sK7)),
% 27.50/4.00    inference(definition_unfolding,[],[f69,f71])).
% 27.50/4.00  
% 27.50/4.00  fof(f57,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 27.50/4.00    inference(cnf_transformation,[],[f36])).
% 27.50/4.00  
% 27.50/4.00  fof(f81,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.50/4.00    inference(definition_unfolding,[],[f57,f70])).
% 27.50/4.00  
% 27.50/4.00  fof(f96,plain,(
% 27.50/4.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 27.50/4.00    inference(equality_resolution,[],[f81])).
% 27.50/4.00  
% 27.50/4.00  fof(f58,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.50/4.00    inference(cnf_transformation,[],[f36])).
% 27.50/4.00  
% 27.50/4.00  fof(f80,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.50/4.00    inference(definition_unfolding,[],[f58,f70])).
% 27.50/4.00  
% 27.50/4.00  fof(f94,plain,(
% 27.50/4.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 27.50/4.00    inference(equality_resolution,[],[f80])).
% 27.50/4.00  
% 27.50/4.00  fof(f95,plain,(
% 27.50/4.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 27.50/4.00    inference(equality_resolution,[],[f94])).
% 27.50/4.00  
% 27.50/4.00  fof(f3,axiom,(
% 27.50/4.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f21,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.50/4.00    inference(nnf_transformation,[],[f3])).
% 27.50/4.00  
% 27.50/4.00  fof(f22,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.50/4.00    inference(flattening,[],[f21])).
% 27.50/4.00  
% 27.50/4.00  fof(f23,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.50/4.00    inference(rectify,[],[f22])).
% 27.50/4.00  
% 27.50/4.00  fof(f24,plain,(
% 27.50/4.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.50/4.00    introduced(choice_axiom,[])).
% 27.50/4.00  
% 27.50/4.00  fof(f25,plain,(
% 27.50/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.50/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 27.50/4.00  
% 27.50/4.00  fof(f48,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f25])).
% 27.50/4.00  
% 27.50/4.00  fof(f6,axiom,(
% 27.50/4.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f28,plain,(
% 27.50/4.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 27.50/4.00    inference(nnf_transformation,[],[f6])).
% 27.50/4.00  
% 27.50/4.00  fof(f29,plain,(
% 27.50/4.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.50/4.00    inference(rectify,[],[f28])).
% 27.50/4.00  
% 27.50/4.00  fof(f30,plain,(
% 27.50/4.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 27.50/4.00    introduced(choice_axiom,[])).
% 27.50/4.00  
% 27.50/4.00  fof(f31,plain,(
% 27.50/4.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.50/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 27.50/4.00  
% 27.50/4.00  fof(f54,plain,(
% 27.50/4.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 27.50/4.00    inference(cnf_transformation,[],[f31])).
% 27.50/4.00  
% 27.50/4.00  fof(f74,plain,(
% 27.50/4.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 27.50/4.00    inference(definition_unfolding,[],[f54,f71])).
% 27.50/4.00  
% 27.50/4.00  fof(f89,plain,(
% 27.50/4.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 27.50/4.00    inference(equality_resolution,[],[f74])).
% 27.50/4.00  
% 27.50/4.00  fof(f90,plain,(
% 27.50/4.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 27.50/4.00    inference(equality_resolution,[],[f89])).
% 27.50/4.00  
% 27.50/4.00  fof(f4,axiom,(
% 27.50/4.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f26,plain,(
% 27.50/4.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.50/4.00    inference(nnf_transformation,[],[f4])).
% 27.50/4.00  
% 27.50/4.00  fof(f27,plain,(
% 27.50/4.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.50/4.00    inference(flattening,[],[f26])).
% 27.50/4.00  
% 27.50/4.00  fof(f49,plain,(
% 27.50/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.50/4.00    inference(cnf_transformation,[],[f27])).
% 27.50/4.00  
% 27.50/4.00  fof(f88,plain,(
% 27.50/4.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.50/4.00    inference(equality_resolution,[],[f49])).
% 27.50/4.00  
% 27.50/4.00  fof(f53,plain,(
% 27.50/4.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 27.50/4.00    inference(cnf_transformation,[],[f31])).
% 27.50/4.00  
% 27.50/4.00  fof(f75,plain,(
% 27.50/4.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 27.50/4.00    inference(definition_unfolding,[],[f53,f71])).
% 27.50/4.00  
% 27.50/4.00  fof(f91,plain,(
% 27.50/4.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 27.50/4.00    inference(equality_resolution,[],[f75])).
% 27.50/4.00  
% 27.50/4.00  fof(f2,axiom,(
% 27.50/4.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f13,plain,(
% 27.50/4.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.50/4.00    inference(ennf_transformation,[],[f2])).
% 27.50/4.00  
% 27.50/4.00  fof(f17,plain,(
% 27.50/4.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.50/4.00    inference(nnf_transformation,[],[f13])).
% 27.50/4.00  
% 27.50/4.00  fof(f18,plain,(
% 27.50/4.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.50/4.00    inference(rectify,[],[f17])).
% 27.50/4.00  
% 27.50/4.00  fof(f19,plain,(
% 27.50/4.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.50/4.00    introduced(choice_axiom,[])).
% 27.50/4.00  
% 27.50/4.00  fof(f20,plain,(
% 27.50/4.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.50/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 27.50/4.00  
% 27.50/4.00  fof(f40,plain,(
% 27.50/4.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f20])).
% 27.50/4.00  
% 27.50/4.00  fof(f47,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f25])).
% 27.50/4.00  
% 27.50/4.00  fof(f59,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.50/4.00    inference(cnf_transformation,[],[f36])).
% 27.50/4.00  
% 27.50/4.00  fof(f79,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.50/4.00    inference(definition_unfolding,[],[f59,f70])).
% 27.50/4.00  
% 27.50/4.00  fof(f92,plain,(
% 27.50/4.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 27.50/4.00    inference(equality_resolution,[],[f79])).
% 27.50/4.00  
% 27.50/4.00  fof(f93,plain,(
% 27.50/4.00    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 27.50/4.00    inference(equality_resolution,[],[f92])).
% 27.50/4.00  
% 27.50/4.00  fof(f44,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.50/4.00    inference(cnf_transformation,[],[f25])).
% 27.50/4.00  
% 27.50/4.00  fof(f85,plain,(
% 27.50/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 27.50/4.00    inference(equality_resolution,[],[f44])).
% 27.50/4.00  
% 27.50/4.00  fof(f46,plain,(
% 27.50/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f25])).
% 27.50/4.00  
% 27.50/4.00  fof(f68,plain,(
% 27.50/4.00    r2_hidden(sK7,sK4)),
% 27.50/4.00    inference(cnf_transformation,[],[f38])).
% 27.50/4.00  
% 27.50/4.00  fof(f51,plain,(
% 27.50/4.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f27])).
% 27.50/4.00  
% 27.50/4.00  fof(f1,axiom,(
% 27.50/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.50/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.50/4.00  
% 27.50/4.00  fof(f39,plain,(
% 27.50/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.50/4.00    inference(cnf_transformation,[],[f1])).
% 27.50/4.00  
% 27.50/4.00  fof(f45,plain,(
% 27.50/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 27.50/4.00    inference(cnf_transformation,[],[f25])).
% 27.50/4.00  
% 27.50/4.00  fof(f84,plain,(
% 27.50/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 27.50/4.00    inference(equality_resolution,[],[f45])).
% 27.50/4.00  
% 27.50/4.00  cnf(c_20,plain,
% 27.50/4.00      ( r2_hidden(sK3(X0,X1,X2),X2)
% 27.50/4.00      | k2_enumset1(X0,X0,X0,X1) = X2
% 27.50/4.00      | sK3(X0,X1,X2) = X1
% 27.50/4.00      | sK3(X0,X1,X2) = X0 ),
% 27.50/4.00      inference(cnf_transformation,[],[f78]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_426,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.50/4.00      theory(equality) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_6338,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,X1)
% 27.50/4.00      | r2_hidden(X2,k2_enumset1(X3,X3,X3,X4))
% 27.50/4.00      | r2_hidden(sK3(X3,X4,X1),X1)
% 27.50/4.00      | X2 != X0
% 27.50/4.00      | sK3(X3,X4,X1) = X4
% 27.50/4.00      | sK3(X3,X4,X1) = X3 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_20,c_426]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_423,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_422,plain,( X0 = X0 ),theory(equality) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2120,plain,
% 27.50/4.00      ( X0 != X1 | X1 = X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_423,c_422]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_26,negated_conjecture,
% 27.50/4.00      ( k3_xboole_0(sK5,sK6) = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(cnf_transformation,[],[f83]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_6885,plain,
% 27.50/4.00      ( k2_enumset1(sK7,sK7,sK7,sK7) = k3_xboole_0(sK5,sK6) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2120,c_26]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_46756,plain,
% 27.50/4.00      ( r2_hidden(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(X0,X0,X0,X1))
% 27.50/4.00      | r2_hidden(sK3(X0,X1,X2),X2)
% 27.50/4.00      | ~ r2_hidden(k3_xboole_0(sK5,sK6),X2)
% 27.50/4.00      | sK3(X0,X1,X2) = X1
% 27.50/4.00      | sK3(X0,X1,X2) = X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_6338,c_6885]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2322,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | r2_hidden(X1,k3_xboole_0(sK5,sK6))
% 27.50/4.00      | X1 != X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_426,c_26]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_79015,plain,
% 27.50/4.00      ( r2_hidden(X0,k3_xboole_0(sK5,sK6))
% 27.50/4.00      | r2_hidden(sK3(sK7,sK7,X1),X1)
% 27.50/4.00      | ~ r2_hidden(k3_xboole_0(sK5,sK6),X1)
% 27.50/4.00      | X0 != k2_enumset1(sK7,sK7,sK7,sK7)
% 27.50/4.00      | sK3(sK7,sK7,X1) = sK7 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_46756,c_2322]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_27,negated_conjecture,
% 27.50/4.00      ( r1_tarski(sK4,sK5) ),
% 27.50/4.00      inference(cnf_transformation,[],[f66]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_24,negated_conjecture,
% 27.50/4.00      ( k3_xboole_0(sK4,sK6) != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_23,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 27.50/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_31,plain,
% 27.50/4.00      ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7)) | sK7 = sK7 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_23]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_22,plain,
% 27.50/4.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 27.50/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_34,plain,
% 27.50/4.00      ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_22]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_427,plain,
% 27.50/4.00      ( X0 != X1
% 27.50/4.00      | X2 != X3
% 27.50/4.00      | X4 != X5
% 27.50/4.00      | X6 != X7
% 27.50/4.00      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 27.50/4.00      theory(equality) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_430,plain,
% 27.50/4.00      ( k2_enumset1(sK7,sK7,sK7,sK7) = k2_enumset1(sK7,sK7,sK7,sK7)
% 27.50/4.00      | sK7 != sK7 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_427]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_4,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 27.50/4.00      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 27.50/4.00      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 27.50/4.00      | k3_xboole_0(X0,X1) = X2 ),
% 27.50/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1017,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6)
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
% 27.50/4.00      | k3_xboole_0(sK4,sK6) = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_4]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_16,plain,
% 27.50/4.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 27.50/4.00      inference(cnf_transformation,[],[f90]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1281,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_16]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_12,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2028,plain,
% 27.50/4.00      ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_12]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_17,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 27.50/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2446,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 27.50/4.00      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_17]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_425,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.50/4.00      theory(equality) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2300,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | r1_tarski(X1,k3_xboole_0(sK5,sK6))
% 27.50/4.00      | X1 != X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_425,c_26]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2614,plain,
% 27.50/4.00      ( r1_tarski(X0,k3_xboole_0(sK5,sK6))
% 27.50/4.00      | X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2300,c_12]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2890,plain,
% 27.50/4.00      ( r1_tarski(k3_xboole_0(sK5,sK6),k3_xboole_0(sK5,sK6)) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2614,c_26]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_3,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 27.50/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1458,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
% 27.50/4.00      | ~ r1_tarski(X0,X1) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2674,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
% 27.50/4.00      | ~ r1_tarski(sK4,X0) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_1458]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_3207,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK5)
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
% 27.50/4.00      | ~ r1_tarski(sK4,sK5) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_2674]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_5,plain,
% 27.50/4.00      ( r2_hidden(sK1(X0,X1,X2),X1)
% 27.50/4.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.50/4.00      | k3_xboole_0(X0,X1) = X2 ),
% 27.50/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2370,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_5,c_24]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2643,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6)
% 27.50/4.00      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK7 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2370,c_17]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_21,plain,
% 27.50/4.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 27.50/4.00      inference(cnf_transformation,[],[f93]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2632,plain,
% 27.50/4.00      ( r2_hidden(X0,k3_xboole_0(sK5,sK6)) | X0 != sK7 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2322,c_21]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_8,plain,
% 27.50/4.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 27.50/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2868,plain,
% 27.50/4.00      ( r2_hidden(X0,sK6) | X0 != sK7 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2632,c_8]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_3284,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
% 27.50/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_2643,c_2868]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_6,plain,
% 27.50/4.00      ( r2_hidden(sK1(X0,X1,X2),X0)
% 27.50/4.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.50/4.00      | k3_xboole_0(X0,X1) = X2 ),
% 27.50/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_3716,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_6,c_24]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_25,negated_conjecture,
% 27.50/4.00      ( r2_hidden(sK7,sK4) ),
% 27.50/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_985,plain,
% 27.50/4.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK4) | X0 != sK7 | X1 != sK4 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_426]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1152,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4)
% 27.50/4.00      | ~ r2_hidden(sK7,sK4)
% 27.50/4.00      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK7
% 27.50/4.00      | sK4 != sK4 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_985]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1394,plain,
% 27.50/4.00      ( sK4 = sK4 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_422]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1757,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) = sK7 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_17]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_4102,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK4) ),
% 27.50/4.00      inference(global_propositional_subsumption,
% 27.50/4.00                [status(thm)],
% 27.50/4.00                [c_3716,c_25,c_1152,c_1394,c_1757]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2304,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_425,c_422]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_8439,plain,
% 27.50/4.00      ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
% 27.50/4.00      | ~ r1_tarski(k3_xboole_0(sK5,sK6),X0) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2304,c_6885]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_6906,plain,
% 27.50/4.00      ( r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | ~ r1_tarski(X1,k3_xboole_0(sK5,sK6))
% 27.50/4.00      | X0 != X1 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_6885,c_425]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_9550,plain,
% 27.50/4.00      ( r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | ~ r1_tarski(k3_xboole_0(sK5,sK6),k3_xboole_0(sK5,sK6))
% 27.50/4.00      | X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_8439,c_6906]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_10090,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_1458]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_10,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 27.50/4.00      inference(cnf_transformation,[],[f51]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2114,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_423,c_10]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_0,plain,
% 27.50/4.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 27.50/4.00      inference(cnf_transformation,[],[f39]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2113,plain,
% 27.50/4.00      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_423,c_0]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_10730,plain,
% 27.50/4.00      ( k3_xboole_0(sK6,sK5) = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2113,c_6885]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_13979,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
% 27.50/4.00      | X0 = k3_xboole_0(sK6,sK5) ),
% 27.50/4.00      inference(resolution,[status(thm)],[c_2114,c_10730]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1262,plain,
% 27.50/4.00      ( ~ r1_tarski(X0,X1)
% 27.50/4.00      | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X2)
% 27.50/4.00      | X2 != X1
% 27.50/4.00      | k2_enumset1(sK7,sK7,sK7,sK7) != X0 ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_425]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_5495,plain,
% 27.50/4.00      ( ~ r1_tarski(k2_enumset1(X0,X1,X2,X3),X4)
% 27.50/4.00      | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X5)
% 27.50/4.00      | X5 != X4
% 27.50/4.00      | k2_enumset1(sK7,sK7,sK7,sK7) != k2_enumset1(X0,X1,X2,X3) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_1262]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_26383,plain,
% 27.50/4.00      ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
% 27.50/4.00      | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7))
% 27.50/4.00      | X0 != k2_enumset1(sK7,sK7,sK7,sK7)
% 27.50/4.00      | k2_enumset1(sK7,sK7,sK7,sK7) != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_5495]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_7,plain,
% 27.50/4.00      ( ~ r2_hidden(X0,X1)
% 27.50/4.00      | ~ r2_hidden(X0,X2)
% 27.50/4.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 27.50/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_1471,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(X1,X0)) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_7]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_2712,plain,
% 27.50/4.00      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.00      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,X0))
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
% 27.50/4.00      inference(instantiation,[status(thm)],[c_1471]) ).
% 27.50/4.00  
% 27.50/4.00  cnf(c_52973,plain,
% 27.50/4.00      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,sK5))
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK5)
% 27.50/4.00      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),sK6) ),
% 27.50/4.01      inference(instantiation,[status(thm)],[c_2712]) ).
% 27.50/4.01  
% 27.50/4.01  cnf(c_1496,plain,
% 27.50/4.01      ( ~ r2_hidden(X0,X1)
% 27.50/4.01      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X2)
% 27.50/4.01      | X2 != X1
% 27.50/4.01      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != X0 ),
% 27.50/4.01      inference(instantiation,[status(thm)],[c_426]) ).
% 27.50/4.01  
% 27.50/4.01  cnf(c_13610,plain,
% 27.50/4.01      ( ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.01      | r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X1)
% 27.50/4.01      | X1 != X0
% 27.50/4.01      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.01      inference(instantiation,[status(thm)],[c_1496]) ).
% 27.50/4.01  
% 27.50/4.01  cnf(c_61793,plain,
% 27.50/4.01      ( r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),X0)
% 27.50/4.01      | ~ r2_hidden(sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)),k3_xboole_0(sK6,sK5))
% 27.50/4.01      | X0 != k3_xboole_0(sK6,sK5)
% 27.50/4.01      | sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) != sK1(sK4,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 27.50/4.01      inference(instantiation,[status(thm)],[c_13610]) ).
% 27.50/4.01  
% 27.50/4.01  cnf(c_79022,plain,
% 27.50/4.01      ( X0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 27.50/4.01      inference(global_propositional_subsumption,
% 27.50/4.01                [status(thm)],
% 27.50/4.01                [c_79015,c_27,c_25,c_24,c_31,c_34,c_430,c_1017,c_1152,c_1281,
% 27.50/4.01                 c_1394,c_1757,c_2028,c_2446,c_2890,c_3207,c_3284,c_3716,
% 27.50/4.01                 c_9550,c_10090,c_13979,c_26383,c_52973,c_61793]) ).
% 27.50/4.01  
% 27.50/4.01  cnf(c_79100,plain,
% 27.50/4.01      ( $false ),
% 27.50/4.01      inference(backward_subsumption_resolution,
% 27.50/4.01                [status(thm)],
% 27.50/4.01                [c_79022,c_10730]) ).
% 27.50/4.01  
% 27.50/4.01  
% 27.50/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.50/4.01  
% 27.50/4.01  ------                               Statistics
% 27.50/4.01  
% 27.50/4.01  ------ Selected
% 27.50/4.01  
% 27.50/4.01  total_time:                             3.029
% 27.50/4.01  
%------------------------------------------------------------------------------
