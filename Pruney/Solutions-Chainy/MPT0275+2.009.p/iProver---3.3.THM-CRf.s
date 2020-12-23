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
% DateTime   : Thu Dec  3 11:36:25 EST 2020

% Result     : Theorem 27.76s
% Output     : CNFRefutation 27.76s
% Verified   : 
% Statistics : Number of formulae       :  200 (3447 expanded)
%              Number of clauses        :  103 ( 604 expanded)
%              Number of leaves         :   22 ( 925 expanded)
%              Depth                    :   26
%              Number of atoms          :  622 (8766 expanded)
%              Number of equality atoms :  375 (5007 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f80,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f73,f89])).

fof(f110,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f111,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f110])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r2_hidden(sK3,sK5)
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 )
      & ( ( r2_hidden(sK4,sK5)
          & r2_hidden(sK3,sK5) )
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r2_hidden(sK3,sK5)
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 )
    & ( ( r2_hidden(sK4,sK5)
        & r2_hidden(sK3,sK5) )
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f46])).

fof(f85,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f103,plain,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f85,f67,f90])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f90,f90])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f86,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f86,f67,f90])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f89])).

fof(f112,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f113,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f112])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f84,plain,
    ( r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( r2_hidden(sK3,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f84,f67,f90])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f89])).

fof(f114,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f99])).

fof(f115,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f114])).

cnf(c_25,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1235,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1229,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1594,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_1229])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1231,plain,
    ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3074,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1231])).

cnf(c_3836,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1594,c_3074])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1240,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2619,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1240])).

cnf(c_4032,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_2619])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1241,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5807,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_4032,c_1241])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1230,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1596,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_1230])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1246,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5611,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_1246])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1226,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_19,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1262,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1226,c_19])).

cnf(c_7591,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5611,c_1262])).

cnf(c_7592,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7591])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1248,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7604,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7592,c_1248])).

cnf(c_32913,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_7604])).

cnf(c_26,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1234,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32914,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_7604])).

cnf(c_33285,plain,
    ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5807,c_1596,c_3836,c_32913,c_32914])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1249,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_33299,plain,
    ( r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_33285,c_1249])).

cnf(c_145848,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_33299])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1228,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1595,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_1228])).

cnf(c_3075,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1595,c_1231])).

cnf(c_4467,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1595,c_3075])).

cnf(c_4896,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4467,c_2619])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1243,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5900,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = sK5
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r1_tarski(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_1243])).

cnf(c_5608,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4467,c_1246])).

cnf(c_6773,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5608,c_1262])).

cnf(c_6774,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6773])).

cnf(c_6786,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6774,c_1248])).

cnf(c_29301,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_6786])).

cnf(c_29302,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_6786])).

cnf(c_24,plain,
    ( r2_hidden(sK2(X0,X1,X2,X3),X3)
    | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3
    | sK2(X0,X1,X2,X3) = X2
    | sK2(X0,X1,X2,X3) = X1
    | sK2(X0,X1,X2,X3) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1236,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3
    | sK2(X0,X1,X2,X3) = X2
    | sK2(X0,X1,X2,X3) = X1
    | sK2(X0,X1,X2,X3) = X0
    | r2_hidden(sK2(X0,X1,X2,X3),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6012,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = sK5
    | sK2(X0,X1,X2,sK5) = X2
    | sK2(X0,X1,X2,sK5) = X1
    | sK2(X0,X1,X2,sK5) = X0
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(X0,X1,X2,sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(X0,X1,X2,sK5)) ),
    inference(superposition,[status(thm)],[c_1236,c_3074])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1252,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8901,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(X0,sK5) = X1
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,X1)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,X1))
    | r2_hidden(sK0(X0,sK5,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_3074])).

cnf(c_14327,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(X0,sK5) = sK5
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_8901,c_3074])).

cnf(c_14459,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(X0,sK5) = sK5
    | k3_xboole_0(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_14327,c_0])).

cnf(c_23303,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) = k3_xboole_0(sK5,sK5)
    | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK0(X0,sK5,sK5)
    | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK4
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(X0,sK5) = sK5
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)) ),
    inference(superposition,[status(thm)],[c_6012,c_14459])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23350,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) = sK5
    | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK0(X0,sK5,sK5)
    | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK4
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(X0,sK5) = sK5
    | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)) ),
    inference(demodulation,[status(thm)],[c_23303,c_7])).

cnf(c_4466,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1594,c_3075])).

cnf(c_4884,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4466,c_2619])).

cnf(c_5884,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = sK5
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r1_tarski(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4884,c_1243])).

cnf(c_35,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5885,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_4884,c_1241])).

cnf(c_5609,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4466,c_1246])).

cnf(c_7033,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5609,c_1262])).

cnf(c_7034,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7033])).

cnf(c_7046,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7034,c_1248])).

cnf(c_29911,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_7046])).

cnf(c_29912,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_7046])).

cnf(c_50909,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5884,c_35,c_5885,c_29911,c_29912])).

cnf(c_50921,plain,
    ( k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_50909,c_0])).

cnf(c_51080,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50921,c_1596])).

cnf(c_16,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1242,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2862,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1242,c_1241])).

cnf(c_2863,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2862,c_7])).

cnf(c_51084,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_51080,c_2863])).

cnf(c_51085,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_51084])).

cnf(c_51726,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23350,c_1594,c_1595,c_51085])).

cnf(c_51792,plain,
    ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5900,c_1594,c_1595,c_1596,c_29301,c_29302,c_51085])).

cnf(c_51802,plain,
    ( r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_51792,c_1249])).

cnf(c_51837,plain,
    ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51802])).

cnf(c_51575,plain,
    ( ~ r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)
    | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_50918,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_50909,c_1240])).

cnf(c_50953,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_50918,c_2863])).

cnf(c_50954,plain,
    ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_50953])).

cnf(c_50994,plain,
    ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_50954])).

cnf(c_27,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_42,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_44,plain,
    ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_145848,c_51837,c_51575,c_50994,c_44,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.59/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.59/4.00  
% 27.59/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.59/4.00  
% 27.59/4.00  ------  iProver source info
% 27.59/4.00  
% 27.59/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.59/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.59/4.00  git: non_committed_changes: false
% 27.59/4.00  git: last_make_outside_of_git: false
% 27.59/4.00  
% 27.59/4.00  ------ 
% 27.59/4.00  
% 27.59/4.00  ------ Input Options
% 27.59/4.00  
% 27.59/4.00  --out_options                           all
% 27.59/4.00  --tptp_safe_out                         true
% 27.59/4.00  --problem_path                          ""
% 27.59/4.00  --include_path                          ""
% 27.59/4.00  --clausifier                            res/vclausify_rel
% 27.59/4.00  --clausifier_options                    --mode clausify
% 27.59/4.00  --stdin                                 false
% 27.59/4.00  --stats_out                             all
% 27.59/4.00  
% 27.59/4.00  ------ General Options
% 27.59/4.00  
% 27.59/4.00  --fof                                   false
% 27.59/4.00  --time_out_real                         305.
% 27.59/4.00  --time_out_virtual                      -1.
% 27.59/4.00  --symbol_type_check                     false
% 27.59/4.00  --clausify_out                          false
% 27.59/4.00  --sig_cnt_out                           false
% 27.59/4.00  --trig_cnt_out                          false
% 27.59/4.00  --trig_cnt_out_tolerance                1.
% 27.59/4.00  --trig_cnt_out_sk_spl                   false
% 27.59/4.00  --abstr_cl_out                          false
% 27.59/4.00  
% 27.59/4.00  ------ Global Options
% 27.59/4.00  
% 27.59/4.00  --schedule                              default
% 27.59/4.00  --add_important_lit                     false
% 27.59/4.00  --prop_solver_per_cl                    1000
% 27.59/4.00  --min_unsat_core                        false
% 27.59/4.00  --soft_assumptions                      false
% 27.59/4.00  --soft_lemma_size                       3
% 27.59/4.00  --prop_impl_unit_size                   0
% 27.59/4.00  --prop_impl_unit                        []
% 27.59/4.00  --share_sel_clauses                     true
% 27.59/4.00  --reset_solvers                         false
% 27.59/4.00  --bc_imp_inh                            [conj_cone]
% 27.59/4.00  --conj_cone_tolerance                   3.
% 27.59/4.00  --extra_neg_conj                        none
% 27.59/4.00  --large_theory_mode                     true
% 27.59/4.00  --prolific_symb_bound                   200
% 27.59/4.00  --lt_threshold                          2000
% 27.59/4.00  --clause_weak_htbl                      true
% 27.59/4.00  --gc_record_bc_elim                     false
% 27.59/4.00  
% 27.59/4.00  ------ Preprocessing Options
% 27.59/4.00  
% 27.59/4.00  --preprocessing_flag                    true
% 27.59/4.00  --time_out_prep_mult                    0.1
% 27.59/4.00  --splitting_mode                        input
% 27.59/4.00  --splitting_grd                         true
% 27.59/4.00  --splitting_cvd                         false
% 27.59/4.00  --splitting_cvd_svl                     false
% 27.59/4.00  --splitting_nvd                         32
% 27.59/4.00  --sub_typing                            true
% 27.59/4.00  --prep_gs_sim                           true
% 27.59/4.00  --prep_unflatten                        true
% 27.59/4.00  --prep_res_sim                          true
% 27.59/4.00  --prep_upred                            true
% 27.59/4.00  --prep_sem_filter                       exhaustive
% 27.59/4.00  --prep_sem_filter_out                   false
% 27.59/4.00  --pred_elim                             true
% 27.59/4.00  --res_sim_input                         true
% 27.59/4.00  --eq_ax_congr_red                       true
% 27.59/4.00  --pure_diseq_elim                       true
% 27.59/4.00  --brand_transform                       false
% 27.59/4.00  --non_eq_to_eq                          false
% 27.59/4.00  --prep_def_merge                        true
% 27.59/4.00  --prep_def_merge_prop_impl              false
% 27.59/4.00  --prep_def_merge_mbd                    true
% 27.59/4.00  --prep_def_merge_tr_red                 false
% 27.59/4.00  --prep_def_merge_tr_cl                  false
% 27.59/4.00  --smt_preprocessing                     true
% 27.59/4.00  --smt_ac_axioms                         fast
% 27.59/4.00  --preprocessed_out                      false
% 27.59/4.00  --preprocessed_stats                    false
% 27.59/4.00  
% 27.59/4.00  ------ Abstraction refinement Options
% 27.59/4.00  
% 27.59/4.00  --abstr_ref                             []
% 27.59/4.00  --abstr_ref_prep                        false
% 27.59/4.00  --abstr_ref_until_sat                   false
% 27.59/4.00  --abstr_ref_sig_restrict                funpre
% 27.59/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.59/4.00  --abstr_ref_under                       []
% 27.59/4.00  
% 27.59/4.00  ------ SAT Options
% 27.59/4.00  
% 27.59/4.00  --sat_mode                              false
% 27.59/4.00  --sat_fm_restart_options                ""
% 27.59/4.00  --sat_gr_def                            false
% 27.59/4.00  --sat_epr_types                         true
% 27.59/4.00  --sat_non_cyclic_types                  false
% 27.59/4.00  --sat_finite_models                     false
% 27.59/4.00  --sat_fm_lemmas                         false
% 27.59/4.00  --sat_fm_prep                           false
% 27.59/4.00  --sat_fm_uc_incr                        true
% 27.59/4.00  --sat_out_model                         small
% 27.59/4.00  --sat_out_clauses                       false
% 27.59/4.00  
% 27.59/4.00  ------ QBF Options
% 27.59/4.00  
% 27.59/4.00  --qbf_mode                              false
% 27.59/4.00  --qbf_elim_univ                         false
% 27.59/4.00  --qbf_dom_inst                          none
% 27.59/4.00  --qbf_dom_pre_inst                      false
% 27.59/4.00  --qbf_sk_in                             false
% 27.59/4.00  --qbf_pred_elim                         true
% 27.59/4.00  --qbf_split                             512
% 27.59/4.00  
% 27.59/4.00  ------ BMC1 Options
% 27.59/4.00  
% 27.59/4.00  --bmc1_incremental                      false
% 27.59/4.00  --bmc1_axioms                           reachable_all
% 27.59/4.00  --bmc1_min_bound                        0
% 27.59/4.00  --bmc1_max_bound                        -1
% 27.59/4.00  --bmc1_max_bound_default                -1
% 27.59/4.00  --bmc1_symbol_reachability              true
% 27.59/4.00  --bmc1_property_lemmas                  false
% 27.59/4.00  --bmc1_k_induction                      false
% 27.59/4.00  --bmc1_non_equiv_states                 false
% 27.59/4.00  --bmc1_deadlock                         false
% 27.59/4.00  --bmc1_ucm                              false
% 27.59/4.00  --bmc1_add_unsat_core                   none
% 27.59/4.00  --bmc1_unsat_core_children              false
% 27.59/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.59/4.00  --bmc1_out_stat                         full
% 27.59/4.00  --bmc1_ground_init                      false
% 27.59/4.00  --bmc1_pre_inst_next_state              false
% 27.59/4.00  --bmc1_pre_inst_state                   false
% 27.59/4.00  --bmc1_pre_inst_reach_state             false
% 27.59/4.00  --bmc1_out_unsat_core                   false
% 27.59/4.00  --bmc1_aig_witness_out                  false
% 27.59/4.00  --bmc1_verbose                          false
% 27.59/4.00  --bmc1_dump_clauses_tptp                false
% 27.59/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.59/4.00  --bmc1_dump_file                        -
% 27.59/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.59/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.59/4.00  --bmc1_ucm_extend_mode                  1
% 27.59/4.00  --bmc1_ucm_init_mode                    2
% 27.59/4.00  --bmc1_ucm_cone_mode                    none
% 27.59/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.59/4.00  --bmc1_ucm_relax_model                  4
% 27.59/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.59/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.59/4.00  --bmc1_ucm_layered_model                none
% 27.59/4.00  --bmc1_ucm_max_lemma_size               10
% 27.59/4.00  
% 27.59/4.00  ------ AIG Options
% 27.59/4.00  
% 27.59/4.00  --aig_mode                              false
% 27.59/4.00  
% 27.59/4.00  ------ Instantiation Options
% 27.59/4.00  
% 27.59/4.00  --instantiation_flag                    true
% 27.59/4.00  --inst_sos_flag                         false
% 27.59/4.00  --inst_sos_phase                        true
% 27.59/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.59/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.59/4.00  --inst_lit_sel_side                     num_symb
% 27.59/4.00  --inst_solver_per_active                1400
% 27.59/4.00  --inst_solver_calls_frac                1.
% 27.59/4.00  --inst_passive_queue_type               priority_queues
% 27.59/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.59/4.00  --inst_passive_queues_freq              [25;2]
% 27.59/4.00  --inst_dismatching                      true
% 27.59/4.00  --inst_eager_unprocessed_to_passive     true
% 27.59/4.00  --inst_prop_sim_given                   true
% 27.59/4.00  --inst_prop_sim_new                     false
% 27.59/4.00  --inst_subs_new                         false
% 27.59/4.00  --inst_eq_res_simp                      false
% 27.59/4.00  --inst_subs_given                       false
% 27.59/4.00  --inst_orphan_elimination               true
% 27.59/4.00  --inst_learning_loop_flag               true
% 27.59/4.00  --inst_learning_start                   3000
% 27.59/4.00  --inst_learning_factor                  2
% 27.59/4.00  --inst_start_prop_sim_after_learn       3
% 27.59/4.00  --inst_sel_renew                        solver
% 27.59/4.00  --inst_lit_activity_flag                true
% 27.59/4.00  --inst_restr_to_given                   false
% 27.59/4.00  --inst_activity_threshold               500
% 27.59/4.00  --inst_out_proof                        true
% 27.59/4.00  
% 27.59/4.00  ------ Resolution Options
% 27.59/4.00  
% 27.59/4.00  --resolution_flag                       true
% 27.59/4.00  --res_lit_sel                           adaptive
% 27.59/4.00  --res_lit_sel_side                      none
% 27.59/4.00  --res_ordering                          kbo
% 27.59/4.00  --res_to_prop_solver                    active
% 27.59/4.00  --res_prop_simpl_new                    false
% 27.59/4.00  --res_prop_simpl_given                  true
% 27.59/4.00  --res_passive_queue_type                priority_queues
% 27.59/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.59/4.00  --res_passive_queues_freq               [15;5]
% 27.59/4.00  --res_forward_subs                      full
% 27.59/4.00  --res_backward_subs                     full
% 27.59/4.00  --res_forward_subs_resolution           true
% 27.59/4.00  --res_backward_subs_resolution          true
% 27.59/4.00  --res_orphan_elimination                true
% 27.59/4.00  --res_time_limit                        2.
% 27.59/4.00  --res_out_proof                         true
% 27.59/4.00  
% 27.59/4.00  ------ Superposition Options
% 27.59/4.00  
% 27.59/4.00  --superposition_flag                    true
% 27.59/4.00  --sup_passive_queue_type                priority_queues
% 27.59/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.59/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.59/4.00  --demod_completeness_check              fast
% 27.59/4.00  --demod_use_ground                      true
% 27.59/4.00  --sup_to_prop_solver                    passive
% 27.59/4.00  --sup_prop_simpl_new                    true
% 27.59/4.00  --sup_prop_simpl_given                  true
% 27.59/4.00  --sup_fun_splitting                     false
% 27.59/4.00  --sup_smt_interval                      50000
% 27.59/4.00  
% 27.59/4.00  ------ Superposition Simplification Setup
% 27.59/4.00  
% 27.59/4.00  --sup_indices_passive                   []
% 27.59/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.59/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.59/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.59/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.59/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.59/4.00  --sup_full_bw                           [BwDemod]
% 27.59/4.00  --sup_immed_triv                        [TrivRules]
% 27.59/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.59/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.59/4.00  --sup_immed_bw_main                     []
% 27.59/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.59/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.59/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.59/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.59/4.00  
% 27.59/4.00  ------ Combination Options
% 27.59/4.00  
% 27.59/4.00  --comb_res_mult                         3
% 27.59/4.00  --comb_sup_mult                         2
% 27.59/4.00  --comb_inst_mult                        10
% 27.59/4.00  
% 27.59/4.00  ------ Debug Options
% 27.59/4.00  
% 27.59/4.00  --dbg_backtrace                         false
% 27.59/4.00  --dbg_dump_prop_clauses                 false
% 27.59/4.00  --dbg_dump_prop_clauses_file            -
% 27.59/4.00  --dbg_out_stat                          false
% 27.59/4.00  ------ Parsing...
% 27.59/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.59/4.00  
% 27.59/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.59/4.00  
% 27.59/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.59/4.00  
% 27.59/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.59/4.00  ------ Proving...
% 27.59/4.00  ------ Problem Properties 
% 27.59/4.00  
% 27.59/4.00  
% 27.59/4.00  clauses                                 31
% 27.59/4.00  conjectures                             3
% 27.59/4.00  EPR                                     2
% 27.59/4.00  Horn                                    22
% 27.59/4.00  unary                                   8
% 27.59/4.00  binary                                  7
% 27.59/4.00  lits                                    74
% 27.59/4.00  lits eq                                 26
% 27.59/4.00  fd_pure                                 0
% 27.59/4.00  fd_pseudo                               0
% 27.59/4.00  fd_cond                                 0
% 27.59/4.00  fd_pseudo_cond                          8
% 27.59/4.00  AC symbols                              0
% 27.59/4.00  
% 27.59/4.00  ------ Schedule dynamic 5 is on 
% 27.59/4.00  
% 27.59/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.59/4.00  
% 27.59/4.00  
% 27.59/4.00  ------ 
% 27.59/4.00  Current options:
% 27.59/4.00  ------ 
% 27.59/4.00  
% 27.59/4.00  ------ Input Options
% 27.59/4.00  
% 27.59/4.00  --out_options                           all
% 27.59/4.00  --tptp_safe_out                         true
% 27.59/4.00  --problem_path                          ""
% 27.59/4.00  --include_path                          ""
% 27.59/4.00  --clausifier                            res/vclausify_rel
% 27.59/4.00  --clausifier_options                    --mode clausify
% 27.59/4.00  --stdin                                 false
% 27.59/4.00  --stats_out                             all
% 27.76/4.00  
% 27.76/4.00  ------ General Options
% 27.76/4.00  
% 27.76/4.00  --fof                                   false
% 27.76/4.00  --time_out_real                         305.
% 27.76/4.00  --time_out_virtual                      -1.
% 27.76/4.00  --symbol_type_check                     false
% 27.76/4.00  --clausify_out                          false
% 27.76/4.00  --sig_cnt_out                           false
% 27.76/4.00  --trig_cnt_out                          false
% 27.76/4.00  --trig_cnt_out_tolerance                1.
% 27.76/4.00  --trig_cnt_out_sk_spl                   false
% 27.76/4.00  --abstr_cl_out                          false
% 27.76/4.00  
% 27.76/4.00  ------ Global Options
% 27.76/4.00  
% 27.76/4.00  --schedule                              default
% 27.76/4.00  --add_important_lit                     false
% 27.76/4.00  --prop_solver_per_cl                    1000
% 27.76/4.00  --min_unsat_core                        false
% 27.76/4.00  --soft_assumptions                      false
% 27.76/4.00  --soft_lemma_size                       3
% 27.76/4.00  --prop_impl_unit_size                   0
% 27.76/4.00  --prop_impl_unit                        []
% 27.76/4.00  --share_sel_clauses                     true
% 27.76/4.00  --reset_solvers                         false
% 27.76/4.00  --bc_imp_inh                            [conj_cone]
% 27.76/4.00  --conj_cone_tolerance                   3.
% 27.76/4.00  --extra_neg_conj                        none
% 27.76/4.00  --large_theory_mode                     true
% 27.76/4.00  --prolific_symb_bound                   200
% 27.76/4.00  --lt_threshold                          2000
% 27.76/4.00  --clause_weak_htbl                      true
% 27.76/4.00  --gc_record_bc_elim                     false
% 27.76/4.00  
% 27.76/4.00  ------ Preprocessing Options
% 27.76/4.00  
% 27.76/4.00  --preprocessing_flag                    true
% 27.76/4.00  --time_out_prep_mult                    0.1
% 27.76/4.00  --splitting_mode                        input
% 27.76/4.00  --splitting_grd                         true
% 27.76/4.00  --splitting_cvd                         false
% 27.76/4.00  --splitting_cvd_svl                     false
% 27.76/4.00  --splitting_nvd                         32
% 27.76/4.00  --sub_typing                            true
% 27.76/4.00  --prep_gs_sim                           true
% 27.76/4.00  --prep_unflatten                        true
% 27.76/4.00  --prep_res_sim                          true
% 27.76/4.00  --prep_upred                            true
% 27.76/4.00  --prep_sem_filter                       exhaustive
% 27.76/4.00  --prep_sem_filter_out                   false
% 27.76/4.00  --pred_elim                             true
% 27.76/4.00  --res_sim_input                         true
% 27.76/4.00  --eq_ax_congr_red                       true
% 27.76/4.00  --pure_diseq_elim                       true
% 27.76/4.00  --brand_transform                       false
% 27.76/4.00  --non_eq_to_eq                          false
% 27.76/4.00  --prep_def_merge                        true
% 27.76/4.00  --prep_def_merge_prop_impl              false
% 27.76/4.00  --prep_def_merge_mbd                    true
% 27.76/4.00  --prep_def_merge_tr_red                 false
% 27.76/4.00  --prep_def_merge_tr_cl                  false
% 27.76/4.00  --smt_preprocessing                     true
% 27.76/4.00  --smt_ac_axioms                         fast
% 27.76/4.00  --preprocessed_out                      false
% 27.76/4.00  --preprocessed_stats                    false
% 27.76/4.00  
% 27.76/4.00  ------ Abstraction refinement Options
% 27.76/4.00  
% 27.76/4.00  --abstr_ref                             []
% 27.76/4.00  --abstr_ref_prep                        false
% 27.76/4.00  --abstr_ref_until_sat                   false
% 27.76/4.00  --abstr_ref_sig_restrict                funpre
% 27.76/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.76/4.00  --abstr_ref_under                       []
% 27.76/4.00  
% 27.76/4.00  ------ SAT Options
% 27.76/4.00  
% 27.76/4.00  --sat_mode                              false
% 27.76/4.00  --sat_fm_restart_options                ""
% 27.76/4.00  --sat_gr_def                            false
% 27.76/4.00  --sat_epr_types                         true
% 27.76/4.00  --sat_non_cyclic_types                  false
% 27.76/4.00  --sat_finite_models                     false
% 27.76/4.00  --sat_fm_lemmas                         false
% 27.76/4.00  --sat_fm_prep                           false
% 27.76/4.00  --sat_fm_uc_incr                        true
% 27.76/4.00  --sat_out_model                         small
% 27.76/4.00  --sat_out_clauses                       false
% 27.76/4.00  
% 27.76/4.00  ------ QBF Options
% 27.76/4.00  
% 27.76/4.00  --qbf_mode                              false
% 27.76/4.00  --qbf_elim_univ                         false
% 27.76/4.00  --qbf_dom_inst                          none
% 27.76/4.00  --qbf_dom_pre_inst                      false
% 27.76/4.00  --qbf_sk_in                             false
% 27.76/4.00  --qbf_pred_elim                         true
% 27.76/4.00  --qbf_split                             512
% 27.76/4.00  
% 27.76/4.00  ------ BMC1 Options
% 27.76/4.00  
% 27.76/4.00  --bmc1_incremental                      false
% 27.76/4.00  --bmc1_axioms                           reachable_all
% 27.76/4.00  --bmc1_min_bound                        0
% 27.76/4.00  --bmc1_max_bound                        -1
% 27.76/4.00  --bmc1_max_bound_default                -1
% 27.76/4.00  --bmc1_symbol_reachability              true
% 27.76/4.00  --bmc1_property_lemmas                  false
% 27.76/4.00  --bmc1_k_induction                      false
% 27.76/4.00  --bmc1_non_equiv_states                 false
% 27.76/4.00  --bmc1_deadlock                         false
% 27.76/4.00  --bmc1_ucm                              false
% 27.76/4.00  --bmc1_add_unsat_core                   none
% 27.76/4.00  --bmc1_unsat_core_children              false
% 27.76/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.76/4.00  --bmc1_out_stat                         full
% 27.76/4.00  --bmc1_ground_init                      false
% 27.76/4.00  --bmc1_pre_inst_next_state              false
% 27.76/4.00  --bmc1_pre_inst_state                   false
% 27.76/4.00  --bmc1_pre_inst_reach_state             false
% 27.76/4.00  --bmc1_out_unsat_core                   false
% 27.76/4.00  --bmc1_aig_witness_out                  false
% 27.76/4.00  --bmc1_verbose                          false
% 27.76/4.00  --bmc1_dump_clauses_tptp                false
% 27.76/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.76/4.00  --bmc1_dump_file                        -
% 27.76/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.76/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.76/4.00  --bmc1_ucm_extend_mode                  1
% 27.76/4.00  --bmc1_ucm_init_mode                    2
% 27.76/4.00  --bmc1_ucm_cone_mode                    none
% 27.76/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.76/4.00  --bmc1_ucm_relax_model                  4
% 27.76/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.76/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.76/4.00  --bmc1_ucm_layered_model                none
% 27.76/4.00  --bmc1_ucm_max_lemma_size               10
% 27.76/4.00  
% 27.76/4.00  ------ AIG Options
% 27.76/4.00  
% 27.76/4.00  --aig_mode                              false
% 27.76/4.00  
% 27.76/4.00  ------ Instantiation Options
% 27.76/4.00  
% 27.76/4.00  --instantiation_flag                    true
% 27.76/4.00  --inst_sos_flag                         false
% 27.76/4.00  --inst_sos_phase                        true
% 27.76/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.76/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.76/4.00  --inst_lit_sel_side                     none
% 27.76/4.00  --inst_solver_per_active                1400
% 27.76/4.00  --inst_solver_calls_frac                1.
% 27.76/4.00  --inst_passive_queue_type               priority_queues
% 27.76/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.76/4.00  --inst_passive_queues_freq              [25;2]
% 27.76/4.00  --inst_dismatching                      true
% 27.76/4.00  --inst_eager_unprocessed_to_passive     true
% 27.76/4.00  --inst_prop_sim_given                   true
% 27.76/4.00  --inst_prop_sim_new                     false
% 27.76/4.00  --inst_subs_new                         false
% 27.76/4.00  --inst_eq_res_simp                      false
% 27.76/4.00  --inst_subs_given                       false
% 27.76/4.00  --inst_orphan_elimination               true
% 27.76/4.00  --inst_learning_loop_flag               true
% 27.76/4.00  --inst_learning_start                   3000
% 27.76/4.00  --inst_learning_factor                  2
% 27.76/4.00  --inst_start_prop_sim_after_learn       3
% 27.76/4.00  --inst_sel_renew                        solver
% 27.76/4.00  --inst_lit_activity_flag                true
% 27.76/4.00  --inst_restr_to_given                   false
% 27.76/4.00  --inst_activity_threshold               500
% 27.76/4.00  --inst_out_proof                        true
% 27.76/4.00  
% 27.76/4.00  ------ Resolution Options
% 27.76/4.00  
% 27.76/4.00  --resolution_flag                       false
% 27.76/4.00  --res_lit_sel                           adaptive
% 27.76/4.00  --res_lit_sel_side                      none
% 27.76/4.00  --res_ordering                          kbo
% 27.76/4.00  --res_to_prop_solver                    active
% 27.76/4.00  --res_prop_simpl_new                    false
% 27.76/4.00  --res_prop_simpl_given                  true
% 27.76/4.00  --res_passive_queue_type                priority_queues
% 27.76/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.76/4.00  --res_passive_queues_freq               [15;5]
% 27.76/4.00  --res_forward_subs                      full
% 27.76/4.00  --res_backward_subs                     full
% 27.76/4.00  --res_forward_subs_resolution           true
% 27.76/4.00  --res_backward_subs_resolution          true
% 27.76/4.00  --res_orphan_elimination                true
% 27.76/4.00  --res_time_limit                        2.
% 27.76/4.00  --res_out_proof                         true
% 27.76/4.00  
% 27.76/4.00  ------ Superposition Options
% 27.76/4.00  
% 27.76/4.00  --superposition_flag                    true
% 27.76/4.00  --sup_passive_queue_type                priority_queues
% 27.76/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.76/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.76/4.00  --demod_completeness_check              fast
% 27.76/4.00  --demod_use_ground                      true
% 27.76/4.00  --sup_to_prop_solver                    passive
% 27.76/4.00  --sup_prop_simpl_new                    true
% 27.76/4.00  --sup_prop_simpl_given                  true
% 27.76/4.00  --sup_fun_splitting                     false
% 27.76/4.00  --sup_smt_interval                      50000
% 27.76/4.00  
% 27.76/4.00  ------ Superposition Simplification Setup
% 27.76/4.00  
% 27.76/4.00  --sup_indices_passive                   []
% 27.76/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.76/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.76/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.76/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.76/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.76/4.00  --sup_full_bw                           [BwDemod]
% 27.76/4.00  --sup_immed_triv                        [TrivRules]
% 27.76/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.76/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.76/4.00  --sup_immed_bw_main                     []
% 27.76/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.76/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.76/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.76/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.76/4.00  
% 27.76/4.00  ------ Combination Options
% 27.76/4.00  
% 27.76/4.00  --comb_res_mult                         3
% 27.76/4.00  --comb_sup_mult                         2
% 27.76/4.00  --comb_inst_mult                        10
% 27.76/4.00  
% 27.76/4.00  ------ Debug Options
% 27.76/4.00  
% 27.76/4.00  --dbg_backtrace                         false
% 27.76/4.00  --dbg_dump_prop_clauses                 false
% 27.76/4.00  --dbg_dump_prop_clauses_file            -
% 27.76/4.00  --dbg_out_stat                          false
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  ------ Proving...
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  % SZS status Theorem for theBenchmark.p
% 27.76/4.00  
% 27.76/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.76/4.00  
% 27.76/4.00  fof(f11,axiom,(
% 27.76/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f24,plain,(
% 27.76/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 27.76/4.00    inference(ennf_transformation,[],[f11])).
% 27.76/4.00  
% 27.76/4.00  fof(f39,plain,(
% 27.76/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.76/4.00    inference(nnf_transformation,[],[f24])).
% 27.76/4.00  
% 27.76/4.00  fof(f40,plain,(
% 27.76/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.76/4.00    inference(flattening,[],[f39])).
% 27.76/4.00  
% 27.76/4.00  fof(f41,plain,(
% 27.76/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.76/4.00    inference(rectify,[],[f40])).
% 27.76/4.00  
% 27.76/4.00  fof(f42,plain,(
% 27.76/4.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 27.76/4.00    introduced(choice_axiom,[])).
% 27.76/4.00  
% 27.76/4.00  fof(f43,plain,(
% 27.76/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.76/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 27.76/4.00  
% 27.76/4.00  fof(f73,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.76/4.00    inference(cnf_transformation,[],[f43])).
% 27.76/4.00  
% 27.76/4.00  fof(f13,axiom,(
% 27.76/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f79,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f13])).
% 27.76/4.00  
% 27.76/4.00  fof(f14,axiom,(
% 27.76/4.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f80,plain,(
% 27.76/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f14])).
% 27.76/4.00  
% 27.76/4.00  fof(f15,axiom,(
% 27.76/4.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f81,plain,(
% 27.76/4.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f15])).
% 27.76/4.00  
% 27.76/4.00  fof(f16,axiom,(
% 27.76/4.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f82,plain,(
% 27.76/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f16])).
% 27.76/4.00  
% 27.76/4.00  fof(f87,plain,(
% 27.76/4.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f81,f82])).
% 27.76/4.00  
% 27.76/4.00  fof(f88,plain,(
% 27.76/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f80,f87])).
% 27.76/4.00  
% 27.76/4.00  fof(f89,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f79,f88])).
% 27.76/4.00  
% 27.76/4.00  fof(f97,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 27.76/4.00    inference(definition_unfolding,[],[f73,f89])).
% 27.76/4.00  
% 27.76/4.00  fof(f110,plain,(
% 27.76/4.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 27.76/4.00    inference(equality_resolution,[],[f97])).
% 27.76/4.00  
% 27.76/4.00  fof(f111,plain,(
% 27.76/4.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 27.76/4.00    inference(equality_resolution,[],[f110])).
% 27.76/4.00  
% 27.76/4.00  fof(f1,axiom,(
% 27.76/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f48,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f1])).
% 27.76/4.00  
% 27.76/4.00  fof(f18,conjecture,(
% 27.76/4.00    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f19,negated_conjecture,(
% 27.76/4.00    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 27.76/4.00    inference(negated_conjecture,[],[f18])).
% 27.76/4.00  
% 27.76/4.00  fof(f27,plain,(
% 27.76/4.00    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 27.76/4.00    inference(ennf_transformation,[],[f19])).
% 27.76/4.00  
% 27.76/4.00  fof(f44,plain,(
% 27.76/4.00    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 27.76/4.00    inference(nnf_transformation,[],[f27])).
% 27.76/4.00  
% 27.76/4.00  fof(f45,plain,(
% 27.76/4.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 27.76/4.00    inference(flattening,[],[f44])).
% 27.76/4.00  
% 27.76/4.00  fof(f46,plain,(
% 27.76/4.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0)) => ((~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0))),
% 27.76/4.00    introduced(choice_axiom,[])).
% 27.76/4.00  
% 27.76/4.00  fof(f47,plain,(
% 27.76/4.00    (~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0)),
% 27.76/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f46])).
% 27.76/4.00  
% 27.76/4.00  fof(f85,plain,(
% 27.76/4.00    r2_hidden(sK4,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0),
% 27.76/4.00    inference(cnf_transformation,[],[f47])).
% 27.76/4.00  
% 27.76/4.00  fof(f8,axiom,(
% 27.76/4.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f67,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f8])).
% 27.76/4.00  
% 27.76/4.00  fof(f12,axiom,(
% 27.76/4.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f78,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f12])).
% 27.76/4.00  
% 27.76/4.00  fof(f90,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f78,f89])).
% 27.76/4.00  
% 27.76/4.00  fof(f103,plain,(
% 27.76/4.00    r2_hidden(sK4,sK5) | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0),
% 27.76/4.00    inference(definition_unfolding,[],[f85,f67,f90])).
% 27.76/4.00  
% 27.76/4.00  fof(f17,axiom,(
% 27.76/4.00    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f25,plain,(
% 27.76/4.00    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 27.76/4.00    inference(ennf_transformation,[],[f17])).
% 27.76/4.00  
% 27.76/4.00  fof(f26,plain,(
% 27.76/4.00    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 27.76/4.00    inference(flattening,[],[f25])).
% 27.76/4.00  
% 27.76/4.00  fof(f83,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f26])).
% 27.76/4.00  
% 27.76/4.00  fof(f101,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f83,f90,f90])).
% 27.76/4.00  
% 27.76/4.00  fof(f7,axiom,(
% 27.76/4.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f38,plain,(
% 27.76/4.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.76/4.00    inference(nnf_transformation,[],[f7])).
% 27.76/4.00  
% 27.76/4.00  fof(f65,plain,(
% 27.76/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.76/4.00    inference(cnf_transformation,[],[f38])).
% 27.76/4.00  
% 27.76/4.00  fof(f92,plain,(
% 27.76/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 27.76/4.00    inference(definition_unfolding,[],[f65,f67])).
% 27.76/4.00  
% 27.76/4.00  fof(f66,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f38])).
% 27.76/4.00  
% 27.76/4.00  fof(f91,plain,(
% 27.76/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f66,f67])).
% 27.76/4.00  
% 27.76/4.00  fof(f86,plain,(
% 27.76/4.00    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 27.76/4.00    inference(cnf_transformation,[],[f47])).
% 27.76/4.00  
% 27.76/4.00  fof(f102,plain,(
% 27.76/4.00    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0),
% 27.76/4.00    inference(definition_unfolding,[],[f86,f67,f90])).
% 27.76/4.00  
% 27.76/4.00  fof(f4,axiom,(
% 27.76/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f22,plain,(
% 27.76/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 27.76/4.00    inference(ennf_transformation,[],[f4])).
% 27.76/4.00  
% 27.76/4.00  fof(f33,plain,(
% 27.76/4.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 27.76/4.00    inference(nnf_transformation,[],[f22])).
% 27.76/4.00  
% 27.76/4.00  fof(f58,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f33])).
% 27.76/4.00  
% 27.76/4.00  fof(f5,axiom,(
% 27.76/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f21,plain,(
% 27.76/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.76/4.00    inference(rectify,[],[f5])).
% 27.76/4.00  
% 27.76/4.00  fof(f23,plain,(
% 27.76/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.76/4.00    inference(ennf_transformation,[],[f21])).
% 27.76/4.00  
% 27.76/4.00  fof(f34,plain,(
% 27.76/4.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 27.76/4.00    introduced(choice_axiom,[])).
% 27.76/4.00  
% 27.76/4.00  fof(f35,plain,(
% 27.76/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.76/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f34])).
% 27.76/4.00  
% 27.76/4.00  fof(f61,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.76/4.00    inference(cnf_transformation,[],[f35])).
% 27.76/4.00  
% 27.76/4.00  fof(f10,axiom,(
% 27.76/4.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f69,plain,(
% 27.76/4.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f10])).
% 27.76/4.00  
% 27.76/4.00  fof(f9,axiom,(
% 27.76/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f68,plain,(
% 27.76/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.76/4.00    inference(cnf_transformation,[],[f9])).
% 27.76/4.00  
% 27.76/4.00  fof(f2,axiom,(
% 27.76/4.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f28,plain,(
% 27.76/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.76/4.00    inference(nnf_transformation,[],[f2])).
% 27.76/4.00  
% 27.76/4.00  fof(f29,plain,(
% 27.76/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.76/4.00    inference(flattening,[],[f28])).
% 27.76/4.00  
% 27.76/4.00  fof(f30,plain,(
% 27.76/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.76/4.00    inference(rectify,[],[f29])).
% 27.76/4.00  
% 27.76/4.00  fof(f31,plain,(
% 27.76/4.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.76/4.00    introduced(choice_axiom,[])).
% 27.76/4.00  
% 27.76/4.00  fof(f32,plain,(
% 27.76/4.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.76/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 27.76/4.00  
% 27.76/4.00  fof(f49,plain,(
% 27.76/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.76/4.00    inference(cnf_transformation,[],[f32])).
% 27.76/4.00  
% 27.76/4.00  fof(f107,plain,(
% 27.76/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 27.76/4.00    inference(equality_resolution,[],[f49])).
% 27.76/4.00  
% 27.76/4.00  fof(f72,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.76/4.00    inference(cnf_transformation,[],[f43])).
% 27.76/4.00  
% 27.76/4.00  fof(f98,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 27.76/4.00    inference(definition_unfolding,[],[f72,f89])).
% 27.76/4.00  
% 27.76/4.00  fof(f112,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 27.76/4.00    inference(equality_resolution,[],[f98])).
% 27.76/4.00  
% 27.76/4.00  fof(f113,plain,(
% 27.76/4.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 27.76/4.00    inference(equality_resolution,[],[f112])).
% 27.76/4.00  
% 27.76/4.00  fof(f50,plain,(
% 27.76/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.76/4.00    inference(cnf_transformation,[],[f32])).
% 27.76/4.00  
% 27.76/4.00  fof(f106,plain,(
% 27.76/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 27.76/4.00    inference(equality_resolution,[],[f50])).
% 27.76/4.00  
% 27.76/4.00  fof(f84,plain,(
% 27.76/4.00    r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0),
% 27.76/4.00    inference(cnf_transformation,[],[f47])).
% 27.76/4.00  
% 27.76/4.00  fof(f104,plain,(
% 27.76/4.00    r2_hidden(sK3,sK5) | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0),
% 27.76/4.00    inference(definition_unfolding,[],[f84,f67,f90])).
% 27.76/4.00  
% 27.76/4.00  fof(f6,axiom,(
% 27.76/4.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f36,plain,(
% 27.76/4.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.76/4.00    inference(nnf_transformation,[],[f6])).
% 27.76/4.00  
% 27.76/4.00  fof(f37,plain,(
% 27.76/4.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.76/4.00    inference(flattening,[],[f36])).
% 27.76/4.00  
% 27.76/4.00  fof(f64,plain,(
% 27.76/4.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f37])).
% 27.76/4.00  
% 27.76/4.00  fof(f74,plain,(
% 27.76/4.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f43])).
% 27.76/4.00  
% 27.76/4.00  fof(f96,plain,(
% 27.76/4.00    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 27.76/4.00    inference(definition_unfolding,[],[f74,f89])).
% 27.76/4.00  
% 27.76/4.00  fof(f53,plain,(
% 27.76/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.76/4.00    inference(cnf_transformation,[],[f32])).
% 27.76/4.00  
% 27.76/4.00  fof(f3,axiom,(
% 27.76/4.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.76/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.76/4.00  
% 27.76/4.00  fof(f20,plain,(
% 27.76/4.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.76/4.00    inference(rectify,[],[f3])).
% 27.76/4.00  
% 27.76/4.00  fof(f55,plain,(
% 27.76/4.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.76/4.00    inference(cnf_transformation,[],[f20])).
% 27.76/4.00  
% 27.76/4.00  fof(f62,plain,(
% 27.76/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.76/4.00    inference(cnf_transformation,[],[f37])).
% 27.76/4.00  
% 27.76/4.00  fof(f109,plain,(
% 27.76/4.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.76/4.00    inference(equality_resolution,[],[f62])).
% 27.76/4.00  
% 27.76/4.00  fof(f71,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.76/4.00    inference(cnf_transformation,[],[f43])).
% 27.76/4.00  
% 27.76/4.00  fof(f99,plain,(
% 27.76/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 27.76/4.00    inference(definition_unfolding,[],[f71,f89])).
% 27.76/4.00  
% 27.76/4.00  fof(f114,plain,(
% 27.76/4.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 27.76/4.00    inference(equality_resolution,[],[f99])).
% 27.76/4.00  
% 27.76/4.00  fof(f115,plain,(
% 27.76/4.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 27.76/4.00    inference(equality_resolution,[],[f114])).
% 27.76/4.00  
% 27.76/4.00  cnf(c_25,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f111]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1235,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_0,plain,
% 27.76/4.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 27.76/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_31,negated_conjecture,
% 27.76/4.00      ( r2_hidden(sK4,sK5)
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1229,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 27.76/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1594,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_0,c_1229]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_29,plain,
% 27.76/4.00      ( ~ r2_hidden(X0,X1)
% 27.76/4.00      | ~ r2_hidden(X2,X1)
% 27.76/4.00      | k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X2) ),
% 27.76/4.00      inference(cnf_transformation,[],[f101]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1231,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
% 27.76/4.00      | r2_hidden(X0,X2) != iProver_top
% 27.76/4.00      | r2_hidden(X1,X2) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_3074,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)
% 27.76/4.00      | r2_hidden(X0,sK5) != iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1594,c_1231]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_3836,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1594,c_3074]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_18,plain,
% 27.76/4.00      ( r1_tarski(X0,X1)
% 27.76/4.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f92]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1240,plain,
% 27.76/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 27.76/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_2619,plain,
% 27.76/4.00      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != k1_xboole_0
% 27.76/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_0,c_1240]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_4032,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_3836,c_2619]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_17,plain,
% 27.76/4.00      ( ~ r1_tarski(X0,X1)
% 27.76/4.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1241,plain,
% 27.76/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 27.76/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5807,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4032,c_1241]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_30,negated_conjecture,
% 27.76/4.00      ( ~ r2_hidden(sK3,sK5)
% 27.76/4.00      | ~ r2_hidden(sK4,sK5)
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1230,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1596,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_0,c_1230]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_9,plain,
% 27.76/4.00      ( ~ r2_hidden(X0,X1)
% 27.76/4.00      | r2_hidden(X0,X2)
% 27.76/4.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f58]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1246,plain,
% 27.76/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.76/4.00      | r2_hidden(X0,X2) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5611,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_3836,c_1246]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_12,plain,
% 27.76/4.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f61]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_20,plain,
% 27.76/4.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 27.76/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_392,plain,
% 27.76/4.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 27.76/4.00      | X3 != X1
% 27.76/4.00      | k1_xboole_0 != X2 ),
% 27.76/4.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_393,plain,
% 27.76/4.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 27.76/4.00      inference(unflattening,[status(thm)],[c_392]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1226,plain,
% 27.76/4.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_19,plain,
% 27.76/4.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1262,plain,
% 27.76/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_1226,c_19]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7591,plain,
% 27.76/4.00      ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5611,c_1262]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7592,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 27.76/4.00      inference(renaming,[status(thm)],[c_7591]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_6,plain,
% 27.76/4.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f107]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1248,plain,
% 27.76/4.00      ( r2_hidden(X0,X1) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7604,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_7592,c_1248]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_32913,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1235,c_7604]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_26,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f113]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1234,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_32914,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1234,c_7604]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_33285,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5807,c_1596,c_3836,c_32913,c_32914]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5,plain,
% 27.76/4.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f106]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1249,plain,
% 27.76/4.00      ( r2_hidden(X0,X1) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_33299,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_33285,c_1249]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_145848,plain,
% 27.76/4.00      ( r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1235,c_33299]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_32,negated_conjecture,
% 27.76/4.00      ( r2_hidden(sK3,sK5)
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f104]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1228,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1595,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_0,c_1228]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_3075,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0)
% 27.76/4.00      | r2_hidden(X0,sK5) != iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1595,c_1231]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_4467,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1595,c_3075]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_4896,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4467,c_2619]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_14,plain,
% 27.76/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.76/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1243,plain,
% 27.76/4.00      ( X0 = X1
% 27.76/4.00      | r1_tarski(X0,X1) != iProver_top
% 27.76/4.00      | r1_tarski(X1,X0) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5900,plain,
% 27.76/4.00      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = sK5
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r1_tarski(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4896,c_1243]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5608,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4467,c_1246]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_6773,plain,
% 27.76/4.00      ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5608,c_1262]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_6774,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 27.76/4.00      inference(renaming,[status(thm)],[c_6773]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_6786,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_6774,c_1248]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_29301,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1235,c_6786]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_29302,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1234,c_6786]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_24,plain,
% 27.76/4.00      ( r2_hidden(sK2(X0,X1,X2,X3),X3)
% 27.76/4.00      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X2
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X1
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1236,plain,
% 27.76/4.00      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = X3
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X2
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X1
% 27.76/4.00      | sK2(X0,X1,X2,X3) = X0
% 27.76/4.00      | r2_hidden(sK2(X0,X1,X2,X3),X3) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_6012,plain,
% 27.76/4.00      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = sK5
% 27.76/4.00      | sK2(X0,X1,X2,sK5) = X2
% 27.76/4.00      | sK2(X0,X1,X2,sK5) = X1
% 27.76/4.00      | sK2(X0,X1,X2,sK5) = X0
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(X0,X1,X2,sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(X0,X1,X2,sK5)) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1236,c_3074]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_2,plain,
% 27.76/4.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 27.76/4.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.76/4.00      | k3_xboole_0(X0,X1) = X2 ),
% 27.76/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1252,plain,
% 27.76/4.00      ( k3_xboole_0(X0,X1) = X2
% 27.76/4.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 27.76/4.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_8901,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(X0,sK5) = X1
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,X1)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,X1))
% 27.76/4.00      | r2_hidden(sK0(X0,sK5,X1),X1) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1252,c_3074]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_14327,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(X0,sK5) = sK5
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_8901,c_3074]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_14459,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(X0,sK5) = sK5
% 27.76/4.00      | k3_xboole_0(sK5,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5))) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_14327,c_0]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_23303,plain,
% 27.76/4.00      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) = k3_xboole_0(sK5,sK5)
% 27.76/4.00      | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK0(X0,sK5,sK5)
% 27.76/4.00      | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK4
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(X0,sK5) = sK5
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_6012,c_14459]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7,plain,
% 27.76/4.00      ( k3_xboole_0(X0,X0) = X0 ),
% 27.76/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_23350,plain,
% 27.76/4.00      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK0(X0,sK5,sK5)) = sK5
% 27.76/4.00      | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK0(X0,sK5,sK5)
% 27.76/4.00      | sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5) = sK4
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(X0,sK5) = sK5
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)),sK5) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK2(sK4,sK4,sK0(X0,sK5,sK5),sK5)) ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_23303,c_7]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_4466,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1594,c_3075]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_4884,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4466,c_2619]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5884,plain,
% 27.76/4.00      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = sK5
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r1_tarski(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4884,c_1243]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_35,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5885,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4884,c_1241]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_5609,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_4466,c_1246]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7033,plain,
% 27.76/4.00      ( r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5609,c_1262]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7034,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 27.76/4.00      inference(renaming,[status(thm)],[c_7033]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_7046,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_7034,c_1248]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_29911,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1235,c_7046]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_29912,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1234,c_7046]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50909,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5884,c_35,c_5885,c_29911,c_29912]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50921,plain,
% 27.76/4.00      ( k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_50909,c_0]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51080,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_50921,c_1596]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_16,plain,
% 27.76/4.00      ( r1_tarski(X0,X0) ),
% 27.76/4.00      inference(cnf_transformation,[],[f109]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_1242,plain,
% 27.76/4.00      ( r1_tarski(X0,X0) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_2862,plain,
% 27.76/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_1242,c_1241]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_2863,plain,
% 27.76/4.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.76/4.00      inference(light_normalisation,[status(thm)],[c_2862,c_7]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51084,plain,
% 27.76/4.00      ( k1_xboole_0 != k1_xboole_0
% 27.76/4.00      | r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_51080,c_2863]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51085,plain,
% 27.76/4.00      ( r2_hidden(sK3,sK5) != iProver_top
% 27.76/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.76/4.00      inference(equality_resolution_simp,[status(thm)],[c_51084]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51726,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0 ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_23350,c_1594,c_1595,c_51085]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51792,plain,
% 27.76/4.00      ( k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 27.76/4.00      inference(global_propositional_subsumption,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_5900,c_1594,c_1595,c_1596,c_29301,c_29302,c_51085]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51802,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 27.76/4.00      | r2_hidden(X0,sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_51792,c_1249]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51837,plain,
% 27.76/4.00      ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 27.76/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 27.76/4.00      inference(instantiation,[status(thm)],[c_51802]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_51575,plain,
% 27.76/4.00      ( ~ r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)
% 27.76/4.00      | k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
% 27.76/4.00      inference(instantiation,[status(thm)],[c_17]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50918,plain,
% 27.76/4.00      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
% 27.76/4.00      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(superposition,[status(thm)],[c_50909,c_1240]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50953,plain,
% 27.76/4.00      ( k1_xboole_0 != k1_xboole_0
% 27.76/4.00      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(demodulation,[status(thm)],[c_50918,c_2863]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50954,plain,
% 27.76/4.00      ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) = iProver_top ),
% 27.76/4.00      inference(equality_resolution_simp,[status(thm)],[c_50953]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_50994,plain,
% 27.76/4.00      ( r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4),sK5) ),
% 27.76/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_50954]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_27,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 27.76/4.00      inference(cnf_transformation,[],[f115]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_42,plain,
% 27.76/4.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 27.76/4.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(c_44,plain,
% 27.76/4.00      ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 27.76/4.00      inference(instantiation,[status(thm)],[c_42]) ).
% 27.76/4.00  
% 27.76/4.00  cnf(contradiction,plain,
% 27.76/4.00      ( $false ),
% 27.76/4.00      inference(minisat,
% 27.76/4.00                [status(thm)],
% 27.76/4.00                [c_145848,c_51837,c_51575,c_50994,c_44,c_35]) ).
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.76/4.00  
% 27.76/4.00  ------                               Statistics
% 27.76/4.00  
% 27.76/4.00  ------ General
% 27.76/4.00  
% 27.76/4.00  abstr_ref_over_cycles:                  0
% 27.76/4.00  abstr_ref_under_cycles:                 0
% 27.76/4.00  gc_basic_clause_elim:                   0
% 27.76/4.00  forced_gc_time:                         0
% 27.76/4.00  parsing_time:                           0.007
% 27.76/4.00  unif_index_cands_time:                  0.
% 27.76/4.00  unif_index_add_time:                    0.
% 27.76/4.00  orderings_time:                         0.
% 27.76/4.00  out_proof_time:                         0.019
% 27.76/4.00  total_time:                             3.36
% 27.76/4.00  num_of_symbols:                         44
% 27.76/4.00  num_of_terms:                           114812
% 27.76/4.00  
% 27.76/4.00  ------ Preprocessing
% 27.76/4.00  
% 27.76/4.00  num_of_splits:                          0
% 27.76/4.00  num_of_split_atoms:                     0
% 27.76/4.00  num_of_reused_defs:                     0
% 27.76/4.00  num_eq_ax_congr_red:                    34
% 27.76/4.00  num_of_sem_filtered_clauses:            1
% 27.76/4.00  num_of_subtypes:                        0
% 27.76/4.00  monotx_restored_types:                  0
% 27.76/4.00  sat_num_of_epr_types:                   0
% 27.76/4.00  sat_num_of_non_cyclic_types:            0
% 27.76/4.00  sat_guarded_non_collapsed_types:        0
% 27.76/4.00  num_pure_diseq_elim:                    0
% 27.76/4.00  simp_replaced_by:                       0
% 27.76/4.00  res_preprocessed:                       138
% 27.76/4.00  prep_upred:                             0
% 27.76/4.00  prep_unflattend:                        2
% 27.76/4.00  smt_new_axioms:                         0
% 27.76/4.00  pred_elim_cands:                        2
% 27.76/4.00  pred_elim:                              1
% 27.76/4.00  pred_elim_cl:                           1
% 27.76/4.00  pred_elim_cycles:                       3
% 27.76/4.00  merged_defs:                            8
% 27.76/4.00  merged_defs_ncl:                        0
% 27.76/4.00  bin_hyper_res:                          8
% 27.76/4.00  prep_cycles:                            4
% 27.76/4.00  pred_elim_time:                         0.
% 27.76/4.00  splitting_time:                         0.
% 27.76/4.00  sem_filter_time:                        0.
% 27.76/4.00  monotx_time:                            0.
% 27.76/4.00  subtype_inf_time:                       0.
% 27.76/4.00  
% 27.76/4.00  ------ Problem properties
% 27.76/4.00  
% 27.76/4.00  clauses:                                31
% 27.76/4.00  conjectures:                            3
% 27.76/4.00  epr:                                    2
% 27.76/4.00  horn:                                   22
% 27.76/4.00  ground:                                 3
% 27.76/4.00  unary:                                  8
% 27.76/4.00  binary:                                 7
% 27.76/4.00  lits:                                   74
% 27.76/4.00  lits_eq:                                26
% 27.76/4.00  fd_pure:                                0
% 27.76/4.00  fd_pseudo:                              0
% 27.76/4.00  fd_cond:                                0
% 27.76/4.00  fd_pseudo_cond:                         8
% 27.76/4.00  ac_symbols:                             0
% 27.76/4.00  
% 27.76/4.00  ------ Propositional Solver
% 27.76/4.00  
% 27.76/4.00  prop_solver_calls:                      34
% 27.76/4.00  prop_fast_solver_calls:                 4550
% 27.76/4.00  smt_solver_calls:                       0
% 27.76/4.00  smt_fast_solver_calls:                  0
% 27.76/4.00  prop_num_of_clauses:                    32439
% 27.76/4.00  prop_preprocess_simplified:             68478
% 27.76/4.00  prop_fo_subsumed:                       1697
% 27.76/4.00  prop_solver_time:                       0.
% 27.76/4.00  smt_solver_time:                        0.
% 27.76/4.00  smt_fast_solver_time:                   0.
% 27.76/4.00  prop_fast_solver_time:                  0.
% 27.76/4.00  prop_unsat_core_time:                   0.003
% 27.76/4.00  
% 27.76/4.00  ------ QBF
% 27.76/4.00  
% 27.76/4.00  qbf_q_res:                              0
% 27.76/4.00  qbf_num_tautologies:                    0
% 27.76/4.00  qbf_prep_cycles:                        0
% 27.76/4.00  
% 27.76/4.00  ------ BMC1
% 27.76/4.00  
% 27.76/4.00  bmc1_current_bound:                     -1
% 27.76/4.00  bmc1_last_solved_bound:                 -1
% 27.76/4.00  bmc1_unsat_core_size:                   -1
% 27.76/4.00  bmc1_unsat_core_parents_size:           -1
% 27.76/4.00  bmc1_merge_next_fun:                    0
% 27.76/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.76/4.00  
% 27.76/4.00  ------ Instantiation
% 27.76/4.00  
% 27.76/4.00  inst_num_of_clauses:                    6172
% 27.76/4.00  inst_num_in_passive:                    5119
% 27.76/4.00  inst_num_in_active:                     1051
% 27.76/4.00  inst_num_in_unprocessed:                2
% 27.76/4.00  inst_num_of_loops:                      1860
% 27.76/4.00  inst_num_of_learning_restarts:          0
% 27.76/4.00  inst_num_moves_active_passive:          802
% 27.76/4.00  inst_lit_activity:                      0
% 27.76/4.00  inst_lit_activity_moves:                3
% 27.76/4.00  inst_num_tautologies:                   0
% 27.76/4.00  inst_num_prop_implied:                  0
% 27.76/4.00  inst_num_existing_simplified:           0
% 27.76/4.00  inst_num_eq_res_simplified:             0
% 27.76/4.00  inst_num_child_elim:                    0
% 27.76/4.00  inst_num_of_dismatching_blockings:      19360
% 27.76/4.00  inst_num_of_non_proper_insts:           6455
% 27.76/4.00  inst_num_of_duplicates:                 0
% 27.76/4.00  inst_inst_num_from_inst_to_res:         0
% 27.76/4.00  inst_dismatching_checking_time:         0.
% 27.76/4.00  
% 27.76/4.00  ------ Resolution
% 27.76/4.00  
% 27.76/4.00  res_num_of_clauses:                     0
% 27.76/4.00  res_num_in_passive:                     0
% 27.76/4.00  res_num_in_active:                      0
% 27.76/4.00  res_num_of_loops:                       142
% 27.76/4.00  res_forward_subset_subsumed:            1015
% 27.76/4.00  res_backward_subset_subsumed:           12
% 27.76/4.00  res_forward_subsumed:                   0
% 27.76/4.00  res_backward_subsumed:                  0
% 27.76/4.00  res_forward_subsumption_resolution:     0
% 27.76/4.00  res_backward_subsumption_resolution:    0
% 27.76/4.00  res_clause_to_clause_subsumption:       119301
% 27.76/4.00  res_orphan_elimination:                 0
% 27.76/4.00  res_tautology_del:                      338
% 27.76/4.00  res_num_eq_res_simplified:              0
% 27.76/4.00  res_num_sel_changes:                    0
% 27.76/4.00  res_moves_from_active_to_pass:          0
% 27.76/4.00  
% 27.76/4.00  ------ Superposition
% 27.76/4.00  
% 27.76/4.00  sup_time_total:                         0.
% 27.76/4.00  sup_time_generating:                    0.
% 27.76/4.00  sup_time_sim_full:                      0.
% 27.76/4.00  sup_time_sim_immed:                     0.
% 27.76/4.00  
% 27.76/4.00  sup_num_of_clauses:                     5086
% 27.76/4.00  sup_num_in_active:                      266
% 27.76/4.00  sup_num_in_passive:                     4820
% 27.76/4.00  sup_num_of_loops:                       371
% 27.76/4.00  sup_fw_superposition:                   4367
% 27.76/4.00  sup_bw_superposition:                   6160
% 27.76/4.00  sup_immediate_simplified:               2241
% 27.76/4.00  sup_given_eliminated:                   4
% 27.76/4.00  comparisons_done:                       0
% 27.76/4.00  comparisons_avoided:                    1088
% 27.76/4.00  
% 27.76/4.00  ------ Simplifications
% 27.76/4.00  
% 27.76/4.00  
% 27.76/4.00  sim_fw_subset_subsumed:                 242
% 27.76/4.00  sim_bw_subset_subsumed:                 59
% 27.76/4.00  sim_fw_subsumed:                        1009
% 27.76/4.00  sim_bw_subsumed:                        105
% 27.76/4.00  sim_fw_subsumption_res:                 57
% 27.76/4.00  sim_bw_subsumption_res:                 0
% 27.76/4.00  sim_tautology_del:                      208
% 27.76/4.00  sim_eq_tautology_del:                   191
% 27.76/4.00  sim_eq_res_simp:                        84
% 27.76/4.00  sim_fw_demodulated:                     859
% 27.76/4.00  sim_bw_demodulated:                     93
% 27.76/4.00  sim_light_normalised:                   641
% 27.76/4.00  sim_joinable_taut:                      0
% 27.76/4.00  sim_joinable_simp:                      0
% 27.76/4.00  sim_ac_normalised:                      0
% 27.76/4.00  sim_smt_subsumption:                    0
% 27.76/4.00  
%------------------------------------------------------------------------------
