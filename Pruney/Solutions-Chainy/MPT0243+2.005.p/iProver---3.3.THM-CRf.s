%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:54 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 399 expanded)
%              Number of clauses        :   54 ( 130 expanded)
%              Number of leaves         :   16 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  435 (1270 expanded)
%              Number of equality atoms :  168 ( 303 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f68])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r2_hidden(sK3,sK5)
        | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
      & ( ( r2_hidden(sK4,sK5)
          & r2_hidden(sK3,sK5) )
        | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r2_hidden(sK3,sK5)
      | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) )
    & ( ( r2_hidden(sK4,sK5)
        & r2_hidden(sK3,sK5) )
      | r1_tarski(k2_tarski(sK3,sK4),sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).

fof(f74,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(definition_unfolding,[],[f74,f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(definition_unfolding,[],[f75,f68])).

fof(f73,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k2_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(definition_unfolding,[],[f73,f68])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_20,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1247,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1239,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1584,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24,c_1239])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1254,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2609,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_1254])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1264,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8472,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
    | r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2609,c_1264])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1238,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1585,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24,c_1238])).

cnf(c_31,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1514,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X2)
    | r1_tarski(k1_tarski(X0),X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1664,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)
    | r1_tarski(k1_tarski(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_1665,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top
    | r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1732,plain,
    ( r2_hidden(sK3,sK5)
    | ~ r1_tarski(k1_tarski(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1733,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r1_tarski(k1_tarski(sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1732])).

cnf(c_2286,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_31,c_1665,c_1733])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2315,plain,
    ( ~ r2_hidden(sK3,sK5)
    | r1_tarski(k1_tarski(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2316,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1659,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(k1_tarski(X2),X0),X1)
    | ~ r1_tarski(k1_tarski(X2),X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1952,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),X0),sK5)
    | ~ r1_tarski(k1_tarski(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_3726,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)
    | ~ r1_tarski(k1_tarski(sK3),sK5)
    | ~ r1_tarski(k1_tarski(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_3727,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top
    | r1_tarski(k1_tarski(sK3),sK5) != iProver_top
    | r1_tarski(k1_tarski(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3726])).

cnf(c_7041,plain,
    ( ~ r2_hidden(sK4,sK5)
    | r1_tarski(k1_tarski(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7042,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_tarski(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7041])).

cnf(c_9036,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8472,c_31,c_33,c_1665,c_1733,c_2316,c_2609,c_3727,c_7042])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1256,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1255,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2964,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1255])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1253,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3734,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_2964,c_1253])).

cnf(c_9041,plain,
    ( k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_9036,c_3734])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1259,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9424,plain,
    ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_9041,c_1259])).

cnf(c_13787,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_9424])).

cnf(c_9042,plain,
    ( r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_9036,c_2964])).

cnf(c_1240,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1586,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24,c_1240])).

cnf(c_1911,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1586,c_31,c_1665,c_1733])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13787,c_9042,c_1911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:38:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.39/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/0.97  
% 3.39/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.97  
% 3.39/0.97  ------  iProver source info
% 3.39/0.97  
% 3.39/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.97  git: non_committed_changes: false
% 3.39/0.97  git: last_make_outside_of_git: false
% 3.39/0.97  
% 3.39/0.97  ------ 
% 3.39/0.97  
% 3.39/0.97  ------ Input Options
% 3.39/0.97  
% 3.39/0.97  --out_options                           all
% 3.39/0.97  --tptp_safe_out                         true
% 3.39/0.97  --problem_path                          ""
% 3.39/0.97  --include_path                          ""
% 3.39/0.97  --clausifier                            res/vclausify_rel
% 3.39/0.97  --clausifier_options                    --mode clausify
% 3.39/0.97  --stdin                                 false
% 3.39/0.97  --stats_out                             all
% 3.39/0.97  
% 3.39/0.97  ------ General Options
% 3.39/0.97  
% 3.39/0.97  --fof                                   false
% 3.39/0.97  --time_out_real                         305.
% 3.39/0.97  --time_out_virtual                      -1.
% 3.39/0.97  --symbol_type_check                     false
% 3.39/0.97  --clausify_out                          false
% 3.39/0.97  --sig_cnt_out                           false
% 3.39/0.97  --trig_cnt_out                          false
% 3.39/0.97  --trig_cnt_out_tolerance                1.
% 3.39/0.97  --trig_cnt_out_sk_spl                   false
% 3.39/0.97  --abstr_cl_out                          false
% 3.39/0.97  
% 3.39/0.97  ------ Global Options
% 3.39/0.97  
% 3.39/0.97  --schedule                              default
% 3.39/0.97  --add_important_lit                     false
% 3.39/0.97  --prop_solver_per_cl                    1000
% 3.39/0.97  --min_unsat_core                        false
% 3.39/0.97  --soft_assumptions                      false
% 3.39/0.97  --soft_lemma_size                       3
% 3.39/0.97  --prop_impl_unit_size                   0
% 3.39/0.97  --prop_impl_unit                        []
% 3.39/0.97  --share_sel_clauses                     true
% 3.39/0.97  --reset_solvers                         false
% 3.39/0.97  --bc_imp_inh                            [conj_cone]
% 3.39/0.97  --conj_cone_tolerance                   3.
% 3.39/0.97  --extra_neg_conj                        none
% 3.39/0.97  --large_theory_mode                     true
% 3.39/0.97  --prolific_symb_bound                   200
% 3.39/0.97  --lt_threshold                          2000
% 3.39/0.97  --clause_weak_htbl                      true
% 3.39/0.97  --gc_record_bc_elim                     false
% 3.39/0.97  
% 3.39/0.97  ------ Preprocessing Options
% 3.39/0.97  
% 3.39/0.97  --preprocessing_flag                    true
% 3.39/0.97  --time_out_prep_mult                    0.1
% 3.39/0.97  --splitting_mode                        input
% 3.39/0.97  --splitting_grd                         true
% 3.39/0.97  --splitting_cvd                         false
% 3.39/0.97  --splitting_cvd_svl                     false
% 3.39/0.97  --splitting_nvd                         32
% 3.39/0.97  --sub_typing                            true
% 3.39/0.97  --prep_gs_sim                           true
% 3.39/0.97  --prep_unflatten                        true
% 3.39/0.97  --prep_res_sim                          true
% 3.39/0.97  --prep_upred                            true
% 3.39/0.97  --prep_sem_filter                       exhaustive
% 3.39/0.97  --prep_sem_filter_out                   false
% 3.39/0.97  --pred_elim                             true
% 3.39/0.97  --res_sim_input                         true
% 3.39/0.97  --eq_ax_congr_red                       true
% 3.39/0.97  --pure_diseq_elim                       true
% 3.39/0.97  --brand_transform                       false
% 3.39/0.97  --non_eq_to_eq                          false
% 3.39/0.97  --prep_def_merge                        true
% 3.39/0.97  --prep_def_merge_prop_impl              false
% 3.39/0.97  --prep_def_merge_mbd                    true
% 3.39/0.97  --prep_def_merge_tr_red                 false
% 3.39/0.97  --prep_def_merge_tr_cl                  false
% 3.39/0.97  --smt_preprocessing                     true
% 3.39/0.97  --smt_ac_axioms                         fast
% 3.39/0.97  --preprocessed_out                      false
% 3.39/0.97  --preprocessed_stats                    false
% 3.39/0.97  
% 3.39/0.97  ------ Abstraction refinement Options
% 3.39/0.97  
% 3.39/0.97  --abstr_ref                             []
% 3.39/0.97  --abstr_ref_prep                        false
% 3.39/0.97  --abstr_ref_until_sat                   false
% 3.39/0.97  --abstr_ref_sig_restrict                funpre
% 3.39/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.97  --abstr_ref_under                       []
% 3.39/0.97  
% 3.39/0.97  ------ SAT Options
% 3.39/0.97  
% 3.39/0.97  --sat_mode                              false
% 3.39/0.97  --sat_fm_restart_options                ""
% 3.39/0.97  --sat_gr_def                            false
% 3.39/0.97  --sat_epr_types                         true
% 3.39/0.97  --sat_non_cyclic_types                  false
% 3.39/0.97  --sat_finite_models                     false
% 3.39/0.97  --sat_fm_lemmas                         false
% 3.39/0.97  --sat_fm_prep                           false
% 3.39/0.97  --sat_fm_uc_incr                        true
% 3.39/0.97  --sat_out_model                         small
% 3.39/0.97  --sat_out_clauses                       false
% 3.39/0.97  
% 3.39/0.97  ------ QBF Options
% 3.39/0.97  
% 3.39/0.97  --qbf_mode                              false
% 3.39/0.97  --qbf_elim_univ                         false
% 3.39/0.97  --qbf_dom_inst                          none
% 3.39/0.97  --qbf_dom_pre_inst                      false
% 3.39/0.97  --qbf_sk_in                             false
% 3.39/0.97  --qbf_pred_elim                         true
% 3.39/0.97  --qbf_split                             512
% 3.39/0.97  
% 3.39/0.97  ------ BMC1 Options
% 3.39/0.97  
% 3.39/0.97  --bmc1_incremental                      false
% 3.39/0.97  --bmc1_axioms                           reachable_all
% 3.39/0.97  --bmc1_min_bound                        0
% 3.39/0.97  --bmc1_max_bound                        -1
% 3.39/0.97  --bmc1_max_bound_default                -1
% 3.39/0.97  --bmc1_symbol_reachability              true
% 3.39/0.97  --bmc1_property_lemmas                  false
% 3.39/0.97  --bmc1_k_induction                      false
% 3.39/0.97  --bmc1_non_equiv_states                 false
% 3.39/0.97  --bmc1_deadlock                         false
% 3.39/0.97  --bmc1_ucm                              false
% 3.39/0.97  --bmc1_add_unsat_core                   none
% 3.39/0.97  --bmc1_unsat_core_children              false
% 3.39/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.97  --bmc1_out_stat                         full
% 3.39/0.97  --bmc1_ground_init                      false
% 3.39/0.97  --bmc1_pre_inst_next_state              false
% 3.39/0.97  --bmc1_pre_inst_state                   false
% 3.39/0.97  --bmc1_pre_inst_reach_state             false
% 3.39/0.97  --bmc1_out_unsat_core                   false
% 3.39/0.97  --bmc1_aig_witness_out                  false
% 3.39/0.97  --bmc1_verbose                          false
% 3.39/0.97  --bmc1_dump_clauses_tptp                false
% 3.39/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.97  --bmc1_dump_file                        -
% 3.39/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.97  --bmc1_ucm_extend_mode                  1
% 3.39/0.97  --bmc1_ucm_init_mode                    2
% 3.39/0.97  --bmc1_ucm_cone_mode                    none
% 3.39/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.97  --bmc1_ucm_relax_model                  4
% 3.39/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.97  --bmc1_ucm_layered_model                none
% 3.39/0.97  --bmc1_ucm_max_lemma_size               10
% 3.39/0.97  
% 3.39/0.97  ------ AIG Options
% 3.39/0.97  
% 3.39/0.97  --aig_mode                              false
% 3.39/0.97  
% 3.39/0.97  ------ Instantiation Options
% 3.39/0.97  
% 3.39/0.97  --instantiation_flag                    true
% 3.39/0.97  --inst_sos_flag                         false
% 3.39/0.97  --inst_sos_phase                        true
% 3.39/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.97  --inst_lit_sel_side                     num_symb
% 3.39/0.97  --inst_solver_per_active                1400
% 3.39/0.97  --inst_solver_calls_frac                1.
% 3.39/0.97  --inst_passive_queue_type               priority_queues
% 3.39/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.97  --inst_passive_queues_freq              [25;2]
% 3.39/0.97  --inst_dismatching                      true
% 3.39/0.97  --inst_eager_unprocessed_to_passive     true
% 3.39/0.97  --inst_prop_sim_given                   true
% 3.39/0.97  --inst_prop_sim_new                     false
% 3.39/0.97  --inst_subs_new                         false
% 3.39/0.97  --inst_eq_res_simp                      false
% 3.39/0.97  --inst_subs_given                       false
% 3.39/0.97  --inst_orphan_elimination               true
% 3.39/0.97  --inst_learning_loop_flag               true
% 3.39/0.97  --inst_learning_start                   3000
% 3.39/0.97  --inst_learning_factor                  2
% 3.39/0.97  --inst_start_prop_sim_after_learn       3
% 3.39/0.97  --inst_sel_renew                        solver
% 3.39/0.97  --inst_lit_activity_flag                true
% 3.39/0.97  --inst_restr_to_given                   false
% 3.39/0.97  --inst_activity_threshold               500
% 3.39/0.97  --inst_out_proof                        true
% 3.39/0.97  
% 3.39/0.97  ------ Resolution Options
% 3.39/0.97  
% 3.39/0.97  --resolution_flag                       true
% 3.39/0.97  --res_lit_sel                           adaptive
% 3.39/0.97  --res_lit_sel_side                      none
% 3.39/0.97  --res_ordering                          kbo
% 3.39/0.97  --res_to_prop_solver                    active
% 3.39/0.97  --res_prop_simpl_new                    false
% 3.39/0.97  --res_prop_simpl_given                  true
% 3.39/0.97  --res_passive_queue_type                priority_queues
% 3.39/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.97  --res_passive_queues_freq               [15;5]
% 3.39/0.97  --res_forward_subs                      full
% 3.39/0.97  --res_backward_subs                     full
% 3.39/0.97  --res_forward_subs_resolution           true
% 3.39/0.97  --res_backward_subs_resolution          true
% 3.39/0.97  --res_orphan_elimination                true
% 3.39/0.97  --res_time_limit                        2.
% 3.39/0.97  --res_out_proof                         true
% 3.39/0.97  
% 3.39/0.97  ------ Superposition Options
% 3.39/0.97  
% 3.39/0.97  --superposition_flag                    true
% 3.39/0.97  --sup_passive_queue_type                priority_queues
% 3.39/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.97  --demod_completeness_check              fast
% 3.39/0.97  --demod_use_ground                      true
% 3.39/0.97  --sup_to_prop_solver                    passive
% 3.39/0.97  --sup_prop_simpl_new                    true
% 3.39/0.97  --sup_prop_simpl_given                  true
% 3.39/0.97  --sup_fun_splitting                     false
% 3.39/0.97  --sup_smt_interval                      50000
% 3.39/0.97  
% 3.39/0.97  ------ Superposition Simplification Setup
% 3.39/0.97  
% 3.39/0.97  --sup_indices_passive                   []
% 3.39/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_full_bw                           [BwDemod]
% 3.39/0.97  --sup_immed_triv                        [TrivRules]
% 3.39/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_immed_bw_main                     []
% 3.39/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.97  
% 3.39/0.97  ------ Combination Options
% 3.39/0.97  
% 3.39/0.97  --comb_res_mult                         3
% 3.39/0.97  --comb_sup_mult                         2
% 3.39/0.97  --comb_inst_mult                        10
% 3.39/0.97  
% 3.39/0.97  ------ Debug Options
% 3.39/0.97  
% 3.39/0.97  --dbg_backtrace                         false
% 3.39/0.97  --dbg_dump_prop_clauses                 false
% 3.39/0.97  --dbg_dump_prop_clauses_file            -
% 3.39/0.97  --dbg_out_stat                          false
% 3.39/0.97  ------ Parsing...
% 3.39/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.97  
% 3.39/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.39/0.97  
% 3.39/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.97  
% 3.39/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.97  ------ Proving...
% 3.39/0.97  ------ Problem Properties 
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  clauses                                 30
% 3.39/0.97  conjectures                             3
% 3.39/0.97  EPR                                     3
% 3.39/0.97  Horn                                    23
% 3.39/0.97  unary                                   6
% 3.39/0.97  binary                                  11
% 3.39/0.97  lits                                    71
% 3.39/0.97  lits eq                                 20
% 3.39/0.97  fd_pure                                 0
% 3.39/0.97  fd_pseudo                               0
% 3.39/0.97  fd_cond                                 0
% 3.39/0.97  fd_pseudo_cond                          8
% 3.39/0.97  AC symbols                              0
% 3.39/0.97  
% 3.39/0.97  ------ Schedule dynamic 5 is on 
% 3.39/0.97  
% 3.39/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  ------ 
% 3.39/0.97  Current options:
% 3.39/0.97  ------ 
% 3.39/0.97  
% 3.39/0.97  ------ Input Options
% 3.39/0.97  
% 3.39/0.97  --out_options                           all
% 3.39/0.97  --tptp_safe_out                         true
% 3.39/0.97  --problem_path                          ""
% 3.39/0.97  --include_path                          ""
% 3.39/0.97  --clausifier                            res/vclausify_rel
% 3.39/0.97  --clausifier_options                    --mode clausify
% 3.39/0.97  --stdin                                 false
% 3.39/0.97  --stats_out                             all
% 3.39/0.97  
% 3.39/0.97  ------ General Options
% 3.39/0.97  
% 3.39/0.97  --fof                                   false
% 3.39/0.97  --time_out_real                         305.
% 3.39/0.97  --time_out_virtual                      -1.
% 3.39/0.97  --symbol_type_check                     false
% 3.39/0.97  --clausify_out                          false
% 3.39/0.97  --sig_cnt_out                           false
% 3.39/0.97  --trig_cnt_out                          false
% 3.39/0.97  --trig_cnt_out_tolerance                1.
% 3.39/0.97  --trig_cnt_out_sk_spl                   false
% 3.39/0.97  --abstr_cl_out                          false
% 3.39/0.97  
% 3.39/0.97  ------ Global Options
% 3.39/0.97  
% 3.39/0.97  --schedule                              default
% 3.39/0.97  --add_important_lit                     false
% 3.39/0.97  --prop_solver_per_cl                    1000
% 3.39/0.97  --min_unsat_core                        false
% 3.39/0.97  --soft_assumptions                      false
% 3.39/0.97  --soft_lemma_size                       3
% 3.39/0.97  --prop_impl_unit_size                   0
% 3.39/0.97  --prop_impl_unit                        []
% 3.39/0.97  --share_sel_clauses                     true
% 3.39/0.97  --reset_solvers                         false
% 3.39/0.97  --bc_imp_inh                            [conj_cone]
% 3.39/0.97  --conj_cone_tolerance                   3.
% 3.39/0.97  --extra_neg_conj                        none
% 3.39/0.97  --large_theory_mode                     true
% 3.39/0.97  --prolific_symb_bound                   200
% 3.39/0.97  --lt_threshold                          2000
% 3.39/0.97  --clause_weak_htbl                      true
% 3.39/0.97  --gc_record_bc_elim                     false
% 3.39/0.97  
% 3.39/0.97  ------ Preprocessing Options
% 3.39/0.97  
% 3.39/0.97  --preprocessing_flag                    true
% 3.39/0.97  --time_out_prep_mult                    0.1
% 3.39/0.97  --splitting_mode                        input
% 3.39/0.97  --splitting_grd                         true
% 3.39/0.97  --splitting_cvd                         false
% 3.39/0.97  --splitting_cvd_svl                     false
% 3.39/0.97  --splitting_nvd                         32
% 3.39/0.97  --sub_typing                            true
% 3.39/0.97  --prep_gs_sim                           true
% 3.39/0.97  --prep_unflatten                        true
% 3.39/0.97  --prep_res_sim                          true
% 3.39/0.97  --prep_upred                            true
% 3.39/0.97  --prep_sem_filter                       exhaustive
% 3.39/0.97  --prep_sem_filter_out                   false
% 3.39/0.97  --pred_elim                             true
% 3.39/0.97  --res_sim_input                         true
% 3.39/0.97  --eq_ax_congr_red                       true
% 3.39/0.97  --pure_diseq_elim                       true
% 3.39/0.97  --brand_transform                       false
% 3.39/0.97  --non_eq_to_eq                          false
% 3.39/0.97  --prep_def_merge                        true
% 3.39/0.97  --prep_def_merge_prop_impl              false
% 3.39/0.97  --prep_def_merge_mbd                    true
% 3.39/0.97  --prep_def_merge_tr_red                 false
% 3.39/0.97  --prep_def_merge_tr_cl                  false
% 3.39/0.97  --smt_preprocessing                     true
% 3.39/0.97  --smt_ac_axioms                         fast
% 3.39/0.97  --preprocessed_out                      false
% 3.39/0.97  --preprocessed_stats                    false
% 3.39/0.97  
% 3.39/0.97  ------ Abstraction refinement Options
% 3.39/0.97  
% 3.39/0.97  --abstr_ref                             []
% 3.39/0.97  --abstr_ref_prep                        false
% 3.39/0.97  --abstr_ref_until_sat                   false
% 3.39/0.97  --abstr_ref_sig_restrict                funpre
% 3.39/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.97  --abstr_ref_under                       []
% 3.39/0.97  
% 3.39/0.97  ------ SAT Options
% 3.39/0.97  
% 3.39/0.97  --sat_mode                              false
% 3.39/0.97  --sat_fm_restart_options                ""
% 3.39/0.97  --sat_gr_def                            false
% 3.39/0.97  --sat_epr_types                         true
% 3.39/0.97  --sat_non_cyclic_types                  false
% 3.39/0.97  --sat_finite_models                     false
% 3.39/0.97  --sat_fm_lemmas                         false
% 3.39/0.97  --sat_fm_prep                           false
% 3.39/0.97  --sat_fm_uc_incr                        true
% 3.39/0.97  --sat_out_model                         small
% 3.39/0.97  --sat_out_clauses                       false
% 3.39/0.97  
% 3.39/0.97  ------ QBF Options
% 3.39/0.97  
% 3.39/0.97  --qbf_mode                              false
% 3.39/0.97  --qbf_elim_univ                         false
% 3.39/0.97  --qbf_dom_inst                          none
% 3.39/0.97  --qbf_dom_pre_inst                      false
% 3.39/0.97  --qbf_sk_in                             false
% 3.39/0.97  --qbf_pred_elim                         true
% 3.39/0.97  --qbf_split                             512
% 3.39/0.97  
% 3.39/0.97  ------ BMC1 Options
% 3.39/0.97  
% 3.39/0.97  --bmc1_incremental                      false
% 3.39/0.97  --bmc1_axioms                           reachable_all
% 3.39/0.97  --bmc1_min_bound                        0
% 3.39/0.97  --bmc1_max_bound                        -1
% 3.39/0.97  --bmc1_max_bound_default                -1
% 3.39/0.97  --bmc1_symbol_reachability              true
% 3.39/0.97  --bmc1_property_lemmas                  false
% 3.39/0.97  --bmc1_k_induction                      false
% 3.39/0.97  --bmc1_non_equiv_states                 false
% 3.39/0.97  --bmc1_deadlock                         false
% 3.39/0.97  --bmc1_ucm                              false
% 3.39/0.97  --bmc1_add_unsat_core                   none
% 3.39/0.97  --bmc1_unsat_core_children              false
% 3.39/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.97  --bmc1_out_stat                         full
% 3.39/0.97  --bmc1_ground_init                      false
% 3.39/0.97  --bmc1_pre_inst_next_state              false
% 3.39/0.97  --bmc1_pre_inst_state                   false
% 3.39/0.97  --bmc1_pre_inst_reach_state             false
% 3.39/0.97  --bmc1_out_unsat_core                   false
% 3.39/0.97  --bmc1_aig_witness_out                  false
% 3.39/0.97  --bmc1_verbose                          false
% 3.39/0.97  --bmc1_dump_clauses_tptp                false
% 3.39/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.97  --bmc1_dump_file                        -
% 3.39/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.97  --bmc1_ucm_extend_mode                  1
% 3.39/0.97  --bmc1_ucm_init_mode                    2
% 3.39/0.97  --bmc1_ucm_cone_mode                    none
% 3.39/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.97  --bmc1_ucm_relax_model                  4
% 3.39/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.97  --bmc1_ucm_layered_model                none
% 3.39/0.97  --bmc1_ucm_max_lemma_size               10
% 3.39/0.97  
% 3.39/0.97  ------ AIG Options
% 3.39/0.97  
% 3.39/0.97  --aig_mode                              false
% 3.39/0.97  
% 3.39/0.97  ------ Instantiation Options
% 3.39/0.97  
% 3.39/0.97  --instantiation_flag                    true
% 3.39/0.97  --inst_sos_flag                         false
% 3.39/0.97  --inst_sos_phase                        true
% 3.39/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.97  --inst_lit_sel_side                     none
% 3.39/0.97  --inst_solver_per_active                1400
% 3.39/0.97  --inst_solver_calls_frac                1.
% 3.39/0.97  --inst_passive_queue_type               priority_queues
% 3.39/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.97  --inst_passive_queues_freq              [25;2]
% 3.39/0.97  --inst_dismatching                      true
% 3.39/0.97  --inst_eager_unprocessed_to_passive     true
% 3.39/0.97  --inst_prop_sim_given                   true
% 3.39/0.97  --inst_prop_sim_new                     false
% 3.39/0.97  --inst_subs_new                         false
% 3.39/0.97  --inst_eq_res_simp                      false
% 3.39/0.97  --inst_subs_given                       false
% 3.39/0.97  --inst_orphan_elimination               true
% 3.39/0.97  --inst_learning_loop_flag               true
% 3.39/0.97  --inst_learning_start                   3000
% 3.39/0.97  --inst_learning_factor                  2
% 3.39/0.97  --inst_start_prop_sim_after_learn       3
% 3.39/0.97  --inst_sel_renew                        solver
% 3.39/0.97  --inst_lit_activity_flag                true
% 3.39/0.97  --inst_restr_to_given                   false
% 3.39/0.97  --inst_activity_threshold               500
% 3.39/0.97  --inst_out_proof                        true
% 3.39/0.97  
% 3.39/0.97  ------ Resolution Options
% 3.39/0.97  
% 3.39/0.97  --resolution_flag                       false
% 3.39/0.97  --res_lit_sel                           adaptive
% 3.39/0.97  --res_lit_sel_side                      none
% 3.39/0.97  --res_ordering                          kbo
% 3.39/0.97  --res_to_prop_solver                    active
% 3.39/0.97  --res_prop_simpl_new                    false
% 3.39/0.97  --res_prop_simpl_given                  true
% 3.39/0.97  --res_passive_queue_type                priority_queues
% 3.39/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.97  --res_passive_queues_freq               [15;5]
% 3.39/0.97  --res_forward_subs                      full
% 3.39/0.97  --res_backward_subs                     full
% 3.39/0.97  --res_forward_subs_resolution           true
% 3.39/0.97  --res_backward_subs_resolution          true
% 3.39/0.97  --res_orphan_elimination                true
% 3.39/0.97  --res_time_limit                        2.
% 3.39/0.97  --res_out_proof                         true
% 3.39/0.97  
% 3.39/0.97  ------ Superposition Options
% 3.39/0.97  
% 3.39/0.97  --superposition_flag                    true
% 3.39/0.97  --sup_passive_queue_type                priority_queues
% 3.39/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.97  --demod_completeness_check              fast
% 3.39/0.97  --demod_use_ground                      true
% 3.39/0.97  --sup_to_prop_solver                    passive
% 3.39/0.97  --sup_prop_simpl_new                    true
% 3.39/0.97  --sup_prop_simpl_given                  true
% 3.39/0.97  --sup_fun_splitting                     false
% 3.39/0.97  --sup_smt_interval                      50000
% 3.39/0.97  
% 3.39/0.97  ------ Superposition Simplification Setup
% 3.39/0.97  
% 3.39/0.97  --sup_indices_passive                   []
% 3.39/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_full_bw                           [BwDemod]
% 3.39/0.97  --sup_immed_triv                        [TrivRules]
% 3.39/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_immed_bw_main                     []
% 3.39/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.97  
% 3.39/0.97  ------ Combination Options
% 3.39/0.97  
% 3.39/0.97  --comb_res_mult                         3
% 3.39/0.97  --comb_sup_mult                         2
% 3.39/0.97  --comb_inst_mult                        10
% 3.39/0.97  
% 3.39/0.97  ------ Debug Options
% 3.39/0.97  
% 3.39/0.97  --dbg_backtrace                         false
% 3.39/0.97  --dbg_dump_prop_clauses                 false
% 3.39/0.97  --dbg_dump_prop_clauses_file            -
% 3.39/0.97  --dbg_out_stat                          false
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  ------ Proving...
% 3.39/0.97  
% 3.39/0.97  
% 3.39/0.97  % SZS status Theorem for theBenchmark.p
% 3.39/0.97  
% 3.39/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.97  
% 3.39/0.97  fof(f8,axiom,(
% 3.39/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f21,plain,(
% 3.39/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.39/0.97    inference(ennf_transformation,[],[f8])).
% 3.39/0.97  
% 3.39/0.97  fof(f34,plain,(
% 3.39/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.39/0.97    inference(nnf_transformation,[],[f21])).
% 3.39/0.97  
% 3.39/0.97  fof(f35,plain,(
% 3.39/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.39/0.97    inference(flattening,[],[f34])).
% 3.39/0.97  
% 3.39/0.97  fof(f36,plain,(
% 3.39/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.39/0.97    inference(rectify,[],[f35])).
% 3.39/0.97  
% 3.39/0.97  fof(f37,plain,(
% 3.39/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.39/0.97    introduced(choice_axiom,[])).
% 3.39/0.97  
% 3.39/0.97  fof(f38,plain,(
% 3.39/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.39/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.39/0.97  
% 3.39/0.97  fof(f63,plain,(
% 3.39/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.39/0.97    inference(cnf_transformation,[],[f38])).
% 3.39/0.97  
% 3.39/0.97  fof(f86,plain,(
% 3.39/0.97    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.39/0.97    inference(equality_resolution,[],[f63])).
% 3.39/0.97  
% 3.39/0.97  fof(f87,plain,(
% 3.39/0.97    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.39/0.97    inference(equality_resolution,[],[f86])).
% 3.39/0.97  
% 3.39/0.97  fof(f10,axiom,(
% 3.39/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f69,plain,(
% 3.39/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f10])).
% 3.39/0.97  
% 3.39/0.97  fof(f9,axiom,(
% 3.39/0.97    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f68,plain,(
% 3.39/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f9])).
% 3.39/0.97  
% 3.39/0.97  fof(f76,plain,(
% 3.39/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)) )),
% 3.39/0.97    inference(definition_unfolding,[],[f69,f68])).
% 3.39/0.97  
% 3.39/0.97  fof(f13,conjecture,(
% 3.39/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f14,negated_conjecture,(
% 3.39/0.97    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.39/0.97    inference(negated_conjecture,[],[f13])).
% 3.39/0.97  
% 3.39/0.97  fof(f22,plain,(
% 3.39/0.97    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.39/0.97    inference(ennf_transformation,[],[f14])).
% 3.39/0.97  
% 3.39/0.97  fof(f40,plain,(
% 3.39/0.97    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/0.97    inference(nnf_transformation,[],[f22])).
% 3.39/0.97  
% 3.39/0.97  fof(f41,plain,(
% 3.39/0.97    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/0.97    inference(flattening,[],[f40])).
% 3.39/0.97  
% 3.39/0.97  fof(f42,plain,(
% 3.39/0.97    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5)))),
% 3.39/0.97    introduced(choice_axiom,[])).
% 3.39/0.97  
% 3.39/0.97  fof(f43,plain,(
% 3.39/0.97    (~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | r1_tarski(k2_tarski(sK3,sK4),sK5))),
% 3.39/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).
% 3.39/0.97  
% 3.39/0.97  fof(f74,plain,(
% 3.39/0.97    r2_hidden(sK4,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.39/0.97    inference(cnf_transformation,[],[f43])).
% 3.39/0.97  
% 3.39/0.97  fof(f79,plain,(
% 3.39/0.97    r2_hidden(sK4,sK5) | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)),
% 3.39/0.97    inference(definition_unfolding,[],[f74,f68])).
% 3.39/0.97  
% 3.39/0.97  fof(f5,axiom,(
% 3.39/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f17,plain,(
% 3.39/0.97    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.39/0.97    inference(ennf_transformation,[],[f5])).
% 3.39/0.97  
% 3.39/0.97  fof(f57,plain,(
% 3.39/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f17])).
% 3.39/0.97  
% 3.39/0.97  fof(f1,axiom,(
% 3.39/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f15,plain,(
% 3.39/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.39/0.97    inference(ennf_transformation,[],[f1])).
% 3.39/0.97  
% 3.39/0.97  fof(f23,plain,(
% 3.39/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.39/0.97    inference(nnf_transformation,[],[f15])).
% 3.39/0.97  
% 3.39/0.97  fof(f24,plain,(
% 3.39/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.39/0.97    inference(rectify,[],[f23])).
% 3.39/0.97  
% 3.39/0.97  fof(f25,plain,(
% 3.39/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.39/0.97    introduced(choice_axiom,[])).
% 3.39/0.97  
% 3.39/0.97  fof(f26,plain,(
% 3.39/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.39/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.39/0.97  
% 3.39/0.97  fof(f44,plain,(
% 3.39/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f26])).
% 3.39/0.97  
% 3.39/0.97  fof(f75,plain,(
% 3.39/0.97    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.39/0.97    inference(cnf_transformation,[],[f43])).
% 3.39/0.97  
% 3.39/0.97  fof(f78,plain,(
% 3.39/0.97    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | ~r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)),
% 3.39/0.97    inference(definition_unfolding,[],[f75,f68])).
% 3.39/0.97  
% 3.39/0.97  fof(f73,plain,(
% 3.39/0.97    r2_hidden(sK3,sK5) | r1_tarski(k2_tarski(sK3,sK4),sK5)),
% 3.39/0.97    inference(cnf_transformation,[],[f43])).
% 3.39/0.97  
% 3.39/0.97  fof(f80,plain,(
% 3.39/0.97    r2_hidden(sK3,sK5) | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)),
% 3.39/0.97    inference(definition_unfolding,[],[f73,f68])).
% 3.39/0.97  
% 3.39/0.97  fof(f4,axiom,(
% 3.39/0.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f16,plain,(
% 3.39/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.39/0.97    inference(ennf_transformation,[],[f4])).
% 3.39/0.97  
% 3.39/0.97  fof(f56,plain,(
% 3.39/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f16])).
% 3.39/0.97  
% 3.39/0.97  fof(f11,axiom,(
% 3.39/0.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f39,plain,(
% 3.39/0.97    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.39/0.97    inference(nnf_transformation,[],[f11])).
% 3.39/0.97  
% 3.39/0.97  fof(f70,plain,(
% 3.39/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f39])).
% 3.39/0.97  
% 3.39/0.97  fof(f71,plain,(
% 3.39/0.97    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f39])).
% 3.39/0.97  
% 3.39/0.97  fof(f7,axiom,(
% 3.39/0.97    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f19,plain,(
% 3.39/0.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.39/0.97    inference(ennf_transformation,[],[f7])).
% 3.39/0.97  
% 3.39/0.97  fof(f20,plain,(
% 3.39/0.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.39/0.97    inference(flattening,[],[f19])).
% 3.39/0.97  
% 3.39/0.97  fof(f59,plain,(
% 3.39/0.97    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f20])).
% 3.39/0.97  
% 3.39/0.97  fof(f3,axiom,(
% 3.39/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f32,plain,(
% 3.39/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/0.97    inference(nnf_transformation,[],[f3])).
% 3.39/0.97  
% 3.39/0.97  fof(f33,plain,(
% 3.39/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/0.97    inference(flattening,[],[f32])).
% 3.39/0.97  
% 3.39/0.97  fof(f53,plain,(
% 3.39/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.39/0.97    inference(cnf_transformation,[],[f33])).
% 3.39/0.97  
% 3.39/0.97  fof(f85,plain,(
% 3.39/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.39/0.97    inference(equality_resolution,[],[f53])).
% 3.39/0.97  
% 3.39/0.97  fof(f6,axiom,(
% 3.39/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f18,plain,(
% 3.39/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.39/0.97    inference(ennf_transformation,[],[f6])).
% 3.39/0.97  
% 3.39/0.97  fof(f58,plain,(
% 3.39/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.39/0.97    inference(cnf_transformation,[],[f18])).
% 3.39/0.97  
% 3.39/0.97  fof(f2,axiom,(
% 3.39/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.39/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.97  
% 3.39/0.97  fof(f27,plain,(
% 3.39/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/0.97    inference(nnf_transformation,[],[f2])).
% 3.39/0.97  
% 3.39/0.97  fof(f28,plain,(
% 3.39/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/0.97    inference(flattening,[],[f27])).
% 3.39/0.97  
% 3.39/0.97  fof(f29,plain,(
% 3.39/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/0.97    inference(rectify,[],[f28])).
% 3.39/0.97  
% 3.39/0.97  fof(f30,plain,(
% 3.39/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.39/0.97    introduced(choice_axiom,[])).
% 3.39/0.97  
% 3.39/0.97  fof(f31,plain,(
% 3.39/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.39/0.97  
% 3.39/0.97  fof(f48,plain,(
% 3.39/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.39/0.97    inference(cnf_transformation,[],[f31])).
% 3.39/0.97  
% 3.39/0.97  fof(f82,plain,(
% 3.39/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.39/0.97    inference(equality_resolution,[],[f48])).
% 3.39/0.97  
% 3.39/0.97  cnf(c_20,plain,
% 3.39/0.97      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.39/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_1247,plain,
% 3.39/0.97      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
% 3.39/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_24,plain,
% 3.39/0.97      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
% 3.39/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_29,negated_conjecture,
% 3.39/0.97      ( r2_hidden(sK4,sK5)
% 3.39/0.97      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
% 3.39/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_1239,plain,
% 3.39/0.97      ( r2_hidden(sK4,sK5) = iProver_top
% 3.39/0.97      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
% 3.39/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_1584,plain,
% 3.39/0.97      ( r2_hidden(sK4,sK5) = iProver_top
% 3.39/0.97      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.39/0.97      inference(demodulation,[status(thm)],[c_24,c_1239]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_13,plain,
% 3.39/0.97      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.39/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_1254,plain,
% 3.39/0.97      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.39/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.39/0.97  
% 3.39/0.97  cnf(c_2609,plain,
% 3.39/0.97      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.39/0.98      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1584,c_1254]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2,plain,
% 3.39/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.39/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1264,plain,
% 3.39/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.39/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_8472,plain,
% 3.39/0.98      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5
% 3.39/0.98      | r2_hidden(sK4,X0) = iProver_top
% 3.39/0.98      | r1_tarski(sK5,X0) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_2609,c_1264]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_28,negated_conjecture,
% 3.39/0.98      ( ~ r2_hidden(sK3,sK5)
% 3.39/0.98      | ~ r2_hidden(sK4,sK5)
% 3.39/0.98      | ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
% 3.39/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_33,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) != iProver_top
% 3.39/0.98      | r2_hidden(sK4,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_30,negated_conjecture,
% 3.39/0.98      ( r2_hidden(sK3,sK5)
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) ),
% 3.39/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1238,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) = iProver_top
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1585,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) = iProver_top
% 3.39/0.98      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.39/0.98      inference(demodulation,[status(thm)],[c_24,c_1238]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_31,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) = iProver_top
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_12,plain,
% 3.39/0.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.39/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1514,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X2)
% 3.39/0.98      | r1_tarski(k1_tarski(X0),X2) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1664,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)
% 3.39/0.98      | r1_tarski(k1_tarski(sK3),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1665,plain,
% 3.39/0.98      ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_26,plain,
% 3.39/0.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 3.39/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1732,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) | ~ r1_tarski(k1_tarski(sK3),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1733,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) = iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK3),sK5) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1732]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2286,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) = iProver_top ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_1585,c_31,c_1665,c_1733]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_25,plain,
% 3.39/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.39/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2315,plain,
% 3.39/0.98      ( ~ r2_hidden(sK3,sK5) | r1_tarski(k1_tarski(sK3),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2316,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK3),sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_15,plain,
% 3.39/0.98      ( ~ r1_tarski(X0,X1)
% 3.39/0.98      | ~ r1_tarski(X2,X1)
% 3.39/0.98      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.39/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1659,plain,
% 3.39/0.98      ( ~ r1_tarski(X0,X1)
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(X2),X0),X1)
% 3.39/0.98      | ~ r1_tarski(k1_tarski(X2),X1) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1952,plain,
% 3.39/0.98      ( ~ r1_tarski(X0,sK5)
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),X0),sK5)
% 3.39/0.98      | ~ r1_tarski(k1_tarski(sK3),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1659]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_3726,plain,
% 3.39/0.98      ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5)
% 3.39/0.98      | ~ r1_tarski(k1_tarski(sK3),sK5)
% 3.39/0.98      | ~ r1_tarski(k1_tarski(sK4),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1952]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_3727,plain,
% 3.39/0.98      ( r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) = iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK3),sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK4),sK5) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_3726]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_7041,plain,
% 3.39/0.98      ( ~ r2_hidden(sK4,sK5) | r1_tarski(k1_tarski(sK4),sK5) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_7042,plain,
% 3.39/0.98      ( r2_hidden(sK4,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_tarski(sK4),sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_7041]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_9036,plain,
% 3.39/0.98      ( k2_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = sK5 ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_8472,c_31,c_33,c_1665,c_1733,c_2316,c_2609,c_3727,
% 3.39/0.98                 c_7042]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_11,plain,
% 3.39/0.98      ( r1_tarski(X0,X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1256,plain,
% 3.39/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1255,plain,
% 3.39/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.39/0.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2964,plain,
% 3.39/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1256,c_1255]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_14,plain,
% 3.39/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.39/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1253,plain,
% 3.39/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_3734,plain,
% 3.39/0.98      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_2964,c_1253]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_9041,plain,
% 3.39/0.98      ( k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK3,sK3,sK4) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_9036,c_3734]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_7,plain,
% 3.39/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.39/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1259,plain,
% 3.39/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.39/0.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_9424,plain,
% 3.39/0.98      ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK4)) != iProver_top
% 3.39/0.98      | r2_hidden(X0,sK5) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_9041,c_1259]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_13787,plain,
% 3.39/0.98      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1247,c_9424]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_9042,plain,
% 3.39/0.98      ( r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_9036,c_2964]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1240,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) != iProver_top
% 3.39/0.98      | r2_hidden(sK4,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK5) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1586,plain,
% 3.39/0.98      ( r2_hidden(sK3,sK5) != iProver_top
% 3.39/0.98      | r2_hidden(sK4,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
% 3.39/0.98      inference(demodulation,[status(thm)],[c_24,c_1240]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1911,plain,
% 3.39/0.98      ( r2_hidden(sK4,sK5) != iProver_top
% 3.39/0.98      | r1_tarski(k1_enumset1(sK3,sK3,sK4),sK5) != iProver_top ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_1586,c_31,c_1665,c_1733]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(contradiction,plain,
% 3.39/0.98      ( $false ),
% 3.39/0.98      inference(minisat,[status(thm)],[c_13787,c_9042,c_1911]) ).
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.98  
% 3.39/0.98  ------                               Statistics
% 3.39/0.98  
% 3.39/0.98  ------ General
% 3.39/0.98  
% 3.39/0.98  abstr_ref_over_cycles:                  0
% 3.39/0.98  abstr_ref_under_cycles:                 0
% 3.39/0.98  gc_basic_clause_elim:                   0
% 3.39/0.98  forced_gc_time:                         0
% 3.39/0.98  parsing_time:                           0.008
% 3.39/0.98  unif_index_cands_time:                  0.
% 3.39/0.98  unif_index_add_time:                    0.
% 3.39/0.98  orderings_time:                         0.
% 3.39/0.98  out_proof_time:                         0.009
% 3.39/0.98  total_time:                             0.401
% 3.39/0.98  num_of_symbols:                         43
% 3.39/0.98  num_of_terms:                           14875
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing
% 3.39/0.98  
% 3.39/0.98  num_of_splits:                          0
% 3.39/0.98  num_of_split_atoms:                     0
% 3.39/0.98  num_of_reused_defs:                     0
% 3.39/0.98  num_eq_ax_congr_red:                    42
% 3.39/0.98  num_of_sem_filtered_clauses:            1
% 3.39/0.98  num_of_subtypes:                        0
% 3.39/0.98  monotx_restored_types:                  0
% 3.39/0.98  sat_num_of_epr_types:                   0
% 3.39/0.98  sat_num_of_non_cyclic_types:            0
% 3.39/0.98  sat_guarded_non_collapsed_types:        0
% 3.39/0.98  num_pure_diseq_elim:                    0
% 3.39/0.98  simp_replaced_by:                       0
% 3.39/0.98  res_preprocessed:                       133
% 3.39/0.98  prep_upred:                             0
% 3.39/0.98  prep_unflattend:                        0
% 3.39/0.98  smt_new_axioms:                         0
% 3.39/0.98  pred_elim_cands:                        2
% 3.39/0.98  pred_elim:                              0
% 3.39/0.98  pred_elim_cl:                           0
% 3.39/0.98  pred_elim_cycles:                       2
% 3.39/0.98  merged_defs:                            8
% 3.39/0.98  merged_defs_ncl:                        0
% 3.39/0.98  bin_hyper_res:                          8
% 3.39/0.98  prep_cycles:                            4
% 3.39/0.98  pred_elim_time:                         0.001
% 3.39/0.98  splitting_time:                         0.
% 3.39/0.98  sem_filter_time:                        0.
% 3.39/0.98  monotx_time:                            0.
% 3.39/0.98  subtype_inf_time:                       0.
% 3.39/0.98  
% 3.39/0.98  ------ Problem properties
% 3.39/0.98  
% 3.39/0.98  clauses:                                30
% 3.39/0.98  conjectures:                            3
% 3.39/0.98  epr:                                    3
% 3.39/0.98  horn:                                   23
% 3.39/0.98  ground:                                 3
% 3.39/0.98  unary:                                  6
% 3.39/0.98  binary:                                 11
% 3.39/0.98  lits:                                   71
% 3.39/0.98  lits_eq:                                20
% 3.39/0.98  fd_pure:                                0
% 3.39/0.98  fd_pseudo:                              0
% 3.39/0.98  fd_cond:                                0
% 3.39/0.98  fd_pseudo_cond:                         8
% 3.39/0.98  ac_symbols:                             0
% 3.39/0.98  
% 3.39/0.98  ------ Propositional Solver
% 3.39/0.98  
% 3.39/0.98  prop_solver_calls:                      28
% 3.39/0.98  prop_fast_solver_calls:                 810
% 3.39/0.98  smt_solver_calls:                       0
% 3.39/0.98  smt_fast_solver_calls:                  0
% 3.39/0.98  prop_num_of_clauses:                    4973
% 3.39/0.98  prop_preprocess_simplified:             15454
% 3.39/0.98  prop_fo_subsumed:                       6
% 3.39/0.98  prop_solver_time:                       0.
% 3.39/0.98  smt_solver_time:                        0.
% 3.39/0.98  smt_fast_solver_time:                   0.
% 3.39/0.98  prop_fast_solver_time:                  0.
% 3.39/0.98  prop_unsat_core_time:                   0.
% 3.39/0.98  
% 3.39/0.98  ------ QBF
% 3.39/0.98  
% 3.39/0.98  qbf_q_res:                              0
% 3.39/0.98  qbf_num_tautologies:                    0
% 3.39/0.98  qbf_prep_cycles:                        0
% 3.39/0.98  
% 3.39/0.98  ------ BMC1
% 3.39/0.98  
% 3.39/0.98  bmc1_current_bound:                     -1
% 3.39/0.98  bmc1_last_solved_bound:                 -1
% 3.39/0.98  bmc1_unsat_core_size:                   -1
% 3.39/0.98  bmc1_unsat_core_parents_size:           -1
% 3.39/0.98  bmc1_merge_next_fun:                    0
% 3.39/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.98  
% 3.39/0.98  ------ Instantiation
% 3.39/0.98  
% 3.39/0.98  inst_num_of_clauses:                    1398
% 3.39/0.98  inst_num_in_passive:                    995
% 3.39/0.98  inst_num_in_active:                     371
% 3.39/0.98  inst_num_in_unprocessed:                32
% 3.39/0.98  inst_num_of_loops:                      460
% 3.39/0.98  inst_num_of_learning_restarts:          0
% 3.39/0.98  inst_num_moves_active_passive:          85
% 3.39/0.98  inst_lit_activity:                      0
% 3.39/0.98  inst_lit_activity_moves:                0
% 3.39/0.98  inst_num_tautologies:                   0
% 3.39/0.98  inst_num_prop_implied:                  0
% 3.39/0.98  inst_num_existing_simplified:           0
% 3.39/0.98  inst_num_eq_res_simplified:             0
% 3.39/0.98  inst_num_child_elim:                    0
% 3.39/0.98  inst_num_of_dismatching_blockings:      1413
% 3.39/0.98  inst_num_of_non_proper_insts:           1630
% 3.39/0.98  inst_num_of_duplicates:                 0
% 3.39/0.98  inst_inst_num_from_inst_to_res:         0
% 3.39/0.98  inst_dismatching_checking_time:         0.
% 3.39/0.98  
% 3.39/0.98  ------ Resolution
% 3.39/0.98  
% 3.39/0.98  res_num_of_clauses:                     0
% 3.39/0.98  res_num_in_passive:                     0
% 3.39/0.98  res_num_in_active:                      0
% 3.39/0.98  res_num_of_loops:                       137
% 3.39/0.98  res_forward_subset_subsumed:            129
% 3.39/0.98  res_backward_subset_subsumed:           12
% 3.39/0.98  res_forward_subsumed:                   0
% 3.39/0.98  res_backward_subsumed:                  0
% 3.39/0.98  res_forward_subsumption_resolution:     0
% 3.39/0.98  res_backward_subsumption_resolution:    0
% 3.39/0.98  res_clause_to_clause_subsumption:       1031
% 3.39/0.98  res_orphan_elimination:                 0
% 3.39/0.98  res_tautology_del:                      58
% 3.39/0.98  res_num_eq_res_simplified:              0
% 3.39/0.98  res_num_sel_changes:                    0
% 3.39/0.98  res_moves_from_active_to_pass:          0
% 3.39/0.98  
% 3.39/0.98  ------ Superposition
% 3.39/0.98  
% 3.39/0.98  sup_time_total:                         0.
% 3.39/0.98  sup_time_generating:                    0.
% 3.39/0.98  sup_time_sim_full:                      0.
% 3.39/0.98  sup_time_sim_immed:                     0.
% 3.39/0.98  
% 3.39/0.98  sup_num_of_clauses:                     211
% 3.39/0.98  sup_num_in_active:                      85
% 3.39/0.98  sup_num_in_passive:                     126
% 3.39/0.98  sup_num_of_loops:                       91
% 3.39/0.98  sup_fw_superposition:                   248
% 3.39/0.98  sup_bw_superposition:                   187
% 3.39/0.98  sup_immediate_simplified:               27
% 3.39/0.98  sup_given_eliminated:                   0
% 3.39/0.98  comparisons_done:                       0
% 3.39/0.98  comparisons_avoided:                    6
% 3.39/0.98  
% 3.39/0.98  ------ Simplifications
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  sim_fw_subset_subsumed:                 0
% 3.39/0.98  sim_bw_subset_subsumed:                 6
% 3.39/0.98  sim_fw_subsumed:                        24
% 3.39/0.98  sim_bw_subsumed:                        0
% 3.39/0.98  sim_fw_subsumption_res:                 0
% 3.39/0.98  sim_bw_subsumption_res:                 0
% 3.39/0.98  sim_tautology_del:                      44
% 3.39/0.98  sim_eq_tautology_del:                   8
% 3.39/0.98  sim_eq_res_simp:                        2
% 3.39/0.98  sim_fw_demodulated:                     0
% 3.39/0.98  sim_bw_demodulated:                     3
% 3.39/0.98  sim_light_normalised:                   6
% 3.39/0.98  sim_joinable_taut:                      0
% 3.39/0.98  sim_joinable_simp:                      0
% 3.39/0.98  sim_ac_normalised:                      0
% 3.39/0.98  sim_smt_subsumption:                    0
% 3.39/0.98  
%------------------------------------------------------------------------------
