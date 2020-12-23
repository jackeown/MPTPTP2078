%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:23 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 753 expanded)
%              Number of clauses        :   44 ( 150 expanded)
%              Number of leaves         :   21 ( 210 expanded)
%              Depth                    :   18
%              Number of atoms          :  350 (1521 expanded)
%              Number of equality atoms :  197 ( 887 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f81,f88])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f80,f89])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f90])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f91])).

fof(f111,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f99])).

fof(f112,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f91])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f92])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f39])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) )
   => ( ( r2_hidden(sK6,sK7)
        | r2_hidden(sK5,sK7)
        | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6) )
      & ( ( ~ r2_hidden(sK6,sK7)
          & ~ r2_hidden(sK5,sK7) )
        | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( r2_hidden(sK6,sK7)
      | r2_hidden(sK5,sK7)
      | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6) )
    & ( ( ~ r2_hidden(sK6,sK7)
        & ~ r2_hidden(sK5,sK7) )
      | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f48])).

fof(f85,plain,
    ( ~ r2_hidden(sK5,sK7)
    | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f105,plain,
    ( ~ r2_hidden(sK5,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(definition_unfolding,[],[f85,f67,f92,f92])).

fof(f86,plain,
    ( ~ r2_hidden(sK6,sK7)
    | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,
    ( ~ r2_hidden(sK6,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(definition_unfolding,[],[f86,f67,f92,f92])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f73,f91])).

fof(f109,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f110,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f109])).

fof(f87,plain,
    ( r2_hidden(sK6,sK7)
    | r2_hidden(sK5,sK7)
    | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,
    ( r2_hidden(sK6,sK7)
    | r2_hidden(sK5,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(definition_unfolding,[],[f87,f67,f92,f92])).

cnf(c_24,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_906,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_903,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_913,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_915,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2591,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_915])).

cnf(c_2674,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_2591])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK5,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_900,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1660,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_900])).

cnf(c_10940,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),sK7) = k1_xboole_0
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_1660])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK6,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_901,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1659,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_901])).

cnf(c_12403,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10940,c_1659])).

cnf(c_18,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_912,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1869,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_912])).

cnf(c_2675,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1869,c_2591])).

cnf(c_12660,plain,
    ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12403,c_2675])).

cnf(c_2981,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2675,c_1869])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2985,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2981,c_17])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_918,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5452,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_918])).

cnf(c_16988,plain,
    ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK7,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12660,c_5452])).

cnf(c_16991,plain,
    ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16988,c_17])).

cnf(c_18421,plain,
    ( r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_16991])).

cnf(c_23,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_907,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18420,plain,
    ( r2_hidden(sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_16991])).

cnf(c_16985,plain,
    ( k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12660,c_0])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK5,sK7)
    | r2_hidden(sK6,sK7)
    | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_902,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) = iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1658,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) = iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_902])).

cnf(c_17456,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k1_xboole_0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) = iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16985,c_1658])).

cnf(c_17461,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | r2_hidden(sK5,sK7) = iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17456,c_17])).

cnf(c_17462,plain,
    ( r2_hidden(sK5,sK7) = iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18421,c_18420,c_17462])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.05/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/1.00  
% 4.05/1.00  ------  iProver source info
% 4.05/1.00  
% 4.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/1.00  git: non_committed_changes: false
% 4.05/1.00  git: last_make_outside_of_git: false
% 4.05/1.00  
% 4.05/1.00  ------ 
% 4.05/1.00  
% 4.05/1.00  ------ Input Options
% 4.05/1.00  
% 4.05/1.00  --out_options                           all
% 4.05/1.00  --tptp_safe_out                         true
% 4.05/1.00  --problem_path                          ""
% 4.05/1.00  --include_path                          ""
% 4.05/1.00  --clausifier                            res/vclausify_rel
% 4.05/1.00  --clausifier_options                    ""
% 4.05/1.00  --stdin                                 false
% 4.05/1.00  --stats_out                             all
% 4.05/1.00  
% 4.05/1.00  ------ General Options
% 4.05/1.00  
% 4.05/1.00  --fof                                   false
% 4.05/1.00  --time_out_real                         305.
% 4.05/1.00  --time_out_virtual                      -1.
% 4.05/1.00  --symbol_type_check                     false
% 4.05/1.00  --clausify_out                          false
% 4.05/1.00  --sig_cnt_out                           false
% 4.05/1.00  --trig_cnt_out                          false
% 4.05/1.00  --trig_cnt_out_tolerance                1.
% 4.05/1.00  --trig_cnt_out_sk_spl                   false
% 4.05/1.00  --abstr_cl_out                          false
% 4.05/1.00  
% 4.05/1.00  ------ Global Options
% 4.05/1.00  
% 4.05/1.00  --schedule                              default
% 4.05/1.00  --add_important_lit                     false
% 4.05/1.00  --prop_solver_per_cl                    1000
% 4.05/1.00  --min_unsat_core                        false
% 4.05/1.00  --soft_assumptions                      false
% 4.05/1.00  --soft_lemma_size                       3
% 4.05/1.00  --prop_impl_unit_size                   0
% 4.05/1.00  --prop_impl_unit                        []
% 4.05/1.00  --share_sel_clauses                     true
% 4.05/1.00  --reset_solvers                         false
% 4.05/1.00  --bc_imp_inh                            [conj_cone]
% 4.05/1.00  --conj_cone_tolerance                   3.
% 4.05/1.00  --extra_neg_conj                        none
% 4.05/1.00  --large_theory_mode                     true
% 4.05/1.00  --prolific_symb_bound                   200
% 4.05/1.00  --lt_threshold                          2000
% 4.05/1.00  --clause_weak_htbl                      true
% 4.05/1.00  --gc_record_bc_elim                     false
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing Options
% 4.05/1.00  
% 4.05/1.00  --preprocessing_flag                    true
% 4.05/1.00  --time_out_prep_mult                    0.1
% 4.05/1.00  --splitting_mode                        input
% 4.05/1.00  --splitting_grd                         true
% 4.05/1.00  --splitting_cvd                         false
% 4.05/1.00  --splitting_cvd_svl                     false
% 4.05/1.00  --splitting_nvd                         32
% 4.05/1.00  --sub_typing                            true
% 4.05/1.00  --prep_gs_sim                           true
% 4.05/1.00  --prep_unflatten                        true
% 4.05/1.00  --prep_res_sim                          true
% 4.05/1.00  --prep_upred                            true
% 4.05/1.00  --prep_sem_filter                       exhaustive
% 4.05/1.00  --prep_sem_filter_out                   false
% 4.05/1.00  --pred_elim                             true
% 4.05/1.00  --res_sim_input                         true
% 4.05/1.00  --eq_ax_congr_red                       true
% 4.05/1.00  --pure_diseq_elim                       true
% 4.05/1.00  --brand_transform                       false
% 4.05/1.00  --non_eq_to_eq                          false
% 4.05/1.00  --prep_def_merge                        true
% 4.05/1.00  --prep_def_merge_prop_impl              false
% 4.05/1.00  --prep_def_merge_mbd                    true
% 4.05/1.00  --prep_def_merge_tr_red                 false
% 4.05/1.00  --prep_def_merge_tr_cl                  false
% 4.05/1.00  --smt_preprocessing                     true
% 4.05/1.00  --smt_ac_axioms                         fast
% 4.05/1.00  --preprocessed_out                      false
% 4.05/1.00  --preprocessed_stats                    false
% 4.05/1.00  
% 4.05/1.00  ------ Abstraction refinement Options
% 4.05/1.00  
% 4.05/1.00  --abstr_ref                             []
% 4.05/1.00  --abstr_ref_prep                        false
% 4.05/1.00  --abstr_ref_until_sat                   false
% 4.05/1.00  --abstr_ref_sig_restrict                funpre
% 4.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/1.00  --abstr_ref_under                       []
% 4.05/1.00  
% 4.05/1.00  ------ SAT Options
% 4.05/1.00  
% 4.05/1.00  --sat_mode                              false
% 4.05/1.00  --sat_fm_restart_options                ""
% 4.05/1.00  --sat_gr_def                            false
% 4.05/1.00  --sat_epr_types                         true
% 4.05/1.00  --sat_non_cyclic_types                  false
% 4.05/1.00  --sat_finite_models                     false
% 4.05/1.00  --sat_fm_lemmas                         false
% 4.05/1.00  --sat_fm_prep                           false
% 4.05/1.00  --sat_fm_uc_incr                        true
% 4.05/1.00  --sat_out_model                         small
% 4.05/1.00  --sat_out_clauses                       false
% 4.05/1.00  
% 4.05/1.00  ------ QBF Options
% 4.05/1.00  
% 4.05/1.00  --qbf_mode                              false
% 4.05/1.00  --qbf_elim_univ                         false
% 4.05/1.00  --qbf_dom_inst                          none
% 4.05/1.00  --qbf_dom_pre_inst                      false
% 4.05/1.00  --qbf_sk_in                             false
% 4.05/1.00  --qbf_pred_elim                         true
% 4.05/1.00  --qbf_split                             512
% 4.05/1.00  
% 4.05/1.00  ------ BMC1 Options
% 4.05/1.00  
% 4.05/1.00  --bmc1_incremental                      false
% 4.05/1.00  --bmc1_axioms                           reachable_all
% 4.05/1.00  --bmc1_min_bound                        0
% 4.05/1.00  --bmc1_max_bound                        -1
% 4.05/1.00  --bmc1_max_bound_default                -1
% 4.05/1.00  --bmc1_symbol_reachability              true
% 4.05/1.00  --bmc1_property_lemmas                  false
% 4.05/1.00  --bmc1_k_induction                      false
% 4.05/1.00  --bmc1_non_equiv_states                 false
% 4.05/1.00  --bmc1_deadlock                         false
% 4.05/1.00  --bmc1_ucm                              false
% 4.05/1.00  --bmc1_add_unsat_core                   none
% 4.05/1.00  --bmc1_unsat_core_children              false
% 4.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/1.00  --bmc1_out_stat                         full
% 4.05/1.00  --bmc1_ground_init                      false
% 4.05/1.00  --bmc1_pre_inst_next_state              false
% 4.05/1.00  --bmc1_pre_inst_state                   false
% 4.05/1.00  --bmc1_pre_inst_reach_state             false
% 4.05/1.00  --bmc1_out_unsat_core                   false
% 4.05/1.00  --bmc1_aig_witness_out                  false
% 4.05/1.00  --bmc1_verbose                          false
% 4.05/1.00  --bmc1_dump_clauses_tptp                false
% 4.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.05/1.00  --bmc1_dump_file                        -
% 4.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.05/1.00  --bmc1_ucm_extend_mode                  1
% 4.05/1.00  --bmc1_ucm_init_mode                    2
% 4.05/1.00  --bmc1_ucm_cone_mode                    none
% 4.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.05/1.00  --bmc1_ucm_relax_model                  4
% 4.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/1.00  --bmc1_ucm_layered_model                none
% 4.05/1.00  --bmc1_ucm_max_lemma_size               10
% 4.05/1.00  
% 4.05/1.00  ------ AIG Options
% 4.05/1.00  
% 4.05/1.00  --aig_mode                              false
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation Options
% 4.05/1.00  
% 4.05/1.00  --instantiation_flag                    true
% 4.05/1.00  --inst_sos_flag                         true
% 4.05/1.00  --inst_sos_phase                        true
% 4.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel_side                     num_symb
% 4.05/1.00  --inst_solver_per_active                1400
% 4.05/1.00  --inst_solver_calls_frac                1.
% 4.05/1.00  --inst_passive_queue_type               priority_queues
% 4.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/1.00  --inst_passive_queues_freq              [25;2]
% 4.05/1.00  --inst_dismatching                      true
% 4.05/1.00  --inst_eager_unprocessed_to_passive     true
% 4.05/1.00  --inst_prop_sim_given                   true
% 4.05/1.00  --inst_prop_sim_new                     false
% 4.05/1.00  --inst_subs_new                         false
% 4.05/1.00  --inst_eq_res_simp                      false
% 4.05/1.00  --inst_subs_given                       false
% 4.05/1.00  --inst_orphan_elimination               true
% 4.05/1.00  --inst_learning_loop_flag               true
% 4.05/1.00  --inst_learning_start                   3000
% 4.05/1.00  --inst_learning_factor                  2
% 4.05/1.00  --inst_start_prop_sim_after_learn       3
% 4.05/1.00  --inst_sel_renew                        solver
% 4.05/1.00  --inst_lit_activity_flag                true
% 4.05/1.00  --inst_restr_to_given                   false
% 4.05/1.00  --inst_activity_threshold               500
% 4.05/1.00  --inst_out_proof                        true
% 4.05/1.00  
% 4.05/1.00  ------ Resolution Options
% 4.05/1.00  
% 4.05/1.00  --resolution_flag                       true
% 4.05/1.00  --res_lit_sel                           adaptive
% 4.05/1.00  --res_lit_sel_side                      none
% 4.05/1.00  --res_ordering                          kbo
% 4.05/1.00  --res_to_prop_solver                    active
% 4.05/1.00  --res_prop_simpl_new                    false
% 4.05/1.00  --res_prop_simpl_given                  true
% 4.05/1.00  --res_passive_queue_type                priority_queues
% 4.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/1.00  --res_passive_queues_freq               [15;5]
% 4.05/1.00  --res_forward_subs                      full
% 4.05/1.00  --res_backward_subs                     full
% 4.05/1.00  --res_forward_subs_resolution           true
% 4.05/1.00  --res_backward_subs_resolution          true
% 4.05/1.00  --res_orphan_elimination                true
% 4.05/1.00  --res_time_limit                        2.
% 4.05/1.00  --res_out_proof                         true
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Options
% 4.05/1.00  
% 4.05/1.00  --superposition_flag                    true
% 4.05/1.00  --sup_passive_queue_type                priority_queues
% 4.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.05/1.00  --demod_completeness_check              fast
% 4.05/1.00  --demod_use_ground                      true
% 4.05/1.00  --sup_to_prop_solver                    passive
% 4.05/1.00  --sup_prop_simpl_new                    true
% 4.05/1.00  --sup_prop_simpl_given                  true
% 4.05/1.00  --sup_fun_splitting                     true
% 4.05/1.00  --sup_smt_interval                      50000
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Simplification Setup
% 4.05/1.00  
% 4.05/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_immed_triv                        [TrivRules]
% 4.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_bw_main                     []
% 4.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_input_bw                          []
% 4.05/1.00  
% 4.05/1.00  ------ Combination Options
% 4.05/1.00  
% 4.05/1.00  --comb_res_mult                         3
% 4.05/1.00  --comb_sup_mult                         2
% 4.05/1.00  --comb_inst_mult                        10
% 4.05/1.00  
% 4.05/1.00  ------ Debug Options
% 4.05/1.00  
% 4.05/1.00  --dbg_backtrace                         false
% 4.05/1.00  --dbg_dump_prop_clauses                 false
% 4.05/1.00  --dbg_dump_prop_clauses_file            -
% 4.05/1.00  --dbg_out_stat                          false
% 4.05/1.00  ------ Parsing...
% 4.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  ------ Proving...
% 4.05/1.00  ------ Problem Properties 
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  clauses                                 31
% 4.05/1.00  conjectures                             3
% 4.05/1.00  EPR                                     1
% 4.05/1.00  Horn                                    18
% 4.05/1.00  unary                                   6
% 4.05/1.00  binary                                  9
% 4.05/1.00  lits                                    76
% 4.05/1.00  lits eq                                 22
% 4.05/1.00  fd_pure                                 0
% 4.05/1.00  fd_pseudo                               0
% 4.05/1.00  fd_cond                                 1
% 4.05/1.00  fd_pseudo_cond                          7
% 4.05/1.00  AC symbols                              0
% 4.05/1.00  
% 4.05/1.00  ------ Schedule dynamic 5 is on 
% 4.05/1.00  
% 4.05/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ 
% 4.05/1.00  Current options:
% 4.05/1.00  ------ 
% 4.05/1.00  
% 4.05/1.00  ------ Input Options
% 4.05/1.00  
% 4.05/1.00  --out_options                           all
% 4.05/1.00  --tptp_safe_out                         true
% 4.05/1.00  --problem_path                          ""
% 4.05/1.00  --include_path                          ""
% 4.05/1.00  --clausifier                            res/vclausify_rel
% 4.05/1.00  --clausifier_options                    ""
% 4.05/1.00  --stdin                                 false
% 4.05/1.00  --stats_out                             all
% 4.05/1.00  
% 4.05/1.00  ------ General Options
% 4.05/1.00  
% 4.05/1.00  --fof                                   false
% 4.05/1.00  --time_out_real                         305.
% 4.05/1.00  --time_out_virtual                      -1.
% 4.05/1.00  --symbol_type_check                     false
% 4.05/1.00  --clausify_out                          false
% 4.05/1.00  --sig_cnt_out                           false
% 4.05/1.00  --trig_cnt_out                          false
% 4.05/1.00  --trig_cnt_out_tolerance                1.
% 4.05/1.00  --trig_cnt_out_sk_spl                   false
% 4.05/1.00  --abstr_cl_out                          false
% 4.05/1.00  
% 4.05/1.00  ------ Global Options
% 4.05/1.00  
% 4.05/1.00  --schedule                              default
% 4.05/1.00  --add_important_lit                     false
% 4.05/1.00  --prop_solver_per_cl                    1000
% 4.05/1.00  --min_unsat_core                        false
% 4.05/1.00  --soft_assumptions                      false
% 4.05/1.00  --soft_lemma_size                       3
% 4.05/1.00  --prop_impl_unit_size                   0
% 4.05/1.00  --prop_impl_unit                        []
% 4.05/1.00  --share_sel_clauses                     true
% 4.05/1.00  --reset_solvers                         false
% 4.05/1.00  --bc_imp_inh                            [conj_cone]
% 4.05/1.00  --conj_cone_tolerance                   3.
% 4.05/1.00  --extra_neg_conj                        none
% 4.05/1.00  --large_theory_mode                     true
% 4.05/1.00  --prolific_symb_bound                   200
% 4.05/1.00  --lt_threshold                          2000
% 4.05/1.00  --clause_weak_htbl                      true
% 4.05/1.00  --gc_record_bc_elim                     false
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing Options
% 4.05/1.00  
% 4.05/1.00  --preprocessing_flag                    true
% 4.05/1.00  --time_out_prep_mult                    0.1
% 4.05/1.00  --splitting_mode                        input
% 4.05/1.00  --splitting_grd                         true
% 4.05/1.00  --splitting_cvd                         false
% 4.05/1.00  --splitting_cvd_svl                     false
% 4.05/1.00  --splitting_nvd                         32
% 4.05/1.00  --sub_typing                            true
% 4.05/1.00  --prep_gs_sim                           true
% 4.05/1.00  --prep_unflatten                        true
% 4.05/1.00  --prep_res_sim                          true
% 4.05/1.00  --prep_upred                            true
% 4.05/1.00  --prep_sem_filter                       exhaustive
% 4.05/1.00  --prep_sem_filter_out                   false
% 4.05/1.00  --pred_elim                             true
% 4.05/1.00  --res_sim_input                         true
% 4.05/1.00  --eq_ax_congr_red                       true
% 4.05/1.00  --pure_diseq_elim                       true
% 4.05/1.00  --brand_transform                       false
% 4.05/1.00  --non_eq_to_eq                          false
% 4.05/1.00  --prep_def_merge                        true
% 4.05/1.00  --prep_def_merge_prop_impl              false
% 4.05/1.00  --prep_def_merge_mbd                    true
% 4.05/1.00  --prep_def_merge_tr_red                 false
% 4.05/1.00  --prep_def_merge_tr_cl                  false
% 4.05/1.00  --smt_preprocessing                     true
% 4.05/1.00  --smt_ac_axioms                         fast
% 4.05/1.00  --preprocessed_out                      false
% 4.05/1.00  --preprocessed_stats                    false
% 4.05/1.00  
% 4.05/1.00  ------ Abstraction refinement Options
% 4.05/1.00  
% 4.05/1.00  --abstr_ref                             []
% 4.05/1.00  --abstr_ref_prep                        false
% 4.05/1.00  --abstr_ref_until_sat                   false
% 4.05/1.00  --abstr_ref_sig_restrict                funpre
% 4.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/1.00  --abstr_ref_under                       []
% 4.05/1.00  
% 4.05/1.00  ------ SAT Options
% 4.05/1.00  
% 4.05/1.00  --sat_mode                              false
% 4.05/1.00  --sat_fm_restart_options                ""
% 4.05/1.00  --sat_gr_def                            false
% 4.05/1.00  --sat_epr_types                         true
% 4.05/1.00  --sat_non_cyclic_types                  false
% 4.05/1.00  --sat_finite_models                     false
% 4.05/1.00  --sat_fm_lemmas                         false
% 4.05/1.00  --sat_fm_prep                           false
% 4.05/1.00  --sat_fm_uc_incr                        true
% 4.05/1.00  --sat_out_model                         small
% 4.05/1.00  --sat_out_clauses                       false
% 4.05/1.00  
% 4.05/1.00  ------ QBF Options
% 4.05/1.00  
% 4.05/1.00  --qbf_mode                              false
% 4.05/1.00  --qbf_elim_univ                         false
% 4.05/1.00  --qbf_dom_inst                          none
% 4.05/1.00  --qbf_dom_pre_inst                      false
% 4.05/1.00  --qbf_sk_in                             false
% 4.05/1.00  --qbf_pred_elim                         true
% 4.05/1.00  --qbf_split                             512
% 4.05/1.00  
% 4.05/1.00  ------ BMC1 Options
% 4.05/1.00  
% 4.05/1.00  --bmc1_incremental                      false
% 4.05/1.00  --bmc1_axioms                           reachable_all
% 4.05/1.00  --bmc1_min_bound                        0
% 4.05/1.00  --bmc1_max_bound                        -1
% 4.05/1.00  --bmc1_max_bound_default                -1
% 4.05/1.00  --bmc1_symbol_reachability              true
% 4.05/1.00  --bmc1_property_lemmas                  false
% 4.05/1.00  --bmc1_k_induction                      false
% 4.05/1.00  --bmc1_non_equiv_states                 false
% 4.05/1.00  --bmc1_deadlock                         false
% 4.05/1.00  --bmc1_ucm                              false
% 4.05/1.00  --bmc1_add_unsat_core                   none
% 4.05/1.00  --bmc1_unsat_core_children              false
% 4.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/1.00  --bmc1_out_stat                         full
% 4.05/1.00  --bmc1_ground_init                      false
% 4.05/1.00  --bmc1_pre_inst_next_state              false
% 4.05/1.00  --bmc1_pre_inst_state                   false
% 4.05/1.00  --bmc1_pre_inst_reach_state             false
% 4.05/1.00  --bmc1_out_unsat_core                   false
% 4.05/1.00  --bmc1_aig_witness_out                  false
% 4.05/1.00  --bmc1_verbose                          false
% 4.05/1.00  --bmc1_dump_clauses_tptp                false
% 4.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.05/1.00  --bmc1_dump_file                        -
% 4.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.05/1.00  --bmc1_ucm_extend_mode                  1
% 4.05/1.00  --bmc1_ucm_init_mode                    2
% 4.05/1.00  --bmc1_ucm_cone_mode                    none
% 4.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.05/1.00  --bmc1_ucm_relax_model                  4
% 4.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/1.00  --bmc1_ucm_layered_model                none
% 4.05/1.00  --bmc1_ucm_max_lemma_size               10
% 4.05/1.00  
% 4.05/1.00  ------ AIG Options
% 4.05/1.00  
% 4.05/1.00  --aig_mode                              false
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation Options
% 4.05/1.00  
% 4.05/1.00  --instantiation_flag                    true
% 4.05/1.00  --inst_sos_flag                         true
% 4.05/1.00  --inst_sos_phase                        true
% 4.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel_side                     none
% 4.05/1.00  --inst_solver_per_active                1400
% 4.05/1.00  --inst_solver_calls_frac                1.
% 4.05/1.00  --inst_passive_queue_type               priority_queues
% 4.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/1.00  --inst_passive_queues_freq              [25;2]
% 4.05/1.00  --inst_dismatching                      true
% 4.05/1.00  --inst_eager_unprocessed_to_passive     true
% 4.05/1.00  --inst_prop_sim_given                   true
% 4.05/1.00  --inst_prop_sim_new                     false
% 4.05/1.00  --inst_subs_new                         false
% 4.05/1.00  --inst_eq_res_simp                      false
% 4.05/1.00  --inst_subs_given                       false
% 4.05/1.00  --inst_orphan_elimination               true
% 4.05/1.00  --inst_learning_loop_flag               true
% 4.05/1.00  --inst_learning_start                   3000
% 4.05/1.00  --inst_learning_factor                  2
% 4.05/1.00  --inst_start_prop_sim_after_learn       3
% 4.05/1.00  --inst_sel_renew                        solver
% 4.05/1.00  --inst_lit_activity_flag                true
% 4.05/1.00  --inst_restr_to_given                   false
% 4.05/1.00  --inst_activity_threshold               500
% 4.05/1.00  --inst_out_proof                        true
% 4.05/1.00  
% 4.05/1.00  ------ Resolution Options
% 4.05/1.00  
% 4.05/1.00  --resolution_flag                       false
% 4.05/1.00  --res_lit_sel                           adaptive
% 4.05/1.00  --res_lit_sel_side                      none
% 4.05/1.00  --res_ordering                          kbo
% 4.05/1.00  --res_to_prop_solver                    active
% 4.05/1.00  --res_prop_simpl_new                    false
% 4.05/1.00  --res_prop_simpl_given                  true
% 4.05/1.00  --res_passive_queue_type                priority_queues
% 4.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/1.00  --res_passive_queues_freq               [15;5]
% 4.05/1.00  --res_forward_subs                      full
% 4.05/1.00  --res_backward_subs                     full
% 4.05/1.00  --res_forward_subs_resolution           true
% 4.05/1.00  --res_backward_subs_resolution          true
% 4.05/1.00  --res_orphan_elimination                true
% 4.05/1.00  --res_time_limit                        2.
% 4.05/1.00  --res_out_proof                         true
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Options
% 4.05/1.00  
% 4.05/1.00  --superposition_flag                    true
% 4.05/1.00  --sup_passive_queue_type                priority_queues
% 4.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.05/1.00  --demod_completeness_check              fast
% 4.05/1.00  --demod_use_ground                      true
% 4.05/1.00  --sup_to_prop_solver                    passive
% 4.05/1.00  --sup_prop_simpl_new                    true
% 4.05/1.00  --sup_prop_simpl_given                  true
% 4.05/1.00  --sup_fun_splitting                     true
% 4.05/1.00  --sup_smt_interval                      50000
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Simplification Setup
% 4.05/1.00  
% 4.05/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_immed_triv                        [TrivRules]
% 4.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_bw_main                     []
% 4.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_input_bw                          []
% 4.05/1.00  
% 4.05/1.00  ------ Combination Options
% 4.05/1.00  
% 4.05/1.00  --comb_res_mult                         3
% 4.05/1.00  --comb_sup_mult                         2
% 4.05/1.00  --comb_inst_mult                        10
% 4.05/1.00  
% 4.05/1.00  ------ Debug Options
% 4.05/1.00  
% 4.05/1.00  --dbg_backtrace                         false
% 4.05/1.00  --dbg_dump_prop_clauses                 false
% 4.05/1.00  --dbg_dump_prop_clauses_file            -
% 4.05/1.00  --dbg_out_stat                          false
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS status Theorem for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  fof(f10,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f26,plain,(
% 4.05/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.05/1.00    inference(ennf_transformation,[],[f10])).
% 4.05/1.00  
% 4.05/1.00  fof(f41,plain,(
% 4.05/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/1.00    inference(nnf_transformation,[],[f26])).
% 4.05/1.00  
% 4.05/1.00  fof(f42,plain,(
% 4.05/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/1.00    inference(flattening,[],[f41])).
% 4.05/1.00  
% 4.05/1.00  fof(f43,plain,(
% 4.05/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/1.00    inference(rectify,[],[f42])).
% 4.05/1.00  
% 4.05/1.00  fof(f44,plain,(
% 4.05/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f45,plain,(
% 4.05/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 4.05/1.00  
% 4.05/1.00  fof(f72,plain,(
% 4.05/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.05/1.00    inference(cnf_transformation,[],[f45])).
% 4.05/1.00  
% 4.05/1.00  fof(f12,axiom,(
% 4.05/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f79,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f12])).
% 4.05/1.00  
% 4.05/1.00  fof(f13,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f80,plain,(
% 4.05/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f13])).
% 4.05/1.00  
% 4.05/1.00  fof(f14,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f81,plain,(
% 4.05/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f14])).
% 4.05/1.00  
% 4.05/1.00  fof(f15,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f82,plain,(
% 4.05/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f15])).
% 4.05/1.00  
% 4.05/1.00  fof(f16,axiom,(
% 4.05/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f83,plain,(
% 4.05/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f16])).
% 4.05/1.00  
% 4.05/1.00  fof(f88,plain,(
% 4.05/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f82,f83])).
% 4.05/1.00  
% 4.05/1.00  fof(f89,plain,(
% 4.05/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f81,f88])).
% 4.05/1.00  
% 4.05/1.00  fof(f90,plain,(
% 4.05/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f80,f89])).
% 4.05/1.00  
% 4.05/1.00  fof(f91,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f79,f90])).
% 4.05/1.00  
% 4.05/1.00  fof(f99,plain,(
% 4.05/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 4.05/1.00    inference(definition_unfolding,[],[f72,f91])).
% 4.05/1.00  
% 4.05/1.00  fof(f111,plain,(
% 4.05/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 4.05/1.00    inference(equality_resolution,[],[f99])).
% 4.05/1.00  
% 4.05/1.00  fof(f112,plain,(
% 4.05/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 4.05/1.00    inference(equality_resolution,[],[f111])).
% 4.05/1.00  
% 4.05/1.00  fof(f17,axiom,(
% 4.05/1.00    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f27,plain,(
% 4.05/1.00    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f17])).
% 4.05/1.00  
% 4.05/1.00  fof(f84,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f11,axiom,(
% 4.05/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f78,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f11])).
% 4.05/1.00  
% 4.05/1.00  fof(f92,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f78,f91])).
% 4.05/1.00  
% 4.05/1.00  fof(f102,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f84,f92])).
% 4.05/1.00  
% 4.05/1.00  fof(f6,axiom,(
% 4.05/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f25,plain,(
% 4.05/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.05/1.00    inference(ennf_transformation,[],[f6])).
% 4.05/1.00  
% 4.05/1.00  fof(f39,plain,(
% 4.05/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f40,plain,(
% 4.05/1.00    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f39])).
% 4.05/1.00  
% 4.05/1.00  fof(f66,plain,(
% 4.05/1.00    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 4.05/1.00    inference(cnf_transformation,[],[f40])).
% 4.05/1.00  
% 4.05/1.00  fof(f5,axiom,(
% 4.05/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f21,plain,(
% 4.05/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(rectify,[],[f5])).
% 4.05/1.00  
% 4.05/1.00  fof(f24,plain,(
% 4.05/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(ennf_transformation,[],[f21])).
% 4.05/1.00  
% 4.05/1.00  fof(f37,plain,(
% 4.05/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f38,plain,(
% 4.05/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f37])).
% 4.05/1.00  
% 4.05/1.00  fof(f65,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f38])).
% 4.05/1.00  
% 4.05/1.00  fof(f1,axiom,(
% 4.05/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f50,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f1])).
% 4.05/1.00  
% 4.05/1.00  fof(f18,conjecture,(
% 4.05/1.00    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f19,negated_conjecture,(
% 4.05/1.00    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.05/1.00    inference(negated_conjecture,[],[f18])).
% 4.05/1.00  
% 4.05/1.00  fof(f28,plain,(
% 4.05/1.00    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.05/1.00    inference(ennf_transformation,[],[f19])).
% 4.05/1.00  
% 4.05/1.00  fof(f46,plain,(
% 4.05/1.00    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 4.05/1.00    inference(nnf_transformation,[],[f28])).
% 4.05/1.00  
% 4.05/1.00  fof(f47,plain,(
% 4.05/1.00    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 4.05/1.00    inference(flattening,[],[f46])).
% 4.05/1.00  
% 4.05/1.00  fof(f48,plain,(
% 4.05/1.00    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6)) & ((~r2_hidden(sK6,sK7) & ~r2_hidden(sK5,sK7)) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f49,plain,(
% 4.05/1.00    (r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6)) & ((~r2_hidden(sK6,sK7) & ~r2_hidden(sK5,sK7)) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f48])).
% 4.05/1.00  
% 4.05/1.00  fof(f85,plain,(
% 4.05/1.00    ~r2_hidden(sK5,sK7) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6)),
% 4.05/1.00    inference(cnf_transformation,[],[f49])).
% 4.05/1.00  
% 4.05/1.00  fof(f7,axiom,(
% 4.05/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f67,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f7])).
% 4.05/1.00  
% 4.05/1.00  fof(f105,plain,(
% 4.05/1.00    ~r2_hidden(sK5,sK7) | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),
% 4.05/1.00    inference(definition_unfolding,[],[f85,f67,f92,f92])).
% 4.05/1.00  
% 4.05/1.00  fof(f86,plain,(
% 4.05/1.00    ~r2_hidden(sK6,sK7) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k2_tarski(sK5,sK6)),
% 4.05/1.00    inference(cnf_transformation,[],[f49])).
% 4.05/1.00  
% 4.05/1.00  fof(f104,plain,(
% 4.05/1.00    ~r2_hidden(sK6,sK7) | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),
% 4.05/1.00    inference(definition_unfolding,[],[f86,f67,f92,f92])).
% 4.05/1.00  
% 4.05/1.00  fof(f9,axiom,(
% 4.05/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f69,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f9])).
% 4.05/1.00  
% 4.05/1.00  fof(f93,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.05/1.00    inference(definition_unfolding,[],[f69,f67])).
% 4.05/1.00  
% 4.05/1.00  fof(f8,axiom,(
% 4.05/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f68,plain,(
% 4.05/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.05/1.00    inference(cnf_transformation,[],[f8])).
% 4.05/1.00  
% 4.05/1.00  fof(f4,axiom,(
% 4.05/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f20,plain,(
% 4.05/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(rectify,[],[f4])).
% 4.05/1.00  
% 4.05/1.00  fof(f23,plain,(
% 4.05/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(ennf_transformation,[],[f20])).
% 4.05/1.00  
% 4.05/1.00  fof(f35,plain,(
% 4.05/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f36,plain,(
% 4.05/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f35])).
% 4.05/1.00  
% 4.05/1.00  fof(f63,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f36])).
% 4.05/1.00  
% 4.05/1.00  fof(f73,plain,(
% 4.05/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.05/1.00    inference(cnf_transformation,[],[f45])).
% 4.05/1.00  
% 4.05/1.00  fof(f98,plain,(
% 4.05/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 4.05/1.00    inference(definition_unfolding,[],[f73,f91])).
% 4.05/1.00  
% 4.05/1.00  fof(f109,plain,(
% 4.05/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 4.05/1.00    inference(equality_resolution,[],[f98])).
% 4.05/1.00  
% 4.05/1.00  fof(f110,plain,(
% 4.05/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 4.05/1.00    inference(equality_resolution,[],[f109])).
% 4.05/1.00  
% 4.05/1.00  fof(f87,plain,(
% 4.05/1.00    r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k4_xboole_0(k2_tarski(sK5,sK6),sK7) != k2_tarski(sK5,sK6)),
% 4.05/1.00    inference(cnf_transformation,[],[f49])).
% 4.05/1.00  
% 4.05/1.00  fof(f103,plain,(
% 4.05/1.00    r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)),
% 4.05/1.00    inference(definition_unfolding,[],[f87,f67,f92,f92])).
% 4.05/1.00  
% 4.05/1.00  cnf(c_24,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f112]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_906,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_27,plain,
% 4.05/1.00      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 4.05/1.00      | r2_hidden(X0,X2)
% 4.05/1.00      | r2_hidden(X1,X2) ),
% 4.05/1.00      inference(cnf_transformation,[],[f102]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_903,plain,
% 4.05/1.00      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) = iProver_top
% 4.05/1.00      | r2_hidden(X0,X2) = iProver_top
% 4.05/1.00      | r2_hidden(X1,X2) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16,plain,
% 4.05/1.00      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_913,plain,
% 4.05/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_14,plain,
% 4.05/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_915,plain,
% 4.05/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2591,plain,
% 4.05/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 4.05/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_913,c_915]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2674,plain,
% 4.05/1.00      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) = k1_xboole_0
% 4.05/1.00      | r2_hidden(X1,X2) = iProver_top
% 4.05/1.00      | r2_hidden(X0,X2) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_903,c_2591]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_0,plain,
% 4.05/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_30,negated_conjecture,
% 4.05/1.00      ( ~ r2_hidden(sK5,sK7)
% 4.05/1.00      | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
% 4.05/1.00      inference(cnf_transformation,[],[f105]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_900,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1660,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) != iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_0,c_900]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10940,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0),sK7) = k1_xboole_0
% 4.05/1.00      | r2_hidden(X0,sK7) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_2674,c_1660]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_29,negated_conjecture,
% 4.05/1.00      ( ~ r2_hidden(sK6,sK7)
% 4.05/1.00      | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
% 4.05/1.00      inference(cnf_transformation,[],[f104]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_901,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK6,sK7) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1659,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK6,sK7) != iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_0,c_901]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12403,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7) = k1_xboole_0 ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10940,c_1659]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_18,plain,
% 4.05/1.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f93]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_912,plain,
% 4.05/1.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1869,plain,
% 4.05/1.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_0,c_912]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2675,plain,
% 4.05/1.00      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1869,c_2591]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12660,plain,
% 4.05/1.00      ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7) = k1_xboole_0 ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12403,c_2675]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2981,plain,
% 4.05/1.00      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_2675,c_1869]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_17,plain,
% 4.05/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2985,plain,
% 4.05/1.00      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_2981,c_17]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11,plain,
% 4.05/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_918,plain,
% 4.05/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X2,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5452,plain,
% 4.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_2985,c_918]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16988,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top
% 4.05/1.00      | r2_hidden(X0,k5_xboole_0(sK7,k1_xboole_0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12660,c_5452]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16991,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != iProver_top
% 4.05/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_16988,c_17]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_18421,plain,
% 4.05/1.00      ( r2_hidden(sK5,sK7) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_906,c_16991]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_23,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f110]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_907,plain,
% 4.05/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_18420,plain,
% 4.05/1.00      ( r2_hidden(sK6,sK7) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_907,c_16991]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16985,plain,
% 4.05/1.00      ( k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k1_xboole_0 ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12660,c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_28,negated_conjecture,
% 4.05/1.00      ( r2_hidden(sK5,sK7)
% 4.05/1.00      | r2_hidden(sK6,sK7)
% 4.05/1.00      | k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
% 4.05/1.00      inference(cnf_transformation,[],[f103]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_902,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),sK7)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) = iProver_top
% 4.05/1.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1658,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) = iProver_top
% 4.05/1.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_0,c_902]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_17456,plain,
% 4.05/1.00      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k1_xboole_0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) = iProver_top
% 4.05/1.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_16985,c_1658]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_17461,plain,
% 4.05/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 4.05/1.00      | r2_hidden(sK5,sK7) = iProver_top
% 4.05/1.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 4.05/1.00      inference(demodulation,[status(thm)],[c_17456,c_17]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_17462,plain,
% 4.05/1.00      ( r2_hidden(sK5,sK7) = iProver_top
% 4.05/1.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 4.05/1.00      inference(equality_resolution_simp,[status(thm)],[c_17461]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(contradiction,plain,
% 4.05/1.00      ( $false ),
% 4.05/1.00      inference(minisat,[status(thm)],[c_18421,c_18420,c_17462]) ).
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  ------                               Statistics
% 4.05/1.00  
% 4.05/1.00  ------ General
% 4.05/1.00  
% 4.05/1.00  abstr_ref_over_cycles:                  0
% 4.05/1.00  abstr_ref_under_cycles:                 0
% 4.05/1.00  gc_basic_clause_elim:                   0
% 4.05/1.00  forced_gc_time:                         0
% 4.05/1.00  parsing_time:                           0.011
% 4.05/1.00  unif_index_cands_time:                  0.
% 4.05/1.00  unif_index_add_time:                    0.
% 4.05/1.00  orderings_time:                         0.
% 4.05/1.00  out_proof_time:                         0.01
% 4.05/1.00  total_time:                             0.471
% 4.05/1.00  num_of_symbols:                         45
% 4.05/1.00  num_of_terms:                           21391
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing
% 4.05/1.00  
% 4.05/1.00  num_of_splits:                          0
% 4.05/1.00  num_of_split_atoms:                     0
% 4.05/1.00  num_of_reused_defs:                     0
% 4.05/1.00  num_eq_ax_congr_red:                    26
% 4.05/1.00  num_of_sem_filtered_clauses:            1
% 4.05/1.00  num_of_subtypes:                        0
% 4.05/1.00  monotx_restored_types:                  0
% 4.05/1.00  sat_num_of_epr_types:                   0
% 4.05/1.00  sat_num_of_non_cyclic_types:            0
% 4.05/1.00  sat_guarded_non_collapsed_types:        0
% 4.05/1.00  num_pure_diseq_elim:                    0
% 4.05/1.00  simp_replaced_by:                       0
% 4.05/1.00  res_preprocessed:                       108
% 4.05/1.00  prep_upred:                             0
% 4.05/1.00  prep_unflattend:                        8
% 4.05/1.00  smt_new_axioms:                         0
% 4.05/1.00  pred_elim_cands:                        2
% 4.05/1.00  pred_elim:                              0
% 4.05/1.00  pred_elim_cl:                           0
% 4.05/1.00  pred_elim_cycles:                       1
% 4.05/1.00  merged_defs:                            0
% 4.05/1.00  merged_defs_ncl:                        0
% 4.05/1.00  bin_hyper_res:                          0
% 4.05/1.00  prep_cycles:                            3
% 4.05/1.00  pred_elim_time:                         0.003
% 4.05/1.00  splitting_time:                         0.
% 4.05/1.00  sem_filter_time:                        0.
% 4.05/1.00  monotx_time:                            0.
% 4.05/1.00  subtype_inf_time:                       0.
% 4.05/1.00  
% 4.05/1.00  ------ Problem properties
% 4.05/1.00  
% 4.05/1.00  clauses:                                31
% 4.05/1.00  conjectures:                            3
% 4.05/1.00  epr:                                    1
% 4.05/1.00  horn:                                   18
% 4.05/1.00  ground:                                 3
% 4.05/1.00  unary:                                  6
% 4.05/1.00  binary:                                 9
% 4.05/1.00  lits:                                   76
% 4.05/1.00  lits_eq:                                22
% 4.05/1.00  fd_pure:                                0
% 4.05/1.00  fd_pseudo:                              0
% 4.05/1.00  fd_cond:                                1
% 4.05/1.00  fd_pseudo_cond:                         7
% 4.05/1.00  ac_symbols:                             0
% 4.05/1.00  
% 4.05/1.00  ------ Propositional Solver
% 4.05/1.00  
% 4.05/1.00  prop_solver_calls:                      26
% 4.05/1.00  prop_fast_solver_calls:                 868
% 4.05/1.00  smt_solver_calls:                       0
% 4.05/1.00  smt_fast_solver_calls:                  0
% 4.05/1.00  prop_num_of_clauses:                    8257
% 4.05/1.00  prop_preprocess_simplified:             18433
% 4.05/1.00  prop_fo_subsumed:                       7
% 4.05/1.00  prop_solver_time:                       0.
% 4.05/1.00  smt_solver_time:                        0.
% 4.05/1.00  smt_fast_solver_time:                   0.
% 4.05/1.00  prop_fast_solver_time:                  0.
% 4.05/1.00  prop_unsat_core_time:                   0.
% 4.05/1.00  
% 4.05/1.00  ------ QBF
% 4.05/1.00  
% 4.05/1.00  qbf_q_res:                              0
% 4.05/1.00  qbf_num_tautologies:                    0
% 4.05/1.00  qbf_prep_cycles:                        0
% 4.05/1.00  
% 4.05/1.00  ------ BMC1
% 4.05/1.00  
% 4.05/1.00  bmc1_current_bound:                     -1
% 4.05/1.00  bmc1_last_solved_bound:                 -1
% 4.05/1.00  bmc1_unsat_core_size:                   -1
% 4.05/1.00  bmc1_unsat_core_parents_size:           -1
% 4.05/1.00  bmc1_merge_next_fun:                    0
% 4.05/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation
% 4.05/1.00  
% 4.05/1.00  inst_num_of_clauses:                    1881
% 4.05/1.00  inst_num_in_passive:                    1438
% 4.05/1.00  inst_num_in_active:                     294
% 4.05/1.00  inst_num_in_unprocessed:                149
% 4.05/1.00  inst_num_of_loops:                      600
% 4.05/1.00  inst_num_of_learning_restarts:          0
% 4.05/1.00  inst_num_moves_active_passive:          306
% 4.05/1.00  inst_lit_activity:                      0
% 4.05/1.00  inst_lit_activity_moves:                0
% 4.05/1.00  inst_num_tautologies:                   0
% 4.05/1.00  inst_num_prop_implied:                  0
% 4.05/1.00  inst_num_existing_simplified:           0
% 4.05/1.00  inst_num_eq_res_simplified:             0
% 4.05/1.00  inst_num_child_elim:                    0
% 4.05/1.00  inst_num_of_dismatching_blockings:      1456
% 4.05/1.00  inst_num_of_non_proper_insts:           3000
% 4.05/1.00  inst_num_of_duplicates:                 0
% 4.05/1.00  inst_inst_num_from_inst_to_res:         0
% 4.05/1.00  inst_dismatching_checking_time:         0.
% 4.05/1.00  
% 4.05/1.00  ------ Resolution
% 4.05/1.00  
% 4.05/1.00  res_num_of_clauses:                     0
% 4.05/1.00  res_num_in_passive:                     0
% 4.05/1.00  res_num_in_active:                      0
% 4.05/1.00  res_num_of_loops:                       111
% 4.05/1.00  res_forward_subset_subsumed:            61
% 4.05/1.00  res_backward_subset_subsumed:           0
% 4.05/1.00  res_forward_subsumed:                   0
% 4.05/1.00  res_backward_subsumed:                  0
% 4.05/1.00  res_forward_subsumption_resolution:     0
% 4.05/1.00  res_backward_subsumption_resolution:    0
% 4.05/1.00  res_clause_to_clause_subsumption:       6522
% 4.05/1.00  res_orphan_elimination:                 0
% 4.05/1.00  res_tautology_del:                      62
% 4.05/1.00  res_num_eq_res_simplified:              0
% 4.05/1.00  res_num_sel_changes:                    0
% 4.05/1.00  res_moves_from_active_to_pass:          0
% 4.05/1.00  
% 4.05/1.00  ------ Superposition
% 4.05/1.00  
% 4.05/1.00  sup_time_total:                         0.
% 4.05/1.00  sup_time_generating:                    0.
% 4.05/1.00  sup_time_sim_full:                      0.
% 4.05/1.00  sup_time_sim_immed:                     0.
% 4.05/1.00  
% 4.05/1.00  sup_num_of_clauses:                     449
% 4.05/1.00  sup_num_in_active:                      104
% 4.05/1.00  sup_num_in_passive:                     345
% 4.05/1.00  sup_num_of_loops:                       118
% 4.05/1.00  sup_fw_superposition:                   651
% 4.05/1.00  sup_bw_superposition:                   657
% 4.05/1.00  sup_immediate_simplified:               300
% 4.05/1.00  sup_given_eliminated:                   1
% 4.05/1.00  comparisons_done:                       0
% 4.05/1.00  comparisons_avoided:                    33
% 4.05/1.00  
% 4.05/1.00  ------ Simplifications
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  sim_fw_subset_subsumed:                 52
% 4.05/1.00  sim_bw_subset_subsumed:                 6
% 4.05/1.00  sim_fw_subsumed:                        57
% 4.05/1.00  sim_bw_subsumed:                        3
% 4.05/1.00  sim_fw_subsumption_res:                 0
% 4.05/1.00  sim_bw_subsumption_res:                 0
% 4.05/1.00  sim_tautology_del:                      24
% 4.05/1.00  sim_eq_tautology_del:                   31
% 4.05/1.00  sim_eq_res_simp:                        5
% 4.05/1.00  sim_fw_demodulated:                     137
% 4.05/1.00  sim_bw_demodulated:                     13
% 4.05/1.00  sim_light_normalised:                   72
% 4.05/1.00  sim_joinable_taut:                      0
% 4.05/1.00  sim_joinable_simp:                      0
% 4.05/1.00  sim_ac_normalised:                      0
% 4.05/1.00  sim_smt_subsumption:                    0
% 4.05/1.00  
%------------------------------------------------------------------------------
