%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:02 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 237 expanded)
%              Number of clauses        :   37 (  46 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  413 ( 791 expanded)
%              Number of equality atoms :  249 ( 547 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK5 != sK7
      & r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( sK5 != sK7
    & r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f48])).

fof(f91,plain,(
    r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f83,f93])).

fof(f119,plain,(
    r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f91,f93,f94])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f87,f94,f94])).

fof(f92,plain,(
    sK5 != sK7 ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f127,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f101])).

fof(f128,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f127])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f95,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f64,f93,f93])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f77,f93])).

fof(f139,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f113])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f125,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f126,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f125])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1326,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1328,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2805,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k2_enumset1(sK5,sK5,sK5,sK6)
    | k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1326,c_1328])).

cnf(c_3361,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = X0
    | k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2805,c_1328])).

cnf(c_38,negated_conjecture,
    ( sK5 != sK7 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_747,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1607,plain,
    ( sK7 != X0
    | sK5 != X0
    | sK5 = sK7 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_1714,plain,
    ( sK7 != sK5
    | sK5 = sK7
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_746,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1715,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1344,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1332,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2926,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1332])).

cnf(c_3369,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0
    | sK7 = X0
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2805,c_2926])).

cnf(c_4214,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0
    | sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_1344,c_3369])).

cnf(c_4244,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3361,c_38,c_1714,c_1715,c_4214])).

cnf(c_4260,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4244,c_1344])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1345,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1350,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1351,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1353,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2318,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1353])).

cnf(c_2480,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1350,c_2318])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1358,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2788,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_1358])).

cnf(c_11414,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_2788])).

cnf(c_11452,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4260,c_11414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:42:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.55/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.98  
% 3.55/0.98  ------  iProver source info
% 3.55/0.98  
% 3.55/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.98  git: non_committed_changes: false
% 3.55/0.98  git: last_make_outside_of_git: false
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  
% 3.55/0.98  ------ Input Options
% 3.55/0.98  
% 3.55/0.98  --out_options                           all
% 3.55/0.98  --tptp_safe_out                         true
% 3.55/0.98  --problem_path                          ""
% 3.55/0.98  --include_path                          ""
% 3.55/0.98  --clausifier                            res/vclausify_rel
% 3.55/0.98  --clausifier_options                    --mode clausify
% 3.55/0.98  --stdin                                 false
% 3.55/0.98  --stats_out                             all
% 3.55/0.98  
% 3.55/0.98  ------ General Options
% 3.55/0.98  
% 3.55/0.98  --fof                                   false
% 3.55/0.98  --time_out_real                         305.
% 3.55/0.98  --time_out_virtual                      -1.
% 3.55/0.98  --symbol_type_check                     false
% 3.55/0.98  --clausify_out                          false
% 3.55/0.98  --sig_cnt_out                           false
% 3.55/0.98  --trig_cnt_out                          false
% 3.55/0.98  --trig_cnt_out_tolerance                1.
% 3.55/0.98  --trig_cnt_out_sk_spl                   false
% 3.55/0.98  --abstr_cl_out                          false
% 3.55/0.98  
% 3.55/0.98  ------ Global Options
% 3.55/0.98  
% 3.55/0.98  --schedule                              default
% 3.55/0.98  --add_important_lit                     false
% 3.55/0.98  --prop_solver_per_cl                    1000
% 3.55/0.98  --min_unsat_core                        false
% 3.55/0.98  --soft_assumptions                      false
% 3.55/0.98  --soft_lemma_size                       3
% 3.55/0.98  --prop_impl_unit_size                   0
% 3.55/0.98  --prop_impl_unit                        []
% 3.55/0.98  --share_sel_clauses                     true
% 3.55/0.98  --reset_solvers                         false
% 3.55/0.98  --bc_imp_inh                            [conj_cone]
% 3.55/0.98  --conj_cone_tolerance                   3.
% 3.55/0.98  --extra_neg_conj                        none
% 3.55/0.98  --large_theory_mode                     true
% 3.55/0.98  --prolific_symb_bound                   200
% 3.55/0.98  --lt_threshold                          2000
% 3.55/0.98  --clause_weak_htbl                      true
% 3.55/0.98  --gc_record_bc_elim                     false
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing Options
% 3.55/0.98  
% 3.55/0.98  --preprocessing_flag                    true
% 3.55/0.98  --time_out_prep_mult                    0.1
% 3.55/0.98  --splitting_mode                        input
% 3.55/0.98  --splitting_grd                         true
% 3.55/0.98  --splitting_cvd                         false
% 3.55/0.98  --splitting_cvd_svl                     false
% 3.55/0.98  --splitting_nvd                         32
% 3.55/0.98  --sub_typing                            true
% 3.55/0.98  --prep_gs_sim                           true
% 3.55/0.98  --prep_unflatten                        true
% 3.55/0.98  --prep_res_sim                          true
% 3.55/0.98  --prep_upred                            true
% 3.55/0.98  --prep_sem_filter                       exhaustive
% 3.55/0.98  --prep_sem_filter_out                   false
% 3.55/0.98  --pred_elim                             true
% 3.55/0.98  --res_sim_input                         true
% 3.55/0.98  --eq_ax_congr_red                       true
% 3.55/0.98  --pure_diseq_elim                       true
% 3.55/0.98  --brand_transform                       false
% 3.55/0.98  --non_eq_to_eq                          false
% 3.55/0.98  --prep_def_merge                        true
% 3.55/0.98  --prep_def_merge_prop_impl              false
% 3.55/0.98  --prep_def_merge_mbd                    true
% 3.55/0.98  --prep_def_merge_tr_red                 false
% 3.55/0.98  --prep_def_merge_tr_cl                  false
% 3.55/0.98  --smt_preprocessing                     true
% 3.55/0.98  --smt_ac_axioms                         fast
% 3.55/0.98  --preprocessed_out                      false
% 3.55/0.98  --preprocessed_stats                    false
% 3.55/0.98  
% 3.55/0.98  ------ Abstraction refinement Options
% 3.55/0.98  
% 3.55/0.98  --abstr_ref                             []
% 3.55/0.98  --abstr_ref_prep                        false
% 3.55/0.98  --abstr_ref_until_sat                   false
% 3.55/0.98  --abstr_ref_sig_restrict                funpre
% 3.55/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.98  --abstr_ref_under                       []
% 3.55/0.98  
% 3.55/0.98  ------ SAT Options
% 3.55/0.98  
% 3.55/0.98  --sat_mode                              false
% 3.55/0.98  --sat_fm_restart_options                ""
% 3.55/0.98  --sat_gr_def                            false
% 3.55/0.98  --sat_epr_types                         true
% 3.55/0.98  --sat_non_cyclic_types                  false
% 3.55/0.98  --sat_finite_models                     false
% 3.55/0.98  --sat_fm_lemmas                         false
% 3.55/0.98  --sat_fm_prep                           false
% 3.55/0.98  --sat_fm_uc_incr                        true
% 3.55/0.98  --sat_out_model                         small
% 3.55/0.98  --sat_out_clauses                       false
% 3.55/0.98  
% 3.55/0.98  ------ QBF Options
% 3.55/0.98  
% 3.55/0.98  --qbf_mode                              false
% 3.55/0.98  --qbf_elim_univ                         false
% 3.55/0.98  --qbf_dom_inst                          none
% 3.55/0.98  --qbf_dom_pre_inst                      false
% 3.55/0.98  --qbf_sk_in                             false
% 3.55/0.98  --qbf_pred_elim                         true
% 3.55/0.98  --qbf_split                             512
% 3.55/0.98  
% 3.55/0.98  ------ BMC1 Options
% 3.55/0.98  
% 3.55/0.98  --bmc1_incremental                      false
% 3.55/0.98  --bmc1_axioms                           reachable_all
% 3.55/0.98  --bmc1_min_bound                        0
% 3.55/0.98  --bmc1_max_bound                        -1
% 3.55/0.98  --bmc1_max_bound_default                -1
% 3.55/0.98  --bmc1_symbol_reachability              true
% 3.55/0.98  --bmc1_property_lemmas                  false
% 3.55/0.98  --bmc1_k_induction                      false
% 3.55/0.98  --bmc1_non_equiv_states                 false
% 3.55/0.98  --bmc1_deadlock                         false
% 3.55/0.98  --bmc1_ucm                              false
% 3.55/0.98  --bmc1_add_unsat_core                   none
% 3.55/0.98  --bmc1_unsat_core_children              false
% 3.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.98  --bmc1_out_stat                         full
% 3.55/0.98  --bmc1_ground_init                      false
% 3.55/0.98  --bmc1_pre_inst_next_state              false
% 3.55/0.98  --bmc1_pre_inst_state                   false
% 3.55/0.98  --bmc1_pre_inst_reach_state             false
% 3.55/0.98  --bmc1_out_unsat_core                   false
% 3.55/0.98  --bmc1_aig_witness_out                  false
% 3.55/0.98  --bmc1_verbose                          false
% 3.55/0.98  --bmc1_dump_clauses_tptp                false
% 3.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.98  --bmc1_dump_file                        -
% 3.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.98  --bmc1_ucm_extend_mode                  1
% 3.55/0.98  --bmc1_ucm_init_mode                    2
% 3.55/0.98  --bmc1_ucm_cone_mode                    none
% 3.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.98  --bmc1_ucm_relax_model                  4
% 3.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.98  --bmc1_ucm_layered_model                none
% 3.55/0.98  --bmc1_ucm_max_lemma_size               10
% 3.55/0.98  
% 3.55/0.98  ------ AIG Options
% 3.55/0.98  
% 3.55/0.98  --aig_mode                              false
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation Options
% 3.55/0.98  
% 3.55/0.98  --instantiation_flag                    true
% 3.55/0.98  --inst_sos_flag                         false
% 3.55/0.98  --inst_sos_phase                        true
% 3.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel_side                     num_symb
% 3.55/0.98  --inst_solver_per_active                1400
% 3.55/0.98  --inst_solver_calls_frac                1.
% 3.55/0.98  --inst_passive_queue_type               priority_queues
% 3.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.98  --inst_passive_queues_freq              [25;2]
% 3.55/0.98  --inst_dismatching                      true
% 3.55/0.98  --inst_eager_unprocessed_to_passive     true
% 3.55/0.98  --inst_prop_sim_given                   true
% 3.55/0.98  --inst_prop_sim_new                     false
% 3.55/0.98  --inst_subs_new                         false
% 3.55/0.98  --inst_eq_res_simp                      false
% 3.55/0.98  --inst_subs_given                       false
% 3.55/0.98  --inst_orphan_elimination               true
% 3.55/0.98  --inst_learning_loop_flag               true
% 3.55/0.98  --inst_learning_start                   3000
% 3.55/0.98  --inst_learning_factor                  2
% 3.55/0.98  --inst_start_prop_sim_after_learn       3
% 3.55/0.98  --inst_sel_renew                        solver
% 3.55/0.98  --inst_lit_activity_flag                true
% 3.55/0.98  --inst_restr_to_given                   false
% 3.55/0.98  --inst_activity_threshold               500
% 3.55/0.98  --inst_out_proof                        true
% 3.55/0.98  
% 3.55/0.98  ------ Resolution Options
% 3.55/0.98  
% 3.55/0.98  --resolution_flag                       true
% 3.55/0.98  --res_lit_sel                           adaptive
% 3.55/0.98  --res_lit_sel_side                      none
% 3.55/0.98  --res_ordering                          kbo
% 3.55/0.98  --res_to_prop_solver                    active
% 3.55/0.98  --res_prop_simpl_new                    false
% 3.55/0.98  --res_prop_simpl_given                  true
% 3.55/0.98  --res_passive_queue_type                priority_queues
% 3.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.98  --res_passive_queues_freq               [15;5]
% 3.55/0.98  --res_forward_subs                      full
% 3.55/0.98  --res_backward_subs                     full
% 3.55/0.98  --res_forward_subs_resolution           true
% 3.55/0.98  --res_backward_subs_resolution          true
% 3.55/0.98  --res_orphan_elimination                true
% 3.55/0.98  --res_time_limit                        2.
% 3.55/0.98  --res_out_proof                         true
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Options
% 3.55/0.98  
% 3.55/0.98  --superposition_flag                    true
% 3.55/0.98  --sup_passive_queue_type                priority_queues
% 3.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.98  --demod_completeness_check              fast
% 3.55/0.98  --demod_use_ground                      true
% 3.55/0.98  --sup_to_prop_solver                    passive
% 3.55/0.98  --sup_prop_simpl_new                    true
% 3.55/0.98  --sup_prop_simpl_given                  true
% 3.55/0.98  --sup_fun_splitting                     false
% 3.55/0.98  --sup_smt_interval                      50000
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Simplification Setup
% 3.55/0.98  
% 3.55/0.98  --sup_indices_passive                   []
% 3.55/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_full_bw                           [BwDemod]
% 3.55/0.98  --sup_immed_triv                        [TrivRules]
% 3.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_immed_bw_main                     []
% 3.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.98  
% 3.55/0.98  ------ Combination Options
% 3.55/0.98  
% 3.55/0.98  --comb_res_mult                         3
% 3.55/0.98  --comb_sup_mult                         2
% 3.55/0.98  --comb_inst_mult                        10
% 3.55/0.98  
% 3.55/0.98  ------ Debug Options
% 3.55/0.98  
% 3.55/0.98  --dbg_backtrace                         false
% 3.55/0.98  --dbg_dump_prop_clauses                 false
% 3.55/0.98  --dbg_dump_prop_clauses_file            -
% 3.55/0.98  --dbg_out_stat                          false
% 3.55/0.98  ------ Parsing...
% 3.55/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.98  ------ Proving...
% 3.55/0.98  ------ Problem Properties 
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  clauses                                 39
% 3.55/0.98  conjectures                             2
% 3.55/0.98  EPR                                     5
% 3.55/0.98  Horn                                    27
% 3.55/0.98  unary                                   15
% 3.55/0.98  binary                                  6
% 3.55/0.98  lits                                    86
% 3.55/0.98  lits eq                                 35
% 3.55/0.98  fd_pure                                 0
% 3.55/0.98  fd_pseudo                               0
% 3.55/0.98  fd_cond                                 0
% 3.55/0.98  fd_pseudo_cond                          14
% 3.55/0.98  AC symbols                              0
% 3.55/0.98  
% 3.55/0.98  ------ Schedule dynamic 5 is on 
% 3.55/0.98  
% 3.55/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  Current options:
% 3.55/0.98  ------ 
% 3.55/0.98  
% 3.55/0.98  ------ Input Options
% 3.55/0.98  
% 3.55/0.98  --out_options                           all
% 3.55/0.98  --tptp_safe_out                         true
% 3.55/0.98  --problem_path                          ""
% 3.55/0.98  --include_path                          ""
% 3.55/0.98  --clausifier                            res/vclausify_rel
% 3.55/0.98  --clausifier_options                    --mode clausify
% 3.55/0.98  --stdin                                 false
% 3.55/0.98  --stats_out                             all
% 3.55/0.98  
% 3.55/0.98  ------ General Options
% 3.55/0.98  
% 3.55/0.98  --fof                                   false
% 3.55/0.98  --time_out_real                         305.
% 3.55/0.98  --time_out_virtual                      -1.
% 3.55/0.98  --symbol_type_check                     false
% 3.55/0.98  --clausify_out                          false
% 3.55/0.98  --sig_cnt_out                           false
% 3.55/0.98  --trig_cnt_out                          false
% 3.55/0.98  --trig_cnt_out_tolerance                1.
% 3.55/0.98  --trig_cnt_out_sk_spl                   false
% 3.55/0.98  --abstr_cl_out                          false
% 3.55/0.98  
% 3.55/0.98  ------ Global Options
% 3.55/0.98  
% 3.55/0.98  --schedule                              default
% 3.55/0.98  --add_important_lit                     false
% 3.55/0.98  --prop_solver_per_cl                    1000
% 3.55/0.98  --min_unsat_core                        false
% 3.55/0.98  --soft_assumptions                      false
% 3.55/0.98  --soft_lemma_size                       3
% 3.55/0.98  --prop_impl_unit_size                   0
% 3.55/0.98  --prop_impl_unit                        []
% 3.55/0.98  --share_sel_clauses                     true
% 3.55/0.98  --reset_solvers                         false
% 3.55/0.98  --bc_imp_inh                            [conj_cone]
% 3.55/0.98  --conj_cone_tolerance                   3.
% 3.55/0.98  --extra_neg_conj                        none
% 3.55/0.98  --large_theory_mode                     true
% 3.55/0.98  --prolific_symb_bound                   200
% 3.55/0.98  --lt_threshold                          2000
% 3.55/0.98  --clause_weak_htbl                      true
% 3.55/0.98  --gc_record_bc_elim                     false
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing Options
% 3.55/0.98  
% 3.55/0.98  --preprocessing_flag                    true
% 3.55/0.98  --time_out_prep_mult                    0.1
% 3.55/0.98  --splitting_mode                        input
% 3.55/0.98  --splitting_grd                         true
% 3.55/0.98  --splitting_cvd                         false
% 3.55/0.98  --splitting_cvd_svl                     false
% 3.55/0.98  --splitting_nvd                         32
% 3.55/0.98  --sub_typing                            true
% 3.55/0.98  --prep_gs_sim                           true
% 3.55/0.98  --prep_unflatten                        true
% 3.55/0.98  --prep_res_sim                          true
% 3.55/0.98  --prep_upred                            true
% 3.55/0.98  --prep_sem_filter                       exhaustive
% 3.55/0.98  --prep_sem_filter_out                   false
% 3.55/0.98  --pred_elim                             true
% 3.55/0.98  --res_sim_input                         true
% 3.55/0.98  --eq_ax_congr_red                       true
% 3.55/0.98  --pure_diseq_elim                       true
% 3.55/0.98  --brand_transform                       false
% 3.55/0.98  --non_eq_to_eq                          false
% 3.55/0.98  --prep_def_merge                        true
% 3.55/0.98  --prep_def_merge_prop_impl              false
% 3.55/0.98  --prep_def_merge_mbd                    true
% 3.55/0.98  --prep_def_merge_tr_red                 false
% 3.55/0.98  --prep_def_merge_tr_cl                  false
% 3.55/0.98  --smt_preprocessing                     true
% 3.55/0.98  --smt_ac_axioms                         fast
% 3.55/0.98  --preprocessed_out                      false
% 3.55/0.98  --preprocessed_stats                    false
% 3.55/0.98  
% 3.55/0.98  ------ Abstraction refinement Options
% 3.55/0.98  
% 3.55/0.98  --abstr_ref                             []
% 3.55/0.98  --abstr_ref_prep                        false
% 3.55/0.98  --abstr_ref_until_sat                   false
% 3.55/0.98  --abstr_ref_sig_restrict                funpre
% 3.55/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.98  --abstr_ref_under                       []
% 3.55/0.98  
% 3.55/0.98  ------ SAT Options
% 3.55/0.98  
% 3.55/0.98  --sat_mode                              false
% 3.55/0.98  --sat_fm_restart_options                ""
% 3.55/0.98  --sat_gr_def                            false
% 3.55/0.98  --sat_epr_types                         true
% 3.55/0.98  --sat_non_cyclic_types                  false
% 3.55/0.98  --sat_finite_models                     false
% 3.55/0.98  --sat_fm_lemmas                         false
% 3.55/0.98  --sat_fm_prep                           false
% 3.55/0.98  --sat_fm_uc_incr                        true
% 3.55/0.98  --sat_out_model                         small
% 3.55/0.98  --sat_out_clauses                       false
% 3.55/0.98  
% 3.55/0.98  ------ QBF Options
% 3.55/0.98  
% 3.55/0.98  --qbf_mode                              false
% 3.55/0.98  --qbf_elim_univ                         false
% 3.55/0.98  --qbf_dom_inst                          none
% 3.55/0.98  --qbf_dom_pre_inst                      false
% 3.55/0.98  --qbf_sk_in                             false
% 3.55/0.98  --qbf_pred_elim                         true
% 3.55/0.98  --qbf_split                             512
% 3.55/0.98  
% 3.55/0.98  ------ BMC1 Options
% 3.55/0.98  
% 3.55/0.98  --bmc1_incremental                      false
% 3.55/0.98  --bmc1_axioms                           reachable_all
% 3.55/0.98  --bmc1_min_bound                        0
% 3.55/0.98  --bmc1_max_bound                        -1
% 3.55/0.98  --bmc1_max_bound_default                -1
% 3.55/0.98  --bmc1_symbol_reachability              true
% 3.55/0.98  --bmc1_property_lemmas                  false
% 3.55/0.98  --bmc1_k_induction                      false
% 3.55/0.98  --bmc1_non_equiv_states                 false
% 3.55/0.98  --bmc1_deadlock                         false
% 3.55/0.98  --bmc1_ucm                              false
% 3.55/0.98  --bmc1_add_unsat_core                   none
% 3.55/0.98  --bmc1_unsat_core_children              false
% 3.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.98  --bmc1_out_stat                         full
% 3.55/0.98  --bmc1_ground_init                      false
% 3.55/0.98  --bmc1_pre_inst_next_state              false
% 3.55/0.98  --bmc1_pre_inst_state                   false
% 3.55/0.98  --bmc1_pre_inst_reach_state             false
% 3.55/0.98  --bmc1_out_unsat_core                   false
% 3.55/0.98  --bmc1_aig_witness_out                  false
% 3.55/0.98  --bmc1_verbose                          false
% 3.55/0.98  --bmc1_dump_clauses_tptp                false
% 3.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.98  --bmc1_dump_file                        -
% 3.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.98  --bmc1_ucm_extend_mode                  1
% 3.55/0.98  --bmc1_ucm_init_mode                    2
% 3.55/0.98  --bmc1_ucm_cone_mode                    none
% 3.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.98  --bmc1_ucm_relax_model                  4
% 3.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.98  --bmc1_ucm_layered_model                none
% 3.55/0.98  --bmc1_ucm_max_lemma_size               10
% 3.55/0.98  
% 3.55/0.98  ------ AIG Options
% 3.55/0.98  
% 3.55/0.98  --aig_mode                              false
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation Options
% 3.55/0.98  
% 3.55/0.98  --instantiation_flag                    true
% 3.55/0.98  --inst_sos_flag                         false
% 3.55/0.98  --inst_sos_phase                        true
% 3.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel_side                     none
% 3.55/0.98  --inst_solver_per_active                1400
% 3.55/0.98  --inst_solver_calls_frac                1.
% 3.55/0.98  --inst_passive_queue_type               priority_queues
% 3.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.98  --inst_passive_queues_freq              [25;2]
% 3.55/0.98  --inst_dismatching                      true
% 3.55/0.98  --inst_eager_unprocessed_to_passive     true
% 3.55/0.98  --inst_prop_sim_given                   true
% 3.55/0.98  --inst_prop_sim_new                     false
% 3.55/0.98  --inst_subs_new                         false
% 3.55/0.98  --inst_eq_res_simp                      false
% 3.55/0.98  --inst_subs_given                       false
% 3.55/0.98  --inst_orphan_elimination               true
% 3.55/0.98  --inst_learning_loop_flag               true
% 3.55/0.98  --inst_learning_start                   3000
% 3.55/0.98  --inst_learning_factor                  2
% 3.55/0.98  --inst_start_prop_sim_after_learn       3
% 3.55/0.98  --inst_sel_renew                        solver
% 3.55/0.98  --inst_lit_activity_flag                true
% 3.55/0.98  --inst_restr_to_given                   false
% 3.55/0.98  --inst_activity_threshold               500
% 3.55/0.98  --inst_out_proof                        true
% 3.55/0.98  
% 3.55/0.98  ------ Resolution Options
% 3.55/0.98  
% 3.55/0.98  --resolution_flag                       false
% 3.55/0.98  --res_lit_sel                           adaptive
% 3.55/0.98  --res_lit_sel_side                      none
% 3.55/0.98  --res_ordering                          kbo
% 3.55/0.98  --res_to_prop_solver                    active
% 3.55/0.98  --res_prop_simpl_new                    false
% 3.55/0.98  --res_prop_simpl_given                  true
% 3.55/0.98  --res_passive_queue_type                priority_queues
% 3.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.98  --res_passive_queues_freq               [15;5]
% 3.55/0.98  --res_forward_subs                      full
% 3.55/0.98  --res_backward_subs                     full
% 3.55/0.98  --res_forward_subs_resolution           true
% 3.55/0.98  --res_backward_subs_resolution          true
% 3.55/0.98  --res_orphan_elimination                true
% 3.55/0.98  --res_time_limit                        2.
% 3.55/0.98  --res_out_proof                         true
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Options
% 3.55/0.98  
% 3.55/0.98  --superposition_flag                    true
% 3.55/0.98  --sup_passive_queue_type                priority_queues
% 3.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.98  --demod_completeness_check              fast
% 3.55/0.98  --demod_use_ground                      true
% 3.55/0.98  --sup_to_prop_solver                    passive
% 3.55/0.98  --sup_prop_simpl_new                    true
% 3.55/0.98  --sup_prop_simpl_given                  true
% 3.55/0.98  --sup_fun_splitting                     false
% 3.55/0.98  --sup_smt_interval                      50000
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Simplification Setup
% 3.55/0.98  
% 3.55/0.98  --sup_indices_passive                   []
% 3.55/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_full_bw                           [BwDemod]
% 3.55/0.98  --sup_immed_triv                        [TrivRules]
% 3.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_immed_bw_main                     []
% 3.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.55/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.55/0.98  
% 3.55/0.98  ------ Combination Options
% 3.55/0.98  
% 3.55/0.98  --comb_res_mult                         3
% 3.55/0.98  --comb_sup_mult                         2
% 3.55/0.98  --comb_inst_mult                        10
% 3.55/0.98  
% 3.55/0.98  ------ Debug Options
% 3.55/0.98  
% 3.55/0.98  --dbg_backtrace                         false
% 3.55/0.98  --dbg_dump_prop_clauses                 false
% 3.55/0.98  --dbg_dump_prop_clauses_file            -
% 3.55/0.98  --dbg_out_stat                          false
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ Proving...
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS status Theorem for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98   Resolution empty clause
% 3.55/0.98  
% 3.55/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  fof(f16,conjecture,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f17,negated_conjecture,(
% 3.55/0.98    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 3.55/0.98    inference(negated_conjecture,[],[f16])).
% 3.55/0.98  
% 3.55/0.98  fof(f22,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 3.55/0.98    inference(ennf_transformation,[],[f17])).
% 3.55/0.98  
% 3.55/0.98  fof(f48,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK5 != sK7 & r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7)))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f49,plain,(
% 3.55/0.98    sK5 != sK7 & r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7))),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f48])).
% 3.55/0.98  
% 3.55/0.98  fof(f91,plain,(
% 3.55/0.98    r1_tarski(k2_tarski(sK5,sK6),k1_tarski(sK7))),
% 3.55/0.98    inference(cnf_transformation,[],[f49])).
% 3.55/0.98  
% 3.55/0.98  fof(f10,axiom,(
% 3.55/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f83,plain,(
% 3.55/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f10])).
% 3.55/0.98  
% 3.55/0.98  fof(f11,axiom,(
% 3.55/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f84,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f11])).
% 3.55/0.98  
% 3.55/0.98  fof(f12,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f85,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f12])).
% 3.55/0.98  
% 3.55/0.98  fof(f93,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f84,f85])).
% 3.55/0.98  
% 3.55/0.98  fof(f94,plain,(
% 3.55/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f83,f93])).
% 3.55/0.98  
% 3.55/0.98  fof(f119,plain,(
% 3.55/0.98    r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),
% 3.55/0.98    inference(definition_unfolding,[],[f91,f93,f94])).
% 3.55/0.98  
% 3.55/0.98  fof(f14,axiom,(
% 3.55/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f46,plain,(
% 3.55/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.55/0.98    inference(nnf_transformation,[],[f14])).
% 3.55/0.98  
% 3.55/0.98  fof(f47,plain,(
% 3.55/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.55/0.98    inference(flattening,[],[f46])).
% 3.55/0.98  
% 3.55/0.98  fof(f87,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f47])).
% 3.55/0.98  
% 3.55/0.98  fof(f117,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f87,f94,f94])).
% 3.55/0.98  
% 3.55/0.98  fof(f92,plain,(
% 3.55/0.98    sK5 != sK7),
% 3.55/0.98    inference(cnf_transformation,[],[f49])).
% 3.55/0.98  
% 3.55/0.98  fof(f7,axiom,(
% 3.55/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f20,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.55/0.98    inference(ennf_transformation,[],[f7])).
% 3.55/0.98  
% 3.55/0.98  fof(f32,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.55/0.98    inference(nnf_transformation,[],[f20])).
% 3.55/0.98  
% 3.55/0.98  fof(f33,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.55/0.98    inference(flattening,[],[f32])).
% 3.55/0.98  
% 3.55/0.98  fof(f34,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.55/0.98    inference(rectify,[],[f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f35,plain,(
% 3.55/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f36,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.55/0.98  
% 3.55/0.98  fof(f67,plain,(
% 3.55/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.55/0.98    inference(cnf_transformation,[],[f36])).
% 3.55/0.98  
% 3.55/0.98  fof(f101,plain,(
% 3.55/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.55/0.98    inference(definition_unfolding,[],[f67,f85])).
% 3.55/0.98  
% 3.55/0.98  fof(f127,plain,(
% 3.55/0.98    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 3.55/0.98    inference(equality_resolution,[],[f101])).
% 3.55/0.98  
% 3.55/0.98  fof(f128,plain,(
% 3.55/0.98    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 3.55/0.98    inference(equality_resolution,[],[f127])).
% 3.55/0.98  
% 3.55/0.98  fof(f6,axiom,(
% 3.55/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f64,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f6])).
% 3.55/0.98  
% 3.55/0.98  fof(f95,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f64,f93,f93])).
% 3.55/0.98  
% 3.55/0.98  fof(f9,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f41,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.55/0.98    inference(nnf_transformation,[],[f9])).
% 3.55/0.98  
% 3.55/0.98  fof(f42,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.55/0.98    inference(flattening,[],[f41])).
% 3.55/0.98  
% 3.55/0.98  fof(f43,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.55/0.98    inference(rectify,[],[f42])).
% 3.55/0.98  
% 3.55/0.98  fof(f44,plain,(
% 3.55/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f45,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 3.55/0.98  
% 3.55/0.98  fof(f77,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.55/0.98    inference(cnf_transformation,[],[f45])).
% 3.55/0.98  
% 3.55/0.98  fof(f113,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.55/0.98    inference(definition_unfolding,[],[f77,f93])).
% 3.55/0.98  
% 3.55/0.98  fof(f139,plain,(
% 3.55/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.55/0.98    inference(equality_resolution,[],[f113])).
% 3.55/0.98  
% 3.55/0.98  fof(f68,plain,(
% 3.55/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.55/0.98    inference(cnf_transformation,[],[f36])).
% 3.55/0.98  
% 3.55/0.98  fof(f100,plain,(
% 3.55/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.55/0.98    inference(definition_unfolding,[],[f68,f85])).
% 3.55/0.98  
% 3.55/0.98  fof(f125,plain,(
% 3.55/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.55/0.98    inference(equality_resolution,[],[f100])).
% 3.55/0.98  
% 3.55/0.98  fof(f126,plain,(
% 3.55/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.55/0.98    inference(equality_resolution,[],[f125])).
% 3.55/0.98  
% 3.55/0.98  fof(f5,axiom,(
% 3.55/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f63,plain,(
% 3.55/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f5])).
% 3.55/0.98  
% 3.55/0.98  fof(f4,axiom,(
% 3.55/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f62,plain,(
% 3.55/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f4])).
% 3.55/0.98  
% 3.55/0.98  fof(f3,axiom,(
% 3.55/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f30,plain,(
% 3.55/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.98    inference(nnf_transformation,[],[f3])).
% 3.55/0.98  
% 3.55/0.98  fof(f31,plain,(
% 3.55/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.98    inference(flattening,[],[f30])).
% 3.55/0.98  
% 3.55/0.98  fof(f61,plain,(
% 3.55/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f31])).
% 3.55/0.98  
% 3.55/0.98  fof(f1,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f23,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.55/0.98    inference(nnf_transformation,[],[f1])).
% 3.55/0.98  
% 3.55/0.98  fof(f24,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.55/0.98    inference(flattening,[],[f23])).
% 3.55/0.98  
% 3.55/0.98  fof(f25,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.55/0.98    inference(rectify,[],[f24])).
% 3.55/0.98  
% 3.55/0.98  fof(f26,plain,(
% 3.55/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f27,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.55/0.98  
% 3.55/0.98  fof(f51,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.55/0.98    inference(cnf_transformation,[],[f27])).
% 3.55/0.98  
% 3.55/0.98  fof(f121,plain,(
% 3.55/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.55/0.98    inference(equality_resolution,[],[f51])).
% 3.55/0.98  
% 3.55/0.98  cnf(c_39,negated_conjecture,
% 3.55/0.98      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1326,plain,
% 3.55/0.98      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_36,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.55/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.55/0.98      | k1_xboole_0 = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1328,plain,
% 3.55/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.55/0.98      | k1_xboole_0 = X1
% 3.55/0.98      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2805,plain,
% 3.55/0.98      ( k2_enumset1(sK7,sK7,sK7,sK7) = k2_enumset1(sK5,sK5,sK5,sK6)
% 3.55/0.98      | k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0 ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1326,c_1328]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3361,plain,
% 3.55/0.98      ( k2_enumset1(sK7,sK7,sK7,sK7) = X0
% 3.55/0.98      | k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = X0
% 3.55/0.98      | r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_2805,c_1328]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_38,negated_conjecture,
% 3.55/0.98      ( sK5 != sK7 ),
% 3.55/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_747,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1607,plain,
% 3.55/0.98      ( sK7 != X0 | sK5 != X0 | sK5 = sK7 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_747]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1714,plain,
% 3.55/0.98      ( sK7 != sK5 | sK5 = sK7 | sK5 != sK5 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1607]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_746,plain,( X0 = X0 ),theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1715,plain,
% 3.55/0.98      ( sK5 = sK5 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_746]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_20,plain,
% 3.55/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f128]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1344,plain,
% 3.55/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_14,plain,
% 3.55/0.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_32,plain,
% 3.55/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.55/0.98      inference(cnf_transformation,[],[f139]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1332,plain,
% 3.55/0.98      ( X0 = X1
% 3.55/0.98      | X0 = X2
% 3.55/0.98      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2926,plain,
% 3.55/0.98      ( X0 = X1
% 3.55/0.98      | X2 = X1
% 3.55/0.98      | r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_14,c_1332]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3369,plain,
% 3.55/0.98      ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0
% 3.55/0.98      | sK7 = X0
% 3.55/0.98      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_2805,c_2926]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4214,plain,
% 3.55/0.98      ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0 | sK7 = sK5 ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1344,c_3369]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4244,plain,
% 3.55/0.98      ( k2_enumset1(sK5,sK5,sK5,sK6) = k1_xboole_0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_3361,c_38,c_1714,c_1715,c_4214]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4260,plain,
% 3.55/0.98      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_4244,c_1344]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_19,plain,
% 3.55/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f126]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1345,plain,
% 3.55/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_13,plain,
% 3.55/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1350,plain,
% 3.55/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_12,plain,
% 3.55/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1351,plain,
% 3.55/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_9,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.55/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1353,plain,
% 3.55/0.98      ( X0 = X1
% 3.55/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.55/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2318,plain,
% 3.55/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1351,c_1353]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2480,plain,
% 3.55/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1350,c_2318]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4,plain,
% 3.55/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1358,plain,
% 3.55/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2788,plain,
% 3.55/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_2480,c_1358]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_11414,plain,
% 3.55/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1345,c_2788]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_11452,plain,
% 3.55/0.98      ( $false ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_4260,c_11414]) ).
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  ------                               Statistics
% 3.55/0.98  
% 3.55/0.98  ------ General
% 3.55/0.98  
% 3.55/0.98  abstr_ref_over_cycles:                  0
% 3.55/0.98  abstr_ref_under_cycles:                 0
% 3.55/0.98  gc_basic_clause_elim:                   0
% 3.55/0.98  forced_gc_time:                         0
% 3.55/0.98  parsing_time:                           0.008
% 3.55/0.98  unif_index_cands_time:                  0.
% 3.55/0.98  unif_index_add_time:                    0.
% 3.55/0.98  orderings_time:                         0.
% 3.55/0.98  out_proof_time:                         0.008
% 3.55/0.98  total_time:                             0.31
% 3.55/0.98  num_of_symbols:                         45
% 3.55/0.98  num_of_terms:                           13793
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing
% 3.55/0.98  
% 3.55/0.98  num_of_splits:                          0
% 3.55/0.98  num_of_split_atoms:                     0
% 3.55/0.98  num_of_reused_defs:                     0
% 3.55/0.98  num_eq_ax_congr_red:                    51
% 3.55/0.98  num_of_sem_filtered_clauses:            1
% 3.55/0.98  num_of_subtypes:                        0
% 3.55/0.98  monotx_restored_types:                  0
% 3.55/0.98  sat_num_of_epr_types:                   0
% 3.55/0.98  sat_num_of_non_cyclic_types:            0
% 3.55/0.98  sat_guarded_non_collapsed_types:        0
% 3.55/0.98  num_pure_diseq_elim:                    0
% 3.55/0.98  simp_replaced_by:                       0
% 3.55/0.98  res_preprocessed:                       169
% 3.55/0.98  prep_upred:                             0
% 3.55/0.98  prep_unflattend:                        8
% 3.55/0.98  smt_new_axioms:                         0
% 3.55/0.98  pred_elim_cands:                        3
% 3.55/0.98  pred_elim:                              0
% 3.55/0.98  pred_elim_cl:                           0
% 3.55/0.98  pred_elim_cycles:                       2
% 3.55/0.98  merged_defs:                            0
% 3.55/0.98  merged_defs_ncl:                        0
% 3.55/0.98  bin_hyper_res:                          0
% 3.55/0.98  prep_cycles:                            4
% 3.55/0.98  pred_elim_time:                         0.003
% 3.55/0.98  splitting_time:                         0.
% 3.55/0.98  sem_filter_time:                        0.
% 3.55/0.98  monotx_time:                            0.
% 3.55/0.98  subtype_inf_time:                       0.
% 3.55/0.98  
% 3.55/0.98  ------ Problem properties
% 3.55/0.98  
% 3.55/0.98  clauses:                                39
% 3.55/0.98  conjectures:                            2
% 3.55/0.98  epr:                                    5
% 3.55/0.98  horn:                                   27
% 3.55/0.98  ground:                                 2
% 3.55/0.98  unary:                                  15
% 3.55/0.98  binary:                                 6
% 3.55/0.98  lits:                                   86
% 3.55/0.98  lits_eq:                                35
% 3.55/0.98  fd_pure:                                0
% 3.55/0.98  fd_pseudo:                              0
% 3.55/0.98  fd_cond:                                0
% 3.55/0.98  fd_pseudo_cond:                         14
% 3.55/0.98  ac_symbols:                             0
% 3.55/0.98  
% 3.55/0.98  ------ Propositional Solver
% 3.55/0.98  
% 3.55/0.98  prop_solver_calls:                      27
% 3.55/0.98  prop_fast_solver_calls:                 1022
% 3.55/0.98  smt_solver_calls:                       0
% 3.55/0.98  smt_fast_solver_calls:                  0
% 3.55/0.98  prop_num_of_clauses:                    3301
% 3.55/0.98  prop_preprocess_simplified:             13401
% 3.55/0.98  prop_fo_subsumed:                       11
% 3.55/0.98  prop_solver_time:                       0.
% 3.55/0.98  smt_solver_time:                        0.
% 3.55/0.98  smt_fast_solver_time:                   0.
% 3.55/0.98  prop_fast_solver_time:                  0.
% 3.55/0.98  prop_unsat_core_time:                   0.
% 3.55/0.98  
% 3.55/0.98  ------ QBF
% 3.55/0.98  
% 3.55/0.98  qbf_q_res:                              0
% 3.55/0.98  qbf_num_tautologies:                    0
% 3.55/0.98  qbf_prep_cycles:                        0
% 3.55/0.98  
% 3.55/0.98  ------ BMC1
% 3.55/0.98  
% 3.55/0.98  bmc1_current_bound:                     -1
% 3.55/0.98  bmc1_last_solved_bound:                 -1
% 3.55/0.98  bmc1_unsat_core_size:                   -1
% 3.55/0.98  bmc1_unsat_core_parents_size:           -1
% 3.55/0.98  bmc1_merge_next_fun:                    0
% 3.55/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation
% 3.55/0.98  
% 3.55/0.98  inst_num_of_clauses:                    1116
% 3.55/0.98  inst_num_in_passive:                    395
% 3.55/0.98  inst_num_in_active:                     368
% 3.55/0.98  inst_num_in_unprocessed:                353
% 3.55/0.98  inst_num_of_loops:                      430
% 3.55/0.98  inst_num_of_learning_restarts:          0
% 3.55/0.98  inst_num_moves_active_passive:          61
% 3.55/0.98  inst_lit_activity:                      0
% 3.55/0.98  inst_lit_activity_moves:                0
% 3.55/0.98  inst_num_tautologies:                   0
% 3.55/0.98  inst_num_prop_implied:                  0
% 3.55/0.98  inst_num_existing_simplified:           0
% 3.55/0.98  inst_num_eq_res_simplified:             0
% 3.55/0.98  inst_num_child_elim:                    0
% 3.55/0.98  inst_num_of_dismatching_blockings:      1359
% 3.55/0.98  inst_num_of_non_proper_insts:           1350
% 3.55/0.98  inst_num_of_duplicates:                 0
% 3.55/0.98  inst_inst_num_from_inst_to_res:         0
% 3.55/0.98  inst_dismatching_checking_time:         0.
% 3.55/0.98  
% 3.55/0.98  ------ Resolution
% 3.55/0.98  
% 3.55/0.98  res_num_of_clauses:                     0
% 3.55/0.98  res_num_in_passive:                     0
% 3.55/0.98  res_num_in_active:                      0
% 3.55/0.98  res_num_of_loops:                       173
% 3.55/0.98  res_forward_subset_subsumed:            305
% 3.55/0.98  res_backward_subset_subsumed:           6
% 3.55/0.98  res_forward_subsumed:                   0
% 3.55/0.98  res_backward_subsumed:                  0
% 3.55/0.98  res_forward_subsumption_resolution:     0
% 3.55/0.98  res_backward_subsumption_resolution:    0
% 3.55/0.98  res_clause_to_clause_subsumption:       893
% 3.55/0.98  res_orphan_elimination:                 0
% 3.55/0.98  res_tautology_del:                      17
% 3.55/0.98  res_num_eq_res_simplified:              0
% 3.55/0.98  res_num_sel_changes:                    0
% 3.55/0.98  res_moves_from_active_to_pass:          0
% 3.55/0.98  
% 3.55/0.98  ------ Superposition
% 3.55/0.98  
% 3.55/0.98  sup_time_total:                         0.
% 3.55/0.98  sup_time_generating:                    0.
% 3.55/0.98  sup_time_sim_full:                      0.
% 3.55/0.98  sup_time_sim_immed:                     0.
% 3.55/0.98  
% 3.55/0.98  sup_num_of_clauses:                     171
% 3.55/0.98  sup_num_in_active:                      68
% 3.55/0.98  sup_num_in_passive:                     103
% 3.55/0.98  sup_num_of_loops:                       85
% 3.55/0.98  sup_fw_superposition:                   205
% 3.55/0.98  sup_bw_superposition:                   157
% 3.55/0.98  sup_immediate_simplified:               54
% 3.55/0.98  sup_given_eliminated:                   3
% 3.55/0.98  comparisons_done:                       0
% 3.55/0.98  comparisons_avoided:                    22
% 3.55/0.98  
% 3.55/0.98  ------ Simplifications
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  sim_fw_subset_subsumed:                 22
% 3.55/0.98  sim_bw_subset_subsumed:                 13
% 3.55/0.98  sim_fw_subsumed:                        23
% 3.55/0.98  sim_bw_subsumed:                        7
% 3.55/0.98  sim_fw_subsumption_res:                 0
% 3.55/0.98  sim_bw_subsumption_res:                 0
% 3.55/0.98  sim_tautology_del:                      6
% 3.55/0.98  sim_eq_tautology_del:                   18
% 3.55/0.98  sim_eq_res_simp:                        1
% 3.55/0.98  sim_fw_demodulated:                     7
% 3.55/0.98  sim_bw_demodulated:                     11
% 3.55/0.98  sim_light_normalised:                   10
% 3.55/0.98  sim_joinable_taut:                      0
% 3.55/0.98  sim_joinable_simp:                      0
% 3.55/0.98  sim_ac_normalised:                      0
% 3.55/0.98  sim_smt_subsumption:                    0
% 3.55/0.98  
%------------------------------------------------------------------------------
