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
% DateTime   : Thu Dec  3 11:41:35 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 210 expanded)
%              Number of clauses        :   40 (  41 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  418 ( 625 expanded)
%              Number of equality atoms :  220 ( 362 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f76])).

fof(f108,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f15])).

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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f99,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f100,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f99])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f40])).

fof(f74,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f74,f76])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f106,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f87])).

fof(f107,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f106])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f68,f76,f76,f76])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f67,f76,f76,f76])).

fof(f109,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f90])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37116,plain,
    ( ~ r1_tarski(X0,sK3(k2_enumset1(X1,X1,X1,X1),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_37118,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_37116])).

cnf(c_465,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_36700,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3(X3,X2))
    | X2 != X0
    | sK3(X3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_37079,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X2))
    | X2 != X0
    | sK3(k2_enumset1(X1,X1,X1,X1),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_36700])).

cnf(c_37081,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r1_tarski(sK4,sK4)
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_37079])).

cnf(c_28,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_36733,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_28,c_21])).

cnf(c_36735,plain,
    ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_36733])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5026,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5030,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6045,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_5030])).

cnf(c_6312,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5026,c_6045])).

cnf(c_6334,plain,
    ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6312])).

cnf(c_464,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5672,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_5766,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_5672])).

cnf(c_5767,plain,
    ( X0 != X1
    | k1_xboole_0 != k2_enumset1(X2,X2,X3,X1)
    | r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5766])).

cnf(c_5769,plain,
    ( sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5767])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5406,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

cnf(c_26,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5726,plain,
    ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_5406,c_26])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_73,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_50,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_52,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_51,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_46,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_23,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_45,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37118,c_37081,c_36735,c_6334,c_5769,c_5726,c_73,c_52,c_51,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.78/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/1.99  
% 11.78/1.99  ------  iProver source info
% 11.78/1.99  
% 11.78/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.78/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/1.99  git: non_committed_changes: false
% 11.78/1.99  git: last_make_outside_of_git: false
% 11.78/1.99  
% 11.78/1.99  ------ 
% 11.78/1.99  ------ Parsing...
% 11.78/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  ------ Proving...
% 11.78/1.99  ------ Problem Properties 
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  clauses                                 29
% 11.78/1.99  conjectures                             1
% 11.78/1.99  EPR                                     2
% 11.78/1.99  Horn                                    18
% 11.78/1.99  unary                                   8
% 11.78/1.99  binary                                  7
% 11.78/1.99  lits                                    68
% 11.78/1.99  lits eq                                 31
% 11.78/1.99  fd_pure                                 0
% 11.78/1.99  fd_pseudo                               0
% 11.78/1.99  fd_cond                                 2
% 11.78/1.99  fd_pseudo_cond                          11
% 11.78/1.99  AC symbols                              0
% 11.78/1.99  
% 11.78/1.99  ------ Input Options Time Limit: Unbounded
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing...
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.78/1.99  Current options:
% 11.78/1.99  ------ 
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing...
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  % SZS status Theorem for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  fof(f12,axiom,(
% 11.78/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f17,plain,(
% 11.78/1.99    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.78/1.99    inference(ennf_transformation,[],[f12])).
% 11.78/1.99  
% 11.78/1.99  fof(f18,plain,(
% 11.78/1.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.78/1.99    inference(flattening,[],[f17])).
% 11.78/1.99  
% 11.78/1.99  fof(f38,plain,(
% 11.78/1.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f39,plain,(
% 11.78/1.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f38])).
% 11.78/1.99  
% 11.78/1.99  fof(f73,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 11.78/1.99    inference(cnf_transformation,[],[f39])).
% 11.78/1.99  
% 11.78/1.99  fof(f72,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f39])).
% 11.78/1.99  
% 11.78/1.99  fof(f5,axiom,(
% 11.78/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f32,plain,(
% 11.78/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.78/1.99    inference(nnf_transformation,[],[f5])).
% 11.78/1.99  
% 11.78/1.99  fof(f33,plain,(
% 11.78/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.78/1.99    inference(rectify,[],[f32])).
% 11.78/1.99  
% 11.78/1.99  fof(f34,plain,(
% 11.78/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f35,plain,(
% 11.78/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 11.78/1.99  
% 11.78/1.99  fof(f60,plain,(
% 11.78/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.78/1.99    inference(cnf_transformation,[],[f35])).
% 11.78/1.99  
% 11.78/1.99  fof(f6,axiom,(
% 11.78/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f64,plain,(
% 11.78/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f6])).
% 11.78/1.99  
% 11.78/1.99  fof(f7,axiom,(
% 11.78/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f65,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f7])).
% 11.78/1.99  
% 11.78/1.99  fof(f8,axiom,(
% 11.78/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f66,plain,(
% 11.78/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f8])).
% 11.78/1.99  
% 11.78/1.99  fof(f75,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f65,f66])).
% 11.78/1.99  
% 11.78/1.99  fof(f76,plain,(
% 11.78/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f64,f75])).
% 11.78/1.99  
% 11.78/1.99  fof(f88,plain,(
% 11.78/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.78/1.99    inference(definition_unfolding,[],[f60,f76])).
% 11.78/1.99  
% 11.78/1.99  fof(f108,plain,(
% 11.78/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.78/1.99    inference(equality_resolution,[],[f88])).
% 11.78/1.99  
% 11.78/1.99  fof(f4,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f15,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.78/1.99    inference(ennf_transformation,[],[f4])).
% 11.78/1.99  
% 11.78/1.99  fof(f27,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(nnf_transformation,[],[f15])).
% 11.78/1.99  
% 11.78/1.99  fof(f28,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(flattening,[],[f27])).
% 11.78/1.99  
% 11.78/1.99  fof(f29,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(rectify,[],[f28])).
% 11.78/1.99  
% 11.78/1.99  fof(f30,plain,(
% 11.78/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f31,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 11.78/1.99  
% 11.78/1.99  fof(f55,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.78/1.99    inference(cnf_transformation,[],[f31])).
% 11.78/1.99  
% 11.78/1.99  fof(f81,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.78/1.99    inference(definition_unfolding,[],[f55,f66])).
% 11.78/1.99  
% 11.78/1.99  fof(f99,plain,(
% 11.78/1.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 11.78/1.99    inference(equality_resolution,[],[f81])).
% 11.78/1.99  
% 11.78/1.99  fof(f100,plain,(
% 11.78/1.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 11.78/1.99    inference(equality_resolution,[],[f99])).
% 11.78/1.99  
% 11.78/1.99  fof(f3,axiom,(
% 11.78/1.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f51,plain,(
% 11.78/1.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.78/1.99    inference(cnf_transformation,[],[f3])).
% 11.78/1.99  
% 11.78/1.99  fof(f1,axiom,(
% 11.78/1.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f20,plain,(
% 11.78/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.78/1.99    inference(nnf_transformation,[],[f1])).
% 11.78/1.99  
% 11.78/1.99  fof(f21,plain,(
% 11.78/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.78/1.99    inference(flattening,[],[f20])).
% 11.78/1.99  
% 11.78/1.99  fof(f22,plain,(
% 11.78/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.78/1.99    inference(rectify,[],[f21])).
% 11.78/1.99  
% 11.78/1.99  fof(f23,plain,(
% 11.78/1.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f24,plain,(
% 11.78/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 11.78/1.99  
% 11.78/1.99  fof(f43,plain,(
% 11.78/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.78/1.99    inference(cnf_transformation,[],[f24])).
% 11.78/1.99  
% 11.78/1.99  fof(f95,plain,(
% 11.78/1.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.78/1.99    inference(equality_resolution,[],[f43])).
% 11.78/1.99  
% 11.78/1.99  fof(f2,axiom,(
% 11.78/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f25,plain,(
% 11.78/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.78/1.99    inference(nnf_transformation,[],[f2])).
% 11.78/1.99  
% 11.78/1.99  fof(f26,plain,(
% 11.78/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.78/1.99    inference(flattening,[],[f25])).
% 11.78/1.99  
% 11.78/1.99  fof(f50,plain,(
% 11.78/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f26])).
% 11.78/1.99  
% 11.78/1.99  fof(f13,conjecture,(
% 11.78/1.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f14,negated_conjecture,(
% 11.78/1.99    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.78/1.99    inference(negated_conjecture,[],[f13])).
% 11.78/1.99  
% 11.78/1.99  fof(f19,plain,(
% 11.78/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 11.78/1.99    inference(ennf_transformation,[],[f14])).
% 11.78/1.99  
% 11.78/1.99  fof(f40,plain,(
% 11.78/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f41,plain,(
% 11.78/1.99    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f40])).
% 11.78/1.99  
% 11.78/1.99  fof(f74,plain,(
% 11.78/1.99    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 11.78/1.99    inference(cnf_transformation,[],[f41])).
% 11.78/1.99  
% 11.78/1.99  fof(f93,plain,(
% 11.78/1.99    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 11.78/1.99    inference(definition_unfolding,[],[f74,f76])).
% 11.78/1.99  
% 11.78/1.99  fof(f11,axiom,(
% 11.78/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f16,plain,(
% 11.78/1.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 11.78/1.99    inference(ennf_transformation,[],[f11])).
% 11.78/1.99  
% 11.78/1.99  fof(f71,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f16])).
% 11.78/1.99  
% 11.78/1.99  fof(f48,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.78/1.99    inference(cnf_transformation,[],[f26])).
% 11.78/1.99  
% 11.78/1.99  fof(f98,plain,(
% 11.78/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.78/1.99    inference(equality_resolution,[],[f48])).
% 11.78/1.99  
% 11.78/1.99  fof(f61,plain,(
% 11.78/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.78/1.99    inference(cnf_transformation,[],[f35])).
% 11.78/1.99  
% 11.78/1.99  fof(f87,plain,(
% 11.78/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.78/1.99    inference(definition_unfolding,[],[f61,f76])).
% 11.78/1.99  
% 11.78/1.99  fof(f106,plain,(
% 11.78/1.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.78/1.99    inference(equality_resolution,[],[f87])).
% 11.78/1.99  
% 11.78/1.99  fof(f107,plain,(
% 11.78/1.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.78/1.99    inference(equality_resolution,[],[f106])).
% 11.78/1.99  
% 11.78/1.99  fof(f9,axiom,(
% 11.78/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.78/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f36,plain,(
% 11.78/1.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.78/1.99    inference(nnf_transformation,[],[f9])).
% 11.78/1.99  
% 11.78/1.99  fof(f68,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 11.78/1.99    inference(cnf_transformation,[],[f36])).
% 11.78/1.99  
% 11.78/1.99  fof(f89,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 11.78/1.99    inference(definition_unfolding,[],[f68,f76,f76,f76])).
% 11.78/1.99  
% 11.78/1.99  fof(f67,plain,(
% 11.78/1.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f36])).
% 11.78/1.99  
% 11.78/1.99  fof(f90,plain,(
% 11.78/1.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f67,f76,f76,f76])).
% 11.78/1.99  
% 11.78/1.99  fof(f109,plain,(
% 11.78/1.99    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 11.78/1.99    inference(equality_resolution,[],[f90])).
% 11.78/1.99  
% 11.78/1.99  cnf(c_27,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,sK3(X1,X0))
% 11.78/1.99      | r1_tarski(X0,k1_setfam_1(X1))
% 11.78/1.99      | k1_xboole_0 = X1 ),
% 11.78/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_37116,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,sK3(k2_enumset1(X1,X1,X1,X1),X0))
% 11.78/1.99      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 11.78/1.99      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_27]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_37118,plain,
% 11.78/1.99      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 11.78/1.99      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 11.78/1.99      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_37116]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_465,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.78/1.99      theory(equality) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_36700,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,X1)
% 11.78/1.99      | r1_tarski(X2,sK3(X3,X2))
% 11.78/1.99      | X2 != X0
% 11.78/1.99      | sK3(X3,X2) != X1 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_465]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_37079,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,X1)
% 11.78/1.99      | r1_tarski(X2,sK3(k2_enumset1(X1,X1,X1,X1),X2))
% 11.78/1.99      | X2 != X0
% 11.78/1.99      | sK3(k2_enumset1(X1,X1,X1,X1),X2) != X1 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_36700]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_37081,plain,
% 11.78/1.99      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 11.78/1.99      | ~ r1_tarski(sK4,sK4)
% 11.78/1.99      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
% 11.78/1.99      | sK4 != sK4 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_37079]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_28,plain,
% 11.78/1.99      ( r1_tarski(X0,k1_setfam_1(X1))
% 11.78/1.99      | r2_hidden(sK3(X1,X0),X1)
% 11.78/1.99      | k1_xboole_0 = X1 ),
% 11.78/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_21,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.78/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_36733,plain,
% 11.78/1.99      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 11.78/1.99      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 11.78/1.99      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 11.78/1.99      inference(resolution,[status(thm)],[c_28,c_21]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_36735,plain,
% 11.78/1.99      ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 11.78/1.99      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 11.78/1.99      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_36733]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_14,plain,
% 11.78/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5026,plain,
% 11.78/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9,plain,
% 11.78/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_4,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5030,plain,
% 11.78/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.78/1.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6045,plain,
% 11.78/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.78/1.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9,c_5030]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6312,plain,
% 11.78/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5026,c_6045]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6334,plain,
% 11.78/1.99      ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_6312]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_464,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.78/1.99      theory(equality) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5672,plain,
% 11.78/1.99      ( r2_hidden(X0,X1)
% 11.78/1.99      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 11.78/1.99      | X0 != X2
% 11.78/1.99      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_464]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5766,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 11.78/1.99      | r2_hidden(X3,k1_xboole_0)
% 11.78/1.99      | X3 != X0
% 11.78/1.99      | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_5672]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5767,plain,
% 11.78/1.99      ( X0 != X1
% 11.78/1.99      | k1_xboole_0 != k2_enumset1(X2,X2,X3,X1)
% 11.78/1.99      | r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) != iProver_top
% 11.78/1.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_5766]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5769,plain,
% 11.78/1.99      ( sK4 != sK4
% 11.78/1.99      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4)
% 11.78/1.99      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 11.78/1.99      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_5767]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.78/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29,negated_conjecture,
% 11.78/1.99      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 11.78/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5406,plain,
% 11.78/1.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 11.78/1.99      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 11.78/1.99      inference(resolution,[status(thm)],[c_6,c_29]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26,plain,
% 11.78/1.99      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5726,plain,
% 11.78/1.99      ( ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 11.78/1.99      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.78/1.99      inference(resolution,[status(thm)],[c_5406,c_26]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_8,plain,
% 11.78/1.99      ( r1_tarski(X0,X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_73,plain,
% 11.78/1.99      ( r1_tarski(sK4,sK4) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_20,plain,
% 11.78/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_50,plain,
% 11.78/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_52,plain,
% 11.78/1.99      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_50]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_51,plain,
% 11.78/1.99      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_22,plain,
% 11.78/1.99      ( X0 = X1
% 11.78/1.99      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 11.78/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_46,plain,
% 11.78/1.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 11.78/1.99      | sK4 = sK4 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_23,plain,
% 11.78/1.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_45,plain,
% 11.78/1.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(contradiction,plain,
% 11.78/1.99      ( $false ),
% 11.78/1.99      inference(minisat,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_37118,c_37081,c_36735,c_6334,c_5769,c_5726,c_73,c_52,
% 11.78/1.99                 c_51,c_46,c_45]) ).
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  ------                               Statistics
% 11.78/1.99  
% 11.78/1.99  ------ Selected
% 11.78/1.99  
% 11.78/1.99  total_time:                             1.383
% 11.78/1.99  
%------------------------------------------------------------------------------
