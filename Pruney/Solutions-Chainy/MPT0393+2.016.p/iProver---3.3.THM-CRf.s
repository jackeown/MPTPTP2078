%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:36 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 468 expanded)
%              Number of clauses        :   58 (  95 expanded)
%              Number of leaves         :   20 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  417 (2087 expanded)
%              Number of equality atoms :  166 ( 907 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f36])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),X0) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK6(X0,X5))
                    & r2_hidden(sK6(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK7)) != sK7 ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k1_setfam_1(k1_tarski(sK7)) != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f44])).

fof(f79,plain,(
    k1_setfam_1(k1_tarski(sK7)) != sK7 ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f80])).

fof(f95,plain,(
    k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) != sK7 ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f100,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f76])).

fof(f110,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f109])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK3(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9750,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(X2),X1)
    | ~ r2_hidden(sK3(X2),sK3(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20134,plain,
    ( ~ r2_hidden(sK3(X0),X0)
    | ~ r2_hidden(sK3(X1),X0)
    | ~ r2_hidden(sK3(X1),sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_9750])).

cnf(c_20136,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20134])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(X1,X2),X2)
    | r2_hidden(sK4(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) != sK7 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6482,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),X0)
    | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_25,c_30])).

cnf(c_24,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | ~ r2_hidden(sK4(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6780,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),X0)
    | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_6482,c_24])).

cnf(c_6817,plain,
    ( r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
    | ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(factoring,[status(thm)],[c_6482])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1355,plain,
    ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6820,plain,
    ( r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6817,c_1355])).

cnf(c_7020,plain,
    ( r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
    | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_6820,c_24])).

cnf(c_7300,plain,
    ( r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6780,c_30,c_7020])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7317,plain,
    ( sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7) = sK7
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_7300,c_9])).

cnf(c_481,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_480,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2615,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_481,c_480])).

cnf(c_8495,plain,
    ( sK7 = sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_7317,c_2615])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_22,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4503,plain,
    ( r2_hidden(X0,k1_setfam_1(k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_483,c_22])).

cnf(c_8521,plain,
    ( ~ r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k1_xboole_0)
    | r2_hidden(sK7,k1_setfam_1(k1_xboole_0))
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_8495,c_4503])).

cnf(c_8500,plain,
    ( r2_hidden(X0,sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7))
    | ~ r2_hidden(X1,sK7)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_7317,c_483])).

cnf(c_9451,plain,
    ( r2_hidden(X0,sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7))
    | ~ r2_hidden(X0,sK7)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_8500,c_480])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12055,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
    | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_9451,c_23])).

cnf(c_12066,plain,
    ( k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8521,c_30,c_1355,c_6817,c_12055])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3(X1),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9909,plain,
    ( r2_hidden(sK3(X0),X0)
    | ~ r2_hidden(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_9929,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9909])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1997,plain,
    ( ~ r2_hidden(sK3(X0),X0)
    | r2_hidden(sK3(X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9749,plain,
    ( ~ r2_hidden(sK3(X0),X0)
    | r2_hidden(sK3(X0),sK3(X1))
    | ~ r1_tarski(X0,sK3(X1)) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_9752,plain,
    ( r2_hidden(sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9749])).

cnf(c_1199,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1871,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK7,X1)
    | X1 != k2_enumset1(X0,X0,X0,X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_2736,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK7,k1_xboole_0)
    | sK7 != X0
    | k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_8549,plain,
    ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
    | r2_hidden(sK7,k1_xboole_0)
    | sK7 != sK7
    | k1_xboole_0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_964,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_946,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK3(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1532,plain,
    ( r2_hidden(sK3(X0),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_946])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_939,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1318,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_939])).

cnf(c_6378,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1318])).

cnf(c_6452,plain,
    ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_6378])).

cnf(c_6454,plain,
    ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6452])).

cnf(c_6459,plain,
    ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6454])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3618,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1300,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3617,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20136,c_12066,c_9929,c_9752,c_8549,c_6459,c_3618,c_3617,c_1355])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.77/1.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/1.53  
% 6.77/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.77/1.53  
% 6.77/1.53  ------  iProver source info
% 6.77/1.53  
% 6.77/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.77/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.77/1.53  git: non_committed_changes: false
% 6.77/1.53  git: last_make_outside_of_git: false
% 6.77/1.53  
% 6.77/1.53  ------ 
% 6.77/1.53  ------ Parsing...
% 6.77/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.77/1.53  
% 6.77/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.77/1.53  
% 6.77/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.77/1.53  
% 6.77/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.77/1.53  ------ Proving...
% 6.77/1.53  ------ Problem Properties 
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  clauses                                 29
% 6.77/1.53  conjectures                             1
% 6.77/1.53  EPR                                     3
% 6.77/1.53  Horn                                    18
% 6.77/1.53  unary                                   7
% 6.77/1.53  binary                                  6
% 6.77/1.53  lits                                    73
% 6.77/1.53  lits eq                                 27
% 6.77/1.53  fd_pure                                 0
% 6.77/1.53  fd_pseudo                               0
% 6.77/1.53  fd_cond                                 3
% 6.77/1.53  fd_pseudo_cond                          10
% 6.77/1.53  AC symbols                              0
% 6.77/1.53  
% 6.77/1.53  ------ Input Options Time Limit: Unbounded
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  ------ 
% 6.77/1.53  Current options:
% 6.77/1.53  ------ 
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  ------ Proving...
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  % SZS status Theorem for theBenchmark.p
% 6.77/1.53  
% 6.77/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 6.77/1.53  
% 6.77/1.53  fof(f9,axiom,(
% 6.77/1.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f15,plain,(
% 6.77/1.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 6.77/1.53    inference(ennf_transformation,[],[f9])).
% 6.77/1.53  
% 6.77/1.53  fof(f36,plain,(
% 6.77/1.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)))),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f37,plain,(
% 6.77/1.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)) | ~r2_hidden(X0,X1))),
% 6.77/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f36])).
% 6.77/1.53  
% 6.77/1.53  fof(f69,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f37])).
% 6.77/1.53  
% 6.77/1.53  fof(f10,axiom,(
% 6.77/1.53    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f16,plain,(
% 6.77/1.53    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 6.77/1.53    inference(ennf_transformation,[],[f10])).
% 6.77/1.53  
% 6.77/1.53  fof(f38,plain,(
% 6.77/1.53    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 6.77/1.53    inference(nnf_transformation,[],[f16])).
% 6.77/1.53  
% 6.77/1.53  fof(f39,plain,(
% 6.77/1.53    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 6.77/1.53    inference(rectify,[],[f38])).
% 6.77/1.53  
% 6.77/1.53  fof(f42,plain,(
% 6.77/1.53    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f41,plain,(
% 6.77/1.53    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))) )),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f40,plain,(
% 6.77/1.53    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f43,plain,(
% 6.77/1.53    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 6.77/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 6.77/1.53  
% 6.77/1.53  fof(f73,plain,(
% 6.77/1.53    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK4(X0,X1),X1) | k1_xboole_0 = X0) )),
% 6.77/1.53    inference(cnf_transformation,[],[f43])).
% 6.77/1.53  
% 6.77/1.53  fof(f12,conjecture,(
% 6.77/1.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f13,negated_conjecture,(
% 6.77/1.53    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 6.77/1.53    inference(negated_conjecture,[],[f12])).
% 6.77/1.53  
% 6.77/1.53  fof(f18,plain,(
% 6.77/1.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 6.77/1.53    inference(ennf_transformation,[],[f13])).
% 6.77/1.53  
% 6.77/1.53  fof(f44,plain,(
% 6.77/1.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK7)) != sK7),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f45,plain,(
% 6.77/1.53    k1_setfam_1(k1_tarski(sK7)) != sK7),
% 6.77/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f44])).
% 6.77/1.53  
% 6.77/1.53  fof(f79,plain,(
% 6.77/1.53    k1_setfam_1(k1_tarski(sK7)) != sK7),
% 6.77/1.53    inference(cnf_transformation,[],[f45])).
% 6.77/1.53  
% 6.77/1.53  fof(f5,axiom,(
% 6.77/1.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f62,plain,(
% 6.77/1.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f5])).
% 6.77/1.53  
% 6.77/1.53  fof(f6,axiom,(
% 6.77/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f63,plain,(
% 6.77/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f6])).
% 6.77/1.53  
% 6.77/1.53  fof(f7,axiom,(
% 6.77/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f64,plain,(
% 6.77/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f7])).
% 6.77/1.53  
% 6.77/1.53  fof(f80,plain,(
% 6.77/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.77/1.53    inference(definition_unfolding,[],[f63,f64])).
% 6.77/1.53  
% 6.77/1.53  fof(f81,plain,(
% 6.77/1.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 6.77/1.53    inference(definition_unfolding,[],[f62,f80])).
% 6.77/1.53  
% 6.77/1.53  fof(f95,plain,(
% 6.77/1.53    k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) != sK7),
% 6.77/1.53    inference(definition_unfolding,[],[f79,f81])).
% 6.77/1.53  
% 6.77/1.53  fof(f74,plain,(
% 6.77/1.53    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK5(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1) | k1_xboole_0 = X0) )),
% 6.77/1.53    inference(cnf_transformation,[],[f43])).
% 6.77/1.53  
% 6.77/1.53  fof(f3,axiom,(
% 6.77/1.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f25,plain,(
% 6.77/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.77/1.53    inference(nnf_transformation,[],[f3])).
% 6.77/1.53  
% 6.77/1.53  fof(f26,plain,(
% 6.77/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.77/1.53    inference(rectify,[],[f25])).
% 6.77/1.53  
% 6.77/1.53  fof(f27,plain,(
% 6.77/1.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f28,plain,(
% 6.77/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.77/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 6.77/1.53  
% 6.77/1.53  fof(f53,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.77/1.53    inference(cnf_transformation,[],[f28])).
% 6.77/1.53  
% 6.77/1.53  fof(f84,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 6.77/1.53    inference(definition_unfolding,[],[f53,f81])).
% 6.77/1.53  
% 6.77/1.53  fof(f98,plain,(
% 6.77/1.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 6.77/1.53    inference(equality_resolution,[],[f84])).
% 6.77/1.53  
% 6.77/1.53  fof(f99,plain,(
% 6.77/1.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 6.77/1.53    inference(equality_resolution,[],[f98])).
% 6.77/1.53  
% 6.77/1.53  fof(f52,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.77/1.53    inference(cnf_transformation,[],[f28])).
% 6.77/1.53  
% 6.77/1.53  fof(f85,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 6.77/1.53    inference(definition_unfolding,[],[f52,f81])).
% 6.77/1.53  
% 6.77/1.53  fof(f100,plain,(
% 6.77/1.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 6.77/1.53    inference(equality_resolution,[],[f85])).
% 6.77/1.53  
% 6.77/1.53  fof(f76,plain,(
% 6.77/1.53    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1 | k1_xboole_0 != X0) )),
% 6.77/1.53    inference(cnf_transformation,[],[f43])).
% 6.77/1.53  
% 6.77/1.53  fof(f109,plain,(
% 6.77/1.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 6.77/1.53    inference(equality_resolution,[],[f76])).
% 6.77/1.53  
% 6.77/1.53  fof(f110,plain,(
% 6.77/1.53    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 6.77/1.53    inference(equality_resolution,[],[f109])).
% 6.77/1.53  
% 6.77/1.53  fof(f75,plain,(
% 6.77/1.53    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(sK4(X0,X1),X1) | k1_xboole_0 = X0) )),
% 6.77/1.53    inference(cnf_transformation,[],[f43])).
% 6.77/1.53  
% 6.77/1.53  fof(f68,plain,(
% 6.77/1.53    ( ! [X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f37])).
% 6.77/1.53  
% 6.77/1.53  fof(f1,axiom,(
% 6.77/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f14,plain,(
% 6.77/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.77/1.53    inference(ennf_transformation,[],[f1])).
% 6.77/1.53  
% 6.77/1.53  fof(f19,plain,(
% 6.77/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.77/1.53    inference(nnf_transformation,[],[f14])).
% 6.77/1.53  
% 6.77/1.53  fof(f20,plain,(
% 6.77/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.77/1.53    inference(rectify,[],[f19])).
% 6.77/1.53  
% 6.77/1.53  fof(f21,plain,(
% 6.77/1.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.77/1.53    introduced(choice_axiom,[])).
% 6.77/1.53  
% 6.77/1.53  fof(f22,plain,(
% 6.77/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.77/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 6.77/1.53  
% 6.77/1.53  fof(f46,plain,(
% 6.77/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f22])).
% 6.77/1.53  
% 6.77/1.53  fof(f47,plain,(
% 6.77/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f22])).
% 6.77/1.53  
% 6.77/1.53  fof(f11,axiom,(
% 6.77/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f17,plain,(
% 6.77/1.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 6.77/1.53    inference(ennf_transformation,[],[f11])).
% 6.77/1.53  
% 6.77/1.53  fof(f78,plain,(
% 6.77/1.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f17])).
% 6.77/1.53  
% 6.77/1.53  fof(f2,axiom,(
% 6.77/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.77/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.77/1.53  
% 6.77/1.53  fof(f23,plain,(
% 6.77/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.77/1.53    inference(nnf_transformation,[],[f2])).
% 6.77/1.53  
% 6.77/1.53  fof(f24,plain,(
% 6.77/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.77/1.53    inference(flattening,[],[f23])).
% 6.77/1.53  
% 6.77/1.53  fof(f49,plain,(
% 6.77/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.77/1.53    inference(cnf_transformation,[],[f24])).
% 6.77/1.53  
% 6.77/1.53  fof(f97,plain,(
% 6.77/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.77/1.53    inference(equality_resolution,[],[f49])).
% 6.77/1.53  
% 6.77/1.53  fof(f51,plain,(
% 6.77/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.77/1.53    inference(cnf_transformation,[],[f24])).
% 6.77/1.53  
% 6.77/1.53  cnf(c_19,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1)
% 6.77/1.53      | ~ r2_hidden(X2,X1)
% 6.77/1.53      | ~ r2_hidden(X2,sK3(X1)) ),
% 6.77/1.53      inference(cnf_transformation,[],[f69]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9750,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1)
% 6.77/1.53      | ~ r2_hidden(sK3(X2),X1)
% 6.77/1.53      | ~ r2_hidden(sK3(X2),sK3(X1)) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_19]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_20134,plain,
% 6.77/1.53      ( ~ r2_hidden(sK3(X0),X0)
% 6.77/1.53      | ~ r2_hidden(sK3(X1),X0)
% 6.77/1.53      | ~ r2_hidden(sK3(X1),sK3(X0)) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_9750]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_20136,plain,
% 6.77/1.53      ( ~ r2_hidden(sK3(k1_xboole_0),sK3(k1_xboole_0))
% 6.77/1.53      | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_20134]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_25,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1)
% 6.77/1.53      | r2_hidden(sK4(X1,X2),X2)
% 6.77/1.53      | r2_hidden(sK4(X1,X2),X0)
% 6.77/1.53      | k1_setfam_1(X1) = X2
% 6.77/1.53      | k1_xboole_0 = X1 ),
% 6.77/1.53      inference(cnf_transformation,[],[f73]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_30,negated_conjecture,
% 6.77/1.53      ( k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) != sK7 ),
% 6.77/1.53      inference(cnf_transformation,[],[f95]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6482,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),X0)
% 6.77/1.53      | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_25,c_30]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_24,plain,
% 6.77/1.53      ( r2_hidden(sK5(X0,X1),X0)
% 6.77/1.53      | ~ r2_hidden(sK4(X0,X1),X1)
% 6.77/1.53      | k1_setfam_1(X0) = X1
% 6.77/1.53      | k1_xboole_0 = X0 ),
% 6.77/1.53      inference(cnf_transformation,[],[f74]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6780,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),X0)
% 6.77/1.53      | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_6482,c_24]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6817,plain,
% 6.77/1.53      ( r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
% 6.77/1.53      | ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(factoring,[status(thm)],[c_6482]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_8,plain,
% 6.77/1.53      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 6.77/1.53      inference(cnf_transformation,[],[f99]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1355,plain,
% 6.77/1.53      ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6820,plain,
% 6.77/1.53      ( r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(global_propositional_subsumption,
% 6.77/1.53                [status(thm)],
% 6.77/1.53                [c_6817,c_1355]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_7020,plain,
% 6.77/1.53      ( r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_6820,c_24]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_7300,plain,
% 6.77/1.53      ( r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(global_propositional_subsumption,
% 6.77/1.53                [status(thm)],
% 6.77/1.53                [c_6780,c_30,c_7020]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 6.77/1.53      inference(cnf_transformation,[],[f100]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_7317,plain,
% 6.77/1.53      ( sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7) = sK7
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_7300,c_9]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_481,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_480,plain,( X0 = X0 ),theory(equality) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_2615,plain,
% 6.77/1.53      ( X0 != X1 | X1 = X0 ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_481,c_480]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_8495,plain,
% 6.77/1.53      ( sK7 = sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7)
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_7317,c_2615]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_483,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.77/1.53      theory(equality) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_22,plain,
% 6.77/1.53      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 6.77/1.53      inference(cnf_transformation,[],[f110]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_4503,plain,
% 6.77/1.53      ( r2_hidden(X0,k1_setfam_1(k1_xboole_0))
% 6.77/1.53      | ~ r2_hidden(X1,k1_xboole_0)
% 6.77/1.53      | X0 != X1 ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_483,c_22]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_8521,plain,
% 6.77/1.53      ( ~ r2_hidden(sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7),k1_xboole_0)
% 6.77/1.53      | r2_hidden(sK7,k1_setfam_1(k1_xboole_0))
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_8495,c_4503]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_8500,plain,
% 6.77/1.53      ( r2_hidden(X0,sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7))
% 6.77/1.53      | ~ r2_hidden(X1,sK7)
% 6.77/1.53      | X0 != X1
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_7317,c_483]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9451,plain,
% 6.77/1.53      ( r2_hidden(X0,sK5(k2_enumset1(sK7,sK7,sK7,sK7),sK7))
% 6.77/1.53      | ~ r2_hidden(X0,sK7)
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_8500,c_480]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_23,plain,
% 6.77/1.53      ( ~ r2_hidden(sK4(X0,X1),X1)
% 6.77/1.53      | ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
% 6.77/1.53      | k1_setfam_1(X0) = X1
% 6.77/1.53      | k1_xboole_0 = X0 ),
% 6.77/1.53      inference(cnf_transformation,[],[f75]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_12055,plain,
% 6.77/1.53      ( ~ r2_hidden(sK4(k2_enumset1(sK7,sK7,sK7,sK7),sK7),sK7)
% 6.77/1.53      | k1_setfam_1(k2_enumset1(sK7,sK7,sK7,sK7)) = sK7
% 6.77/1.53      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(resolution,[status(thm)],[c_9451,c_23]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_12066,plain,
% 6.77/1.53      ( k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(global_propositional_subsumption,
% 6.77/1.53                [status(thm)],
% 6.77/1.53                [c_8521,c_30,c_1355,c_6817,c_12055]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_20,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3(X1),X1) ),
% 6.77/1.53      inference(cnf_transformation,[],[f68]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9909,plain,
% 6.77/1.53      ( r2_hidden(sK3(X0),X0) | ~ r2_hidden(sK7,X0) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_20]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9929,plain,
% 6.77/1.53      ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
% 6.77/1.53      | ~ r2_hidden(sK7,k1_xboole_0) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_9909]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_2,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.77/1.53      inference(cnf_transformation,[],[f46]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1997,plain,
% 6.77/1.53      ( ~ r2_hidden(sK3(X0),X0)
% 6.77/1.53      | r2_hidden(sK3(X0),X1)
% 6.77/1.53      | ~ r1_tarski(X0,X1) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9749,plain,
% 6.77/1.53      ( ~ r2_hidden(sK3(X0),X0)
% 6.77/1.53      | r2_hidden(sK3(X0),sK3(X1))
% 6.77/1.53      | ~ r1_tarski(X0,sK3(X1)) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_1997]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_9752,plain,
% 6.77/1.53      ( r2_hidden(sK3(k1_xboole_0),sK3(k1_xboole_0))
% 6.77/1.53      | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
% 6.77/1.53      | ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_9749]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1199,plain,
% 6.77/1.53      ( r2_hidden(X0,X1)
% 6.77/1.53      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 6.77/1.53      | X0 != X2
% 6.77/1.53      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_483]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1871,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 6.77/1.53      | r2_hidden(sK7,X1)
% 6.77/1.53      | X1 != k2_enumset1(X0,X0,X0,X0)
% 6.77/1.53      | sK7 != X0 ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_1199]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_2736,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 6.77/1.53      | r2_hidden(sK7,k1_xboole_0)
% 6.77/1.53      | sK7 != X0
% 6.77/1.53      | k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_1871]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_8549,plain,
% 6.77/1.53      ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
% 6.77/1.53      | r2_hidden(sK7,k1_xboole_0)
% 6.77/1.53      | sK7 != sK7
% 6.77/1.53      | k1_xboole_0 != k2_enumset1(sK7,sK7,sK7,sK7) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_2736]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1,plain,
% 6.77/1.53      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.77/1.53      inference(cnf_transformation,[],[f47]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_964,plain,
% 6.77/1.53      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 6.77/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 6.77/1.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_946,plain,
% 6.77/1.53      ( r2_hidden(X0,X1) != iProver_top
% 6.77/1.53      | r2_hidden(sK3(X1),X1) = iProver_top ),
% 6.77/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1532,plain,
% 6.77/1.53      ( r2_hidden(sK3(X0),X0) = iProver_top
% 6.77/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 6.77/1.53      inference(superposition,[status(thm)],[c_964,c_946]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_29,plain,
% 6.77/1.53      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 6.77/1.53      inference(cnf_transformation,[],[f78]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_939,plain,
% 6.77/1.53      ( r2_hidden(X0,X1) != iProver_top
% 6.77/1.53      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 6.77/1.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1318,plain,
% 6.77/1.53      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.77/1.53      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 6.77/1.53      inference(superposition,[status(thm)],[c_22,c_939]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6378,plain,
% 6.77/1.53      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 6.77/1.53      | r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top ),
% 6.77/1.53      inference(superposition,[status(thm)],[c_1532,c_1318]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6452,plain,
% 6.77/1.53      ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top
% 6.77/1.53      | iProver_top != iProver_top ),
% 6.77/1.53      inference(equality_factoring,[status(thm)],[c_6378]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6454,plain,
% 6.77/1.53      ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) = iProver_top ),
% 6.77/1.53      inference(equality_resolution_simp,[status(thm)],[c_6452]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_6459,plain,
% 6.77/1.53      ( r1_tarski(k1_xboole_0,sK3(k1_xboole_0)) ),
% 6.77/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_6454]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_5,plain,
% 6.77/1.53      ( r1_tarski(X0,X0) ),
% 6.77/1.53      inference(cnf_transformation,[],[f97]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_3618,plain,
% 6.77/1.53      ( r1_tarski(sK7,sK7) ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_3,plain,
% 6.77/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.77/1.53      inference(cnf_transformation,[],[f51]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_1300,plain,
% 6.77/1.53      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(c_3617,plain,
% 6.77/1.53      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 6.77/1.53      inference(instantiation,[status(thm)],[c_1300]) ).
% 6.77/1.53  
% 6.77/1.53  cnf(contradiction,plain,
% 6.77/1.53      ( $false ),
% 6.77/1.53      inference(minisat,
% 6.77/1.53                [status(thm)],
% 6.77/1.53                [c_20136,c_12066,c_9929,c_9752,c_8549,c_6459,c_3618,
% 6.77/1.53                 c_3617,c_1355]) ).
% 6.77/1.53  
% 6.77/1.53  
% 6.77/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 6.77/1.53  
% 6.77/1.53  ------                               Statistics
% 6.77/1.53  
% 6.77/1.53  ------ Selected
% 6.77/1.53  
% 6.77/1.53  total_time:                             0.652
% 6.77/1.53  
%------------------------------------------------------------------------------
